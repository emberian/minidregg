/- The kernel activity: a Core4 activity persisted between turns, its awaits,
the resume contract, and its fees on the Book.

An activity of an object is a cell of the deployment's activity role
(`Kernel.ObjectiveActivityCell`) at its protected coordinate
(`recordCell domain object activity`), holding its `Record`: the exact machine
checkpoint (the bytes of `ObjectiveBendCheckpoint.encodeState`, never a
summary), the checkpoint's digest, the pinned package identity, the generation,
the read versions the continuation depends on, the escrow terms, and its phase.
While awaiting, the phase names one `Await`: its id `H(record cell, generation,
checkpoint digest)`, its source (an answer slot with one decider, or a height),
and a mandatory deadline height. The object is a native resource (`object`, a
cell id the authority layer issues capabilities on); its declared state lives in
its own protected state cell (`stateCell domain object`).

Six kernel turns; each is ONE `DataIntent` built by `intentOf` with the sealing of
the receiver that admitted it (`ObjectiveActivityReceiver`: the signed marker,
the authority guards, the replay event), so its writes commit all together or
not at all (`DurableDataIntent.execute_no_partial_data_commit`):

* `publish`: the package (a checked `ObjectiveBendSourceArtifact`) into its
  content-addressed package cell.
* `birth`: instantiate the pinned definition with typed input, run to the
  first yield, commit the record, the declared-state write, the answer slot it
  awaits and the Book postings, all at once.
* `resolve`: the slot's one decider decides it (typed against the awaiting
  activity's own response type) at or before the deadline; spends the slot claim.
* `deliver`: anyone resumes the activity with the typed outcome of its await.
  The await id is spent as a nullifier bound to the checkpoint digest, AND the
  record cell is written against its current root: consume-once is a
  compare-and-swap at admission's decide point. Recorded reads are revalidated
  (stale: the activity receives `conflict` carrying the outcome it lost, never
  the bare outcome). Past the deadline an open slot expires in the same turn and
  the activity receives `timedOut`. The checkpoint is decoded from the record
  cell (no state is ever accepted from a request), resumed with the typed
  response, run to its next yield or end, and the new checkpoint, the Plan's
  write, the next await and the Book postings commit together.
* `topUp`: anyone funds an activity's purse on the Book.
* `writeState`: a holder of the object writes its declared state directly
  (what makes a recorded read stale).

Fees are Book postings in the deployment's credit asset. An activity's purse is
a Book account of its own, `heldAccount cell` (the record cell's id), registered
by the birth. Every turn that runs Core4 pays the public price of its DECLARED
envelope (`Tariff.price`) to the collector. A yield reserves, in the purse, the
fee pair of the await (`resumeFee`, `timeoutFee`): exactly one of the pair pays
the turn that ends the await, the other stays in the purse, and the purse is
returned to the payer's account when the activity ends. A yield the purse cannot
reserve is refused (the activity stays parked at its previous yield until a
`topUp`). Every posting is one `CanonicalResourceKernel.Batch`, admitted on the
loaded Book (`AcceptedBatch`), so every turn conserves every asset
(`Birth.conserves`, `Delivery.conserves`). No amount depends on how much
computation ran (`refund_measurement_free`). -/
import Kernel.AnswerSlot
import Compiler.ObjectiveBendSourceArtifact
import Compiler.CanonicalCellRegistry
import Theory.ObjectiveBendDemandCollect

namespace Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendOpenRecursion (Term)
open Minidregg.Theory.ObjectiveBendTypes (Ty Bounds LambdaAnnotation Quantity Reuse)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine (State Limits initial runBounded resume)
open Minidregg.Theory.ObjectiveBendDemandData (Data Budget)
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook AcceptedBatch)
set_option autoImplicit false

abbrev Role := ObjectiveActivityCell.Role

/-! ## The record -/

inductive Source where
  /-- An answer slot (by name) and its one decider. -/
  | reply (slot : Digest) (decider : SubjectId)
  /-- A height at or after which the await is due. -/
  | height (due : Nat)
  deriving DecidableEq, Repr

structure Await where
  id : Digest
  source : Source
  deadline : Nat
  yieldedAt : Nat
  deriving DecidableEq, Repr

/-- The escrow terms of an activity: who pays, the Book account its purse is
returned to, and the fee pair each await reserves in the purse. -/
structure Escrow where
  payer : SubjectId
  account : AccountId
  resumeTicks : Nat
  timeoutTicks : Nat
  resumeFee : Nat
  timeoutFee : Nat
  deriving DecidableEq, Repr

inductive Phase where
  | awaiting (await : Await)
  | done (result : Bytes)
  | faulted (reason : String)
  deriving DecidableEq, Repr

structure Record where
  object : CellId
  activity : Digest
  /-- The package identity (`ObjectiveBendSourceArtifact.identity`) that made
  every checkpoint of this activity. -/
  pin : Digest
  /-- The instantiating input, as data bytes; the program is re-instantiated
  and re-checked at every turn, never trusted from a previous one. -/
  input : Bytes
  generation : Nat
  checkpoint : Bytes
  checkpointDigest : Digest
  reads : List ReadGuard
  escrow : Escrow
  phase : Phase
  deriving DecidableEq, Repr

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap (StreamCodec.sum (StreamCodec.product digestStream subjectStream) StreamCodec.nat)
    (fun source => match source with
      | .reply slot decider => .inl (slot, decider)
      | .height due => .inr due)
    (fun wire => match wire with
      | .inl (slot, decider) => .reply slot decider
      | .inr due => .height due)
    (by intro source; cases source <;> rfl)

def awaitStream : StreamCodec Await :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product sourceStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun a => (a.id, a.source, a.deadline, a.yieldedAt))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩)
    (by intro a; cases a; rfl)

def escrowStream : StreamCodec Escrow :=
  StreamCodec.xmap
    (StreamCodec.product subjectStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
    (fun e => (e.payer, e.account, e.resumeTicks, e.timeoutTicks, e.resumeFee, e.timeoutFee))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩)
    (by intro e; cases e; rfl)

def phaseStream : StreamCodec Phase :=
  StreamCodec.xmap (StreamCodec.sum awaitStream (StreamCodec.sum bytesStream stringStream))
    (fun phase => match phase with
      | .awaiting a => .inl a
      | .done result => .inr (.inl result)
      | .faulted reason => .inr (.inr reason))
    (fun wire => match wire with
      | .inl a => .awaiting a
      | .inr (.inl result) => .done result
      | .inr (.inr reason) => .faulted reason)
    (by intro phase; cases phase <;> rfl)

def recordStream : StreamCodec Record :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
      (StreamCodec.product digestStream (StreamCodec.product (StreamCodec.list readGuardStream)
      (StreamCodec.product escrowStream phaseStream)))))))))
    (fun r => (r.object, r.activity, r.pin, r.input, r.generation, r.checkpoint, r.checkpointDigest,
      r.reads, r.escrow, r.phase))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1,
      w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

/-- v2: the escrow names the payer's Book account (fees moved onto the Book). -/
def recordFrame : Bytes := "DREGG/OBJECTIVE/ACTIVITY-RECORD/v2".toUTF8.toList
def recordCodec := framed recordFrame recordStream
def encodeRecord (record : Record) : Bytes := recordCodec.encode record
def decodeRecord (bytes : Bytes) : Option Record := recordCodec.decode bytes

theorem record_roundTrip (record : Record) : decodeRecord (encodeRecord record) = some record :=
  framed_roundTrip _ _ record

/-! ## Cells: protected coordinates

Every activity cell is a registry cell of role `objectiveActivity` at
`ObjectiveActivityCell.coordinate domain role key`; its body is the kernel's own
framed bytes. The registry's law pins each cell to its coordinate, no birth may
install the role, and only `ObjectiveActivityReceiver` writes it. -/

def recordKey (object : CellId) (activity : Digest) : Bytes :=
  digestStream.encode object ++ digestStream.encode activity

def recordCell (domain : Digest) (object : CellId) (activity : Digest) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .record (recordKey object activity)⟩

def stateKey (object : CellId) : Bytes := digestStream.encode object

/-- The object's declared state: one cell per object, beside the object's own
native resource cell. -/
def stateCell (domain : Digest) (object : CellId) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .state (stateKey object)⟩

def packageKey (pin : Digest) : Bytes := digestStream.encode pin

def packageCell (domain : Digest) (pin : Digest) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .package (packageKey pin)⟩

def activityId (object : CellId) (birth : TransactionId) : Digest :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/ID/v1" (digestStream.encode object ++ digestStream.encode birth)

/-- The registry image of an activity cell. -/
def image (role : Role) (key body : Bytes) : Bytes :=
  LifecycleImage.bytes CanonicalCellRegistry.registry
    (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩)

/-- The activity payload a cell's canonical bytes hold, if it is an activity cell. -/
def payloadOf (bytes : Bytes) : Option ObjectiveActivityCell.Payload :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some (.live ⟨.objectiveActivity, payload⟩) => ObjectiveActivityCell.payloadAt payload.logical
  | _ => none

/-- The kernel bytes of an activity cell of one role. -/
def bodyOf (role : Role) (bytes : Bytes) : Option Bytes := do
  let payload ← payloadOf bytes
  if payload.role = role then some payload.body else none

/-- The await id: the record cell, the generation of the yield, and the digest
of the checkpoint it resumes. -/
def awaitId (cell : CellId) (generation : Nat) (checkpoint : Digest) : Digest :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/AWAIT/v1"
    (digestStream.encode cell ++ StreamCodec.nat.encode generation ++ digestStream.encode checkpoint)

/-- Spent by every turn that ends the await: the nullifier bound to the
checkpoint digest (through the id). -/
def awaitClaim (id : Digest) : StableNullifier := claim "await" (digestStream.encode id)

/-- Every delivery of one await shares one transaction id: an exact retry is a
replay, any different delivery is a transaction conflict. -/
def deliveryTransaction (id : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/DELIVER/v1" (digestStream.encode id)

/-- An activity's purse on the Book: the account whose id is its record cell's
id. The directory gives that id to the record cell, so no account cell (and so
no account capability) can exist at it; the birth registers it fresh. -/
def heldAccount (cell : CellId) : AccountId := cell.value

/-! ## Configuration and fees -/

/-- The public price of a DECLARED envelope of ticks. -/
structure Tariff where
  base : Nat
  perTick : Nat
  deriving DecidableEq, Repr

def Tariff.price (tariff : Tariff) (ticks : Nat) : Nat := tariff.base + tariff.perTick * ticks

structure Config where
  /-- The deployment: its domain names the activity coordinates; its Book holds the fees. -/
  deployment : CanonicalCellRegistry.Deployment
  /-- The credit asset fees are paid in, and the account that collects them. -/
  asset : AssetId
  collector : AccountId
  limits : Limits
  planBudget : Budget
  maxTicks : Nat
  maxPatience : Nat
  typeFuel : Nat
  maxArtifactBytes : Nat
  tariff : Tariff

def Config.domain (config : Config) : Digest := config.deployment.domain
def Config.bookCell (config : Config) : CellId := ⟨config.deployment.resourceBookId⟩

/-- The escrow terms for an activity. -/
def escrowOf (tariff : Tariff) (payer : SubjectId) (account : AccountId) (resumeTicks timeoutTicks : Nat) :
    Escrow :=
  ⟨payer, account, resumeTicks, timeoutTicks, tariff.price resumeTicks, tariff.price timeoutTicks⟩

def Escrow.pair (escrow : Escrow) : Nat := escrow.resumeFee + escrow.timeoutFee

/-- How an await ended: by its outcome (reply, refusal, unknown, broken, a due
height) or by its deadline. -/
inductive Path where
  | resumed
  | timedOut
  deriving DecidableEq, Repr

/-- The fee the ending turn uses, and the one that stays in the purse.
Functions of the escrow and the path only. -/
def Escrow.used (escrow : Escrow) : Path → Nat
  | .resumed => escrow.resumeFee
  | .timedOut => escrow.timeoutFee
def Escrow.unused (escrow : Escrow) : Path → Nat
  | .resumed => escrow.timeoutFee
  | .timedOut => escrow.resumeFee
def Escrow.ticks (escrow : Escrow) : Path → Nat
  | .resumed => escrow.resumeTicks
  | .timedOut => escrow.timeoutTicks

/-! ## Refusals -/

inductive Refusal where
  | packageMissing | packageIdentity | packageType (reason : String) | packageExists
  | inputType | outcomeProtocol (label : String)
  | recordExists | recordMissing | recordMisplaced | notAwaiting | awaitMismatch | checkpointDigest | checkpointCodec
  | envelope (ticks maximum : Nat) | patience (patience maximum : Nat)
  | plan (reason : String) | messageAwaitNeedsInbox
  | planExtraction (reason : String) | resultExtraction (reason : String)
  | exhausted
  | responseType (label : String)
  | slotMissing | slotFresh | slotMismatch | slot (reason : AnswerSlot.Refusal)
  | notYetDecided (deadline height : Nat) | notYetDue (due height : Nat)
  /-- The Book is not a live Book cell at the deployment's Book id. -/
  | bookUnavailable
  /-- The purse is already a Book account (a second birth of one record). -/
  | purseTaken
  /-- The payer is the issuer well, the collector or the purse itself. -/
  | payerInvalid
  /-- The deposit cannot reserve the first await's fee pair. -/
  | underfunded (deposit pair : Nat)
  /-- The purse cannot reserve the next await's fee pair: the activity stays
  parked at its yield until a `topUp`. -/
  | awaitsFunding (available pair : Nat)
  /-- The Book refused the postings (an account absent or overdrawn). -/
  | bookRefused
  | zeroAmount
  deriving Repr

/-! ## Typing data against declared types

The kernel never asks whether data "conforms": it types the data's own closed
Core4 term with the actual checker (`ObjectiveBendTyping.check`), annotating
each injection with the constructor type the declared type gives it, and
requires the checked type to agree with the declared one. A response typed this
way is exactly the premise of `typed_resume_preserved`. -/

def unalias (bounds : Bounds) : Ty → Ty
  | .variable index => (bounds.lookup index).getD (.variable index)
  | other => other

/-- Injection annotations for one datum at one declared type, by source path. -/
def dataAnnotations (bounds : Bounds) : Nat → Data → Ty → List Nat → List (List Nat × LambdaAnnotation)
  | 0, _, _, _ => []
  | fuel + 1, .variant label payload, type, position =>
      match unalias bounds type with
      | .variant row => match row.lookup bounds 64 label with
        | some payloadType =>
          (position, ⟨payloadType, .variant row, .unrestricted, .reusable⟩) ::
            dataAnnotations bounds fuel payload payloadType (position ++ [0])
        | none => []
      | _ => []
  | fuel + 1, .record fields, type, position =>
      (fields.zipIdx).flatMap fun ((name, value), index) =>
        match (unalias bounds type).lookup bounds 64 name with
        | some member => dataAnnotations bounds fuel value member (position ++ [index])
        | none => []
  | _ + 1, _, _, _ => []

def annotationsOf (entries : List (List Nat × LambdaAnnotation)) : List Nat → Option LambdaAnnotation :=
  fun path => (entries.find? (fun entry => entry.1 == path)).map Prod.snd

def dataSource (assumptions : Assumptions) (data : Data) (type : Ty) : AnnotatedTerm :=
  ⟨data.term, annotationsOf (dataAnnotations assumptions.bounds 64 data type []), assumptions⟩

/-- A datum typed at a declared type by the actual checker. -/
structure TypedData (assumptions : Assumptions) (data : Data) (type : Ty) where
  private mk ::
  checked : Checked (dataSource assumptions data type) []
  agrees : sameType assumptions checked.type type = true

def typeData (assumptions : Assumptions) (fuel : Nat) (data : Data) (type : Ty) :
    Option (TypedData assumptions data type) := do
  let checked ← check (dataSource assumptions data type) [] fuel
  if agrees : sameType assumptions checked.type type = true then some ⟨checked, agrees⟩ else none

/-- The typing derivation the resume contract consumes. -/
theorem TypedData.typed {assumptions : Assumptions} {data : Data} {type : Ty}
    (typed : TypedData assumptions data type) :
    PartialTyping assumptions [] data.term type typed.checked.uses :=
  .conversion typed.checked.derivation typed.agrees

/-! ## Await outcomes -/

/-- Every await resolves to exactly one of these (the root's sum, with
`conflict` added: B2). A `conflict` carries the outcome the await DID resolve
to (`decided`), so the activity sees the reply it lost to a stale read. -/
inductive AwaitOutcome where
  | reply (value : Data)
  | refused
  | unknown
  | timedOut
  | broken
  | upgraded
  | conflict (stale : Nat) (decided : AwaitOutcome)
  deriving Repr

def AwaitOutcome.label : AwaitOutcome → String
  | .reply _ => "reply" | .refused => "refused" | .unknown => "unknown" | .timedOut => "timedOut"
  | .broken => "broken" | .upgraded => "upgraded" | .conflict _ _ => "conflict"

/-- The response datum the activity is resumed with. -/
def AwaitOutcome.data : AwaitOutcome → Data
  | .reply value => .variant "reply" value
  | .conflict stale decided =>
      .variant "conflict" (.record [("stale", .natural stale), ("decided", decided.data)])
  | .refused => .variant "refused" (.record [])
  | .unknown => .variant "unknown" (.record [])
  | .timedOut => .variant "timedOut" (.record [])
  | .broken => .variant "broken" (.record [])
  | .upgraded => .variant "upgraded" (.record [])

/-- The kernel's own outcomes, which every activity's response type must type
at birth, bare and inside a `conflict` (a reply is typed when it is decided). -/
def kernelOutcomes : List AwaitOutcome :=
  let bare : List AwaitOutcome := [.refused, .unknown, .timedOut, .broken, .upgraded]
  bare ++ bare.map (.conflict 0)

/-- The type a reply must have: the `reply` member of the response sum. -/
def replyType (assumptions : Assumptions) (response : Ty) : Option Ty :=
  match unalias assumptions.bounds response with
  | .variant row => row.lookup assumptions.bounds 64 "reply"
  | _ => none

/-- The reply type a `conflict` carries in its `decided` field. -/
def conflictReplyType (assumptions : Assumptions) (response : Ty) : Option Ty := do
  let .variant row := unalias assumptions.bounds response | none
  let lost ← row.lookup assumptions.bounds 64 "conflict"
  let decided ← (unalias assumptions.bounds lost).lookup assumptions.bounds 64 "decided"
  replyType assumptions decided

/-! ## The pinned program -/

/-- The checked package of an activity and its instantiation with its input. -/
structure Program (config : Config) (pin : Digest) (input : Data) where
  private mk ::
  artifact : ObjectiveBendSourceArtifact.Artifact
  identity : ObjectiveBendSourceArtifact.identity artifact = pin
  definition : ObjectiveBendSourceArtifact.Checked artifact config.maxArtifactBytes
  domain : Ty
  applied : AnnotatedTerm
  appliedExact : applied = ⟨.app definition.packet.source.term input.term,
    fun path => match path with
      | 0 :: rest => definition.packet.source.annotations rest
      | 1 :: rest => annotationsOf (dataAnnotations definition.packet.source.assumptions.bounds 64 input domain []) rest
      | _ => none,
    definition.packet.source.assumptions⟩
  checked : Checked applied []
  planType : Ty
  responseType : Ty
  resultType : Ty
  typeExact : checked.type = .computation planType responseType resultType
  reply : Ty
  replyExact : replyType applied.assumptions responseType = some reply

def Program.assumptions {config : Config} {pin : Digest} {input : Data} (program : Program config pin input) :
    Assumptions := program.applied.assumptions

/-- The package bytes a snapshot holds for a pin (empty when absent). -/
def packageBytes {rootBytes : Bytes → Digest} (config : Config) (snapshot : DataSnapshot rootBytes)
    (pin : Digest) : Bytes :=
  (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain pin))).getD []

/-- Load the artifact from its cell, check the definition, instantiate it with
the input (typed at the declared domain), and check the instantiation. -/
def loadProgram (config : Config) (bytes : Bytes) (pin : Digest) (input : Data) :
    Except Refusal (Program config pin input) := do
  let some artifact := ObjectiveBendSourceArtifact.decode bytes | throw .packageMissing
  if identity : ObjectiveBendSourceArtifact.identity artifact = pin then
    let definition ← match ObjectiveBendSourceArtifact.checkWithin artifact config.maxArtifactBytes config.typeFuel with
      | .ok checked => pure checked
      | .error reason => throw (.packageType reason)
    let source := definition.packet.source
    match callable definition.typed.type with
    | .arrow _ _ domain _ =>
      let applied : AnnotatedTerm := ⟨.app source.term input.term,
        fun path => match path with
          | 0 :: rest => source.annotations rest
          | 1 :: rest => annotationsOf (dataAnnotations source.assumptions.bounds 64 input domain []) rest
          | _ => none,
        source.assumptions⟩
      let some checked := check applied [] config.typeFuel | throw .inputType
      match typeExact : checked.type with
      | .computation planType responseType resultType =>
        match replyExact : replyType applied.assumptions responseType with
        | some reply =>
          pure ⟨artifact, identity, definition, domain, applied, rfl, checked, planType, responseType,
            resultType, typeExact, reply, replyExact⟩
        | none => throw (.outcomeProtocol "reply")
      | _ => throw (.packageType "the definition does not return an Activity")
    | _ => throw (.packageType "the definition takes no input")
  else throw .packageIdentity

/-- Type an outcome at the program's response type. -/
def typeOutcome {config : Config} {pin : Digest} {input : Data} (program : Program config pin input)
    (outcome : AwaitOutcome) : Except Refusal (TypedData program.assumptions outcome.data program.responseType) :=
  match typeData program.assumptions config.typeFuel outcome.data program.responseType with
  | some typed => .ok typed
  | none => .error (.responseType outcome.label)

/-- At birth: every kernel outcome is typed at the response type, bare and in a
`conflict`, and a `conflict`'s decided reply has the reply type itself, so no
outcome the kernel can deliver is ill-typed later (an ill-typed delivery would
park the activity for ever). -/
def outcomeProtocol {config : Config} {pin : Digest} {input : Data} (program : Program config pin input) :
    Except Refusal Unit := do
  for outcome in kernelOutcomes do
    if (typeData program.assumptions config.typeFuel outcome.data program.responseType).isNone then
      throw (.outcomeProtocol outcome.label)
  match conflictReplyType program.assumptions program.responseType with
  | some lost =>
    if sameType program.assumptions lost program.reply then pure ()
    else throw (.outcomeProtocol "conflict.decided.reply")
  | none => throw (.outcomeProtocol "conflict.decided.reply")

/-! ## Plans the kernel performs -/

inductive PlanSource where
  | reply (decider : SubjectId)
  | height (due : Nat)
  deriving DecidableEq, Repr

/-- A yielded Plan: `await {state, on, patience}`. The declared state is
written to the object's state cell; `on` names what the activity waits for; the
deadline is the yield height plus `patience`. -/
structure PlanAwait where
  state : Data
  source : PlanSource
  patience : Nat

def fieldOf (fields : List (String × Data)) (name : String) : Option Data :=
  (fields.find? (fun field => field.1 == name)).map Prod.snd

def decodePlan : Data → Except Refusal PlanAwait
  | .variant "await" (.record fields) => do
    let some state := fieldOf fields "state" | throw (.plan "await.state missing")
    let some (.natural patience) := fieldOf fields "patience" | throw (.plan "await.patience missing")
    let some on := fieldOf fields "on" | throw (.plan "await.on missing")
    let source ← match on with
      | .variant "reply" (.record ask) => match fieldOf ask "decider" with
        | some (.natural decider) => pure (PlanSource.reply ⟨decider⟩)
        | _ => throw (.plan "await.on.reply.decider missing")
      | .variant "height" (.record due) => match fieldOf due "at" with
        | some (.natural height) => pure (PlanSource.height height)
        | _ => throw (.plan "await.on.height.at missing")
      | .variant "message" _ => throw .messageAwaitNeedsInbox
      | _ => throw (.plan "await.on must be reply, height or message")
    pure ⟨state, source, patience⟩
  | _ => throw (.plan "the kernel performs only `await` Plans")

/-- What one segment of an activity ends in. A yield keeps the yielded machine
state COLLECTED (`ObjectiveBendDemandCollect.collect`: only what the yielded
Plan and the stack reach, compacted), so a checkpoint is storage-charged for
what the continuation can use, not for every cell the run ever allocated; the
Plan is extracted from the uncollected state. Resuming the collected state is
resuming the original (`ObjectiveResumeContract.runSegment_collect`). -/
inductive Segment where
  | yielded (state : State) (plan : PlanAwait)
  | finished (result : Data)
  | faulted (reason : String)

/-- Run one segment from `start` within a declared envelope. Running out of
envelope commits nothing (`exhausted`): the activity stays where it was. -/
def runSegment (config : Config) (ticks : Nat) (start : State) : Except Refusal Segment :=
  match runBounded config.limits ticks start with
  | .yielded _ yielded =>
    match ObjectiveBendDemandData.yieldedPlan config.limits config.planBudget yielded with
    | .ok extracted => do
      let plan ← decodePlan extracted.value
      pure (.yielded (ObjectiveBendDemandCollect.collect yielded) plan)
    | .error (failure, _) => .error (.planExtraction (reprStr failure))
  | .finished _ finished =>
    match ObjectiveBendDemandData.complete config.limits config.planBudget finished with
    | .ok result => .ok (.finished result.value)
    | .error (failure, _) => .error (.resultExtraction (reprStr failure))
  | .divergent _ _ => .ok (.faulted "divergent")
  | .refused reason _ => .ok (.faulted (reprStr reason))
  | .suspended _ _ => .error .exhausted

def Segment.yields : Segment → Bool
  | .yielded _ _ => true
  | _ => false

/-! ## Turns -/

abbrev Snapshot (rootBytes : Bytes → Digest) := DataSnapshot rootBytes

def postAt {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) (bytes : Bytes) : Post :=
  ⟨cell, snapshot.model.roots cell, bytes⟩

def guardAt {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : ReadGuard :=
  ⟨cell, snapshot.model.roots cell⟩

def recordPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (cell : CellId) (record : Record) : Post :=
  postAt snapshot cell (image .record (recordKey record.object record.activity) (encodeRecord record))

def slotPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (slot : AnswerSlot.Slot) : Post :=
  postAt snapshot (AnswerSlot.cell config.domain slot.name) (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))

/-- The image a declared-state write installs. -/
def stateImage (object : CellId) (value : Data) : Bytes := image .state (stateKey object) (dataBytes value)

def readRecord {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : Option Record :=
  (bodyOf .record (snapshot.canonicalBytes cell)).bind decodeRecord

def readSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (name : Digest) :
    Option AnswerSlot.Slot :=
  (bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name))).bind AnswerSlot.decode

/-! ### The Book -/

abbrev BookCell := CellState.Materialized (CanonicalCellRegistry.materializer .resourceBook)

/-- The Book a cell's canonical bytes hold, if it is a live Book cell. -/
def bookOf (bytes : Bytes) : Option BookCell :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some (.live ⟨.resourceBook, payload⟩) => some payload
  | _ => none

def loadBook {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) :
    Except Refusal BookCell :=
  match bookOf (snapshot.canonicalBytes config.bookCell) with
  | some book => .ok book
  | none => .error .bookUnavailable

/-- Postings admitted on the loaded Book: the accepted batch and its post. -/
structure Postings (pre : BookCell) where
  private mk ::
  batch : Batch
  accepted : AcceptedBatch pre batch

def postings (pre : BookCell) (batch : Batch) : Except Refusal (Postings pre) :=
  if admitted : batch.Admission (logicalBook pre.logical) then
    .ok ⟨batch, AcceptedBatch.ofAdmission admitted⟩
  else .error .bookRefused

def Postings.post {pre : BookCell} (posted : Postings pre) : BookCell := posted.accepted.post

def Postings.write {rootBytes : Bytes → Digest} {pre : BookCell} (config : Config) (snapshot : Snapshot rootBytes)
    (posted : Postings pre) : Post :=
  postAt snapshot config.bookCell
    (LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, posted.post⟩))

/-- Every admitted posting conserves every asset (the Book's posting theorem). -/
theorem Postings.conserves {pre : BookCell} (posted : Postings pre) (asset : AssetId) :
    (logicalBook posted.post.logical).totalAsset asset = (logicalBook pre.logical).totalAsset asset :=
  posted.accepted.conserves asset

/-- The purse balance on a Book, as a natural. -/
def purse (book : Book) (asset : AssetId) (held : AccountId) : Nat := (book.balance held asset).toNat

/-! ### Yields -/

/-- What a yield commits besides the record: the declared-state write, the
answer slot it opens, and the await. -/
structure YieldCommit where
  await : Await
  posts : List Post
  reads : List ReadGuard

def commitYield {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell : CellId) (object : CellId) (generation : Nat)
    (checkpoint : Digest) (plan : PlanAwait) : Except Refusal YieldCommit := do
  if plan.patience = 0 ∨ config.maxPatience < plan.patience then
    throw (.patience plan.patience config.maxPatience)
  let deadline := height + plan.patience
  let id := awaitId cell generation checkpoint
  let stateBytes := stateImage object plan.state
  let statePost := postAt snapshot (stateCell config.domain object) stateBytes
  let reads : List ReadGuard := [⟨stateCell config.domain object, rootBytes stateBytes⟩]
  match plan.source with
  | .reply decider =>
    let slotName := AnswerSlot.name transaction cell generation
    if (readSlot config snapshot slotName).isSome then throw .slotFresh
    let slot : AnswerSlot.Slot := ⟨slotName, cell, decider, deadline, .opened⟩
    pure ⟨⟨id, .reply slotName decider, deadline, height⟩, [statePost, slotPost config snapshot slot], reads⟩
  | .height due =>
    if deadline < due then throw (.plan "a height await is due after its deadline")
    pure ⟨⟨id, .height due, deadline, height⟩, [statePost], reads⟩

/-- The record that ends a segment. -/
def nextRecord (base : Record) (generation : Nat) : Segment → Option YieldCommit → Record
  | .yielded state _, some yielded =>
    let encoded := checkpointBytes state
    { base with
      generation := generation
      checkpoint := encoded
      checkpointDigest := ObjectiveActivityWire.checkpointDigest encoded
      reads := yielded.reads
      phase := .awaiting yielded.await }
  | .finished result, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      reads := []
      phase := .done (dataBytes result) }
  | .faulted reason, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      reads := []
      phase := .faulted reason }
  | .yielded _ _, none =>
    { base with generation := generation, phase := .faulted "internal: yield without commit" }

/-- The yield commit of a segment, when it yielded. -/
def segmentCommit {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell object : CellId) (generation : Nat) :
    Segment → Except Refusal (Option YieldCommit)
  | .yielded state plan => do
    let committed ← commitYield config snapshot height transaction cell object generation
      (checkpointDigest (checkpointBytes state)) plan
    pure (some committed)
  | _ => pure none

/-- After a segment: a yield must leave the purse able to pay the await's fee
pair (it stays reserved there); an end returns the purse to the payer. The
ending turn's own postings come first (`before`). -/
def settlePurse (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (before : Batch) (segment : Segment) : Except Refusal Batch :=
  let after := purse (before.apply book) config.asset held
  if segment.yields then
    if escrow.pair ≤ after then .ok before
    else .error (.awaitsFunding after escrow.pair)
  else if after = 0 then .ok before
  else .ok ⟨before.registrations,
    before.operations ++ [.transfer held escrow.account config.asset after]⟩

/-! ### publish -/

/-- The output codec an activity artifact names: its entry returns an
`Activity<P,R,A>`, never a native method result. -/
def codecId : Digest := tagged "DREGG/OBJECTIVE/ACTIVITY/OUTPUT-CODEC/v1" []

def publishTransaction (pin : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/PUBLISH/v1" (digestStream.encode pin)

structure Publication {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (artifactBytes : Bytes) where
  private mk ::
  pin : Digest
  posts : List Post
  postsExact : posts = [postAt snapshot (packageCell config.domain pin) (image .package (packageKey pin) artifactBytes)]

def publish {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (artifactBytes : Bytes) : Except Refusal (Publication config snapshot artifactBytes) := do
  let some artifact := ObjectiveBendSourceArtifact.decode artifactBytes | throw .packageMissing
  if artifact.outputCodec ≠ codecId then throw (.packageType "not an activity artifact")
  let pin := ObjectiveBendSourceArtifact.identity artifact
  if (payloadOf (snapshot.canonicalBytes (packageCell config.domain pin))).isSome then throw .packageExists
  let definition ← match ObjectiveBendSourceArtifact.checkWithin artifact config.maxArtifactBytes config.typeFuel with
    | .ok checked => pure checked
    | .error reason => throw (.packageType reason)
  match callable definition.typed.type with
  | .arrow _ _ _ (.computation _ _ _) => pure ()
  | _ => throw (.packageType "an activity package selects a definition `Input -> Activity<P,R,A>`")
  pure ⟨pin, _, rfl⟩

def Publication.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {artifactBytes : Bytes} (publication : Publication config snapshot artifactBytes) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (publishTransaction publication.pin) publication.posts [] [] sealing

/-! ### birth -/

structure BirthRequest where
  subject : SubjectId
  object : CellId
  pin : Digest
  input : Data
  nonce : Nat
  ticks : Nat
  resumeTicks : Nat
  timeoutTicks : Nat
  /-- The payer's Book account: it pays the birth's envelope and the deposit,
  and receives the purse when the activity ends. -/
  account : AccountId
  /-- Moved into the activity's purse; must reserve the first await's fee pair. -/
  deposit : Nat

def birthTransaction (request : BirthRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/BIRTH/v2"
    (subjectStream.encode request.subject ++ digestStream.encode request.object ++
      digestStream.encode request.pin ++ bytesStream.encode (dataBytes request.input) ++
      StreamCodec.nat.encode request.nonce)

/-- The birth's postings: register the purse, pay the birth's declared envelope
to the collector, move the deposit into the purse; then the purse settles
(`settlePurse`). -/
def birthBatch (config : Config) (book : Book) (held : AccountId) (request : BirthRequest)
    (escrow : Escrow) (segment : Segment) : Except Refusal Batch :=
  settlePurse config (Batch.apply ⟨[held], []⟩ book) held escrow
    ⟨[], [.fee request.account config.collector config.asset (config.tariff.price request.ticks)] ++
      (if request.deposit = 0 then [] else [.transfer request.account held config.asset request.deposit])⟩ segment
  |>.map fun settled => ⟨held :: settled.registrations, settled.operations⟩

/-- An admitted birth: the program, its first segment from its initial state,
and the posts that commit the record, the yield and the Book postings. -/
structure Birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) where
  private mk ::
  program : Program config request.pin request.input
  programExact : loadProgram config (packageBytes config snapshot request.pin) request.pin request.input =
    .ok program
  cell : CellId
  cellExact : cell = recordCell config.domain request.object (activityId request.object (birthTransaction request))
  segment : Segment
  segmentExact : runSegment config request.ticks (initial program.applied.erase) = .ok segment
  yielded : Option YieldCommit
  yieldedExact : segmentCommit config snapshot height (birthTransaction request) cell request.object 0 segment =
    .ok yielded
  record : Record
  recordExact : record = nextRecord
    ⟨request.object, activityId request.object (birthTransaction request), request.pin, dataBytes request.input,
      0, [], checkpointDigest [], [],
      escrowOf config.tariff request.subject request.account request.resumeTicks request.timeoutTicks,
      .faulted "unborn"⟩ 0 segment yielded
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  posts : List Post
  recordFirst : posts.head? = some (recordPost config snapshot cell record)
  postsExact : posts = recordPost config snapshot cell record ::
    ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
  guards : List ReadGuard
  guardsExact : guards = [guardAt snapshot (packageCell config.domain request.pin)]

def birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) : Except Refusal (Birth config snapshot height request) := do
  if config.maxTicks < request.ticks then throw (.envelope request.ticks config.maxTicks)
  if config.maxTicks < request.resumeTicks then throw (.envelope request.resumeTicks config.maxTicks)
  if config.maxTicks < request.timeoutTicks then throw (.envelope request.timeoutTicks config.maxTicks)
  match programExact : loadProgram config (packageBytes config snapshot request.pin) request.pin request.input with
  | .error reason => throw reason
  | .ok program =>
    outcomeProtocol program
    let transaction := birthTransaction request
    let activity := activityId request.object transaction
    let cell := recordCell config.domain request.object activity
    if (payloadOf (snapshot.canonicalBytes cell)).isSome then throw .recordExists
    let held := heldAccount cell
    if request.account = config.asset ∨ request.account = config.collector ∨ request.account = held then
      throw .payerInvalid
    match bookExact : loadBook config snapshot with
    | .error reason => throw reason
    | .ok book =>
      if held ∈ (logicalBook book.logical).accounts then throw .purseTaken
      match segmentExact : runSegment config request.ticks (initial program.applied.erase) with
      | .error reason => throw reason
      | .ok segment =>
        match yieldedExact : segmentCommit config snapshot height transaction cell request.object 0 segment with
        | .error reason => throw reason
        | .ok yielded =>
          let escrow := escrowOf config.tariff request.subject request.account request.resumeTicks request.timeoutTicks
          if segment.yields ∧ request.deposit < escrow.pair then
            throw (.underfunded request.deposit escrow.pair)
          let batch ← birthBatch config (logicalBook book.logical) held request escrow segment
          let posted ← postings book batch
          let base : Record := ⟨request.object, activity, request.pin, dataBytes request.input, 0, [],
            checkpointDigest [], [], escrow, .faulted "unborn"⟩
          let record := nextRecord base 0 segment yielded
          let posts := recordPost config snapshot cell record ::
            ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
          pure ⟨program, programExact, cell, rfl, segment, segmentExact, yielded, yieldedExact, record, rfl,
            book, bookExact, posted, posts, rfl, rfl, [guardAt snapshot (packageCell config.domain request.pin)], rfl⟩

def Birth.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (birthTransaction request) born.posts born.guards [] sealing

/-- **A birth conserves every asset**: its postings are one admitted batch on
the loaded Book. -/
theorem Birth.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) (asset : AssetId) :
    (logicalBook born.posted.post.logical).totalAsset asset = (logicalBook born.book.logical).totalAsset asset :=
  born.posted.conserves asset

/-! ### resolve -/

inductive Answer where
  | reply (value : Data)
  | refused (reason : String)
  | unknown
  | broken (reason : String)
  deriving Repr

def Answer.decision : Answer → AnswerSlot.Decision
  | .reply value => .reply (dataBytes value)
  | .refused reason => .refused reason
  | .unknown => .unknown
  | .broken reason => .broken reason

structure ResolveRequest where
  subject : SubjectId
  slot : Digest
  answer : Answer

def resolveTransaction (slot : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/RESOLVE/v1" (digestStream.encode slot)

/-- A reply must be typed at the awaiting activity's own declared reply type. -/
def replyTyped {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (activity : CellId) (slot : Digest) : Answer → Except Refusal Unit
  | .reply value => do
    let some record := readRecord snapshot activity | throw .recordMissing
    let .awaiting await := record.phase | throw .notAwaiting
    let .reply named _ := await.source | throw .slotMismatch
    if named ≠ slot then throw .slotMismatch
    let some input := decodeDataBytes record.input | throw .inputType
    let program ← loadProgram config (packageBytes config snapshot record.pin) record.pin input
    match typeData program.assumptions config.typeFuel value program.reply with
    | some _ => pure ()
    | none => throw (.responseType "reply")
  | _ => pure ()

structure Resolution {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ResolveRequest) where
  private mk ::
  slot : AnswerSlot.Slot
  slotExact : readSlot config snapshot request.slot = some slot
  named : slot.name = request.slot
  decided : AnswerSlot.Slot
  decidedExact : AnswerSlot.decide slot request.subject height request.answer.decision = .ok decided
  typed : replyTyped config snapshot slot.activity request.slot request.answer = .ok ()
  posts : List Post
  postsExact : posts = [slotPost config snapshot decided]

def resolve {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ResolveRequest) : Except Refusal (Resolution config snapshot height request) :=
  match slotExact : readSlot config snapshot request.slot with
  | none => .error .slotMissing
  | some slot =>
    if named : slot.name = request.slot then
      match decidedExact : AnswerSlot.decide slot request.subject height request.answer.decision with
      | .error reason => .error (.slot reason)
      | .ok decided =>
        match typed : replyTyped config snapshot slot.activity request.slot request.answer with
        | .error reason => .error reason
        | .ok () => .ok ⟨slot, slotExact, named, decided, decidedExact, typed, _, rfl⟩
    else .error .slotMismatch

def Resolution.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request)
    (sealing : Seal) : DataIntent rootBytes :=
  intentOf rootBytes (resolveTransaction request.slot) resolution.posts
    [guardAt snapshot resolution.slot.activity] [AnswerSlot.decisionClaim request.slot] sealing

/-! ### deliver -/

structure Settlement where
  path : Path
  decided : AwaitOutcome
  posts : List Post
  guards : List ReadGuard
  claims : List StableNullifier

def outcomeOfDecision : AnswerSlot.Decision → Except Refusal AwaitOutcome
  | .reply bytes => match decodeDataBytes bytes with
    | some value => .ok (.reply value)
    | none => .error (.responseType "reply")
  | .refused _ => .ok .refused
  | .unknown => .ok .unknown
  | .broken _ => .ok .broken
  | .expired => .ok .timedOut

/-- How the await ends at this height: its decided slot, its due height, or its
deadline. A function of the snapshot, the height and the await only. -/
def settle {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (cell : CellId) (await : Await) : Except Refusal Settlement :=
  match await.source with
  | .reply slotName _ =>
    match readSlot config snapshot slotName with
    | none => .error .slotMissing
    | some slot =>
      if slot.name ≠ slotName ∨ slot.activity ≠ cell then .error .slotMismatch else
      match slot.phase with
      | .decided decision _ => do
        let outcome ← outcomeOfDecision decision
        pure ⟨if decision = .expired then .timedOut else .resumed, outcome, [],
          [guardAt snapshot (AnswerSlot.cell config.domain slotName)], []⟩
      | .opened =>
        match AnswerSlot.expire slot height with
        | .ok expired => .ok ⟨.timedOut, .timedOut, [slotPost config snapshot expired], [],
            [AnswerSlot.decisionClaim slotName]⟩
        | .error _ => .error (.notYetDecided await.deadline height)
  | .height due =>
    if await.deadline < height then .ok ⟨.timedOut, .timedOut, [], [], []⟩
    else if due ≤ height then .ok ⟨.resumed, .reply (.record [("at", .natural height)]), [], [], []⟩
    else .error (.notYetDue due height)

/-- The number of recorded reads whose cell moved since the yield. -/
def staleCount {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (reads : List ReadGuard) : Nat :=
  (reads.filter (fun guard => snapshot.model.roots guard.cellId != guard.expectedRoot)).length

/-- A stale read wraps the decided outcome; it never replaces it. -/
def revalidate (stale : Nat) (decided : AwaitOutcome) : AwaitOutcome :=
  if stale = 0 then decided else .conflict stale decided

/-- No state, no checkpoint and no outcome is ever taken from a request: the
submitter names the record and may add envelope it pays for from `account`. -/
structure DeliverRequest where
  subject : SubjectId
  record : CellId
  extraTicks : Nat
  account : AccountId

/-- The ending turn's own postings: the used fee from the purse, and the
submitter's added envelope from its account, both to the collector. -/
def deliveryCharges (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : DeliverRequest) : Batch :=
  ⟨[], [.fee (heldAccount cell) config.collector config.asset (record.escrow.used path)] ++
    (if request.extraTicks = 0 then []
     else [.fee request.account config.collector config.asset (config.tariff.price request.extraTicks)])⟩

structure Delivery {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : DeliverRequest) where
  private mk ::
  record : Record
  recordExact : readRecord snapshot request.record = some record
  located : request.record = recordCell config.domain record.object record.activity
  await : Await
  awaiting : record.phase = .awaiting await
  idExact : await.id = awaitId request.record record.generation record.checkpointDigest
  digestExact : checkpointDigest record.checkpoint = record.checkpointDigest
  input : Data
  inputExact : decodeDataBytes record.input = some input
  program : Program config record.pin input
  programExact : loadProgram config (packageBytes config snapshot record.pin) record.pin input = .ok program
  settlement : Settlement
  settled : settle config snapshot height request.record await = .ok settlement
  outcome : AwaitOutcome
  outcomeExact : outcome = revalidate (staleCount snapshot record.reads) settlement.decided
  response : TypedData program.assumptions outcome.data program.responseType
  state : State
  stateExact : decodeCheckpoint record.checkpoint = some state
  resumed : State
  resumeExact : resume outcome.data.term state = some resumed
  envelope : Nat
  envelopeExact : envelope = record.escrow.ticks settlement.path + request.extraTicks
  segment : Segment
  segmentExact : runSegment config envelope resumed = .ok segment
  yielded : Option YieldCommit
  yieldedExact : segmentCommit config snapshot height (deliveryTransaction await.id) request.record record.object
    (record.generation + 1) segment = .ok yielded
  next : Record
  nextExact : next = nextRecord record (record.generation + 1) segment yielded
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  batch : Batch
  batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow
    (deliveryCharges config record request.record settlement.path request) segment = .ok batch
  posted : Postings book
  postedBatch : posted.batch = batch
  posts : List Post
  recordFirst : posts.head? = some (recordPost config snapshot request.record next)
  postsExact : posts = recordPost config snapshot request.record next ::
    (settlement.posts ++ (yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
  guards : List ReadGuard
  guardsExact : guards = guardAt snapshot (packageCell config.domain record.pin) ::
    (settlement.guards ++ record.reads.map (fun guard => guardAt snapshot guard.cellId))
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: settlement.claims

def deliver {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : DeliverRequest) : Except Refusal (Delivery config snapshot height request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error .recordMissing
  | some record =>
  if located : request.record = recordCell config.domain record.object record.activity then
  match awaiting : record.phase with
  | .done _ | .faulted _ => .error .notAwaiting
  | .awaiting await =>
  if idExact : await.id = awaitId request.record record.generation record.checkpointDigest then
  if digestExact : checkpointDigest record.checkpoint = record.checkpointDigest then
  match inputExact : decodeDataBytes record.input with
  | none => .error .inputType
  | some input =>
  match programExact : loadProgram config (packageBytes config snapshot record.pin) record.pin input with
  | .error reason => .error reason
  | .ok program =>
  match settled : settle config snapshot height request.record await with
  | .error reason => .error reason
  | .ok settlement =>
  let outcome := revalidate (staleCount snapshot record.reads) settlement.decided
  match typeOutcome program outcome with
  | .error reason => .error reason
  | .ok response =>
  match stateExact : decodeCheckpoint record.checkpoint with
  | none => .error .checkpointCodec
  | some state =>
  match resumeExact : resume outcome.data.term state with
  | none => .error .checkpointCodec
  | some resumed =>
  let envelope := record.escrow.ticks settlement.path + request.extraTicks
  if config.maxTicks < envelope then .error (.envelope envelope config.maxTicks) else
  match segmentExact : runSegment config envelope resumed with
  | .error reason => .error reason
  | .ok segment =>
  let transaction := deliveryTransaction await.id
  match yieldedExact : segmentCommit config snapshot height transaction request.record record.object
      (record.generation + 1) segment with
  | .error reason => .error reason
  | .ok yielded =>
  let next := nextRecord record (record.generation + 1) segment yielded
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow
      (deliveryCharges config record request.record settlement.path request) segment with
  | .error reason => .error reason
  | .ok batch =>
  match postings book batch with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = batch then
  let posts := recordPost config snapshot request.record next ::
    (settlement.posts ++ (yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
  let guards := guardAt snapshot (packageCell config.domain record.pin) ::
    (settlement.guards ++ record.reads.map (fun guard => guardAt snapshot guard.cellId))
  .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program, programExact,
    settlement, settled, outcome, rfl, response, state, stateExact, resumed, resumeExact, envelope, rfl,
    segment, segmentExact, yielded, yieldedExact, next, rfl, book, bookExact, batch, batchExact, posted,
    postedBatch, posts, rfl, rfl, guards, rfl, awaitClaim await.id :: settlement.claims, rfl⟩
  else .error .bookRefused
  else .error .checkpointDigest
  else .error .awaitMismatch
  else .error .recordMisplaced

def Delivery.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (deliveryTransaction delivery.await.id) delivery.posts delivery.guards delivery.claims sealing

/-- **A delivery conserves every asset.** -/
theorem Delivery.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) (asset : AssetId) :
    (logicalBook delivery.posted.post.logical).totalAsset asset =
      (logicalBook delivery.book.logical).totalAsset asset :=
  delivery.posted.conserves asset

/-! ### topUp -/

structure TopUpRequest where
  subject : SubjectId
  record : CellId
  account : AccountId
  amount : Nat
  nonce : Nat

def topUpTransaction (request : TopUpRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/TOP-UP/v1"
    (subjectStream.encode request.subject ++ digestStream.encode request.record ++
      StreamCodec.nat.encode request.account ++ StreamCodec.nat.encode request.amount ++
      StreamCodec.nat.encode request.nonce)

structure TopUp {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : TopUpRequest) where
  private mk ::
  record : Record
  recordExact : readRecord snapshot request.record = some record
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount]⟩

def topUp {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : TopUpRequest) : Except Refusal (TopUp config snapshot request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error .recordMissing
  | some record =>
    match record.phase with
    | .done _ | .faulted _ => .error .notAwaiting
    | .awaiting _ =>
    if request.amount = 0 then .error .zeroAmount else
    if request.account = config.asset ∨ request.account = heldAccount request.record then .error .payerInvalid else
    match bookExact : loadBook config snapshot with
    | .error reason => .error reason
    | .ok book =>
      match postings book ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount]⟩ with
      | .error reason => .error reason
      | .ok posted =>
        if postedBatch : posted.batch = ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount]⟩ then
          .ok ⟨record, recordExact, book, bookExact, posted, postedBatch⟩
        else .error .bookRefused

def TopUp.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : TopUpRequest} (topped : TopUp config snapshot request) (sealing : Seal) : DataIntent rootBytes :=
  intentOf rootBytes (topUpTransaction request) [topped.posted.write config snapshot]
    [guardAt snapshot request.record] [] sealing

/-- **A top-up conserves every asset.** -/
theorem TopUp.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : TopUpRequest} (topped : TopUp config snapshot request) (asset : AssetId) :
    (logicalBook topped.posted.post.logical).totalAsset asset = (logicalBook topped.book.logical).totalAsset asset :=
  topped.posted.conserves asset

/-! ### writeState -/

structure StateWriteRequest where
  subject : SubjectId
  record : CellId
  value : Data
  nonce : Nat

def stateTransaction (request : StateWriteRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/STATE/v2"
    (digestStream.encode request.record ++ StreamCodec.nat.encode request.nonce ++ dataBytes request.value)

/-- The object a state write targets: the record names it. Who may write it is
the receiver's question (a holder of a capability on the object). -/
structure StateWrite {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : StateWriteRequest) where
  private mk ::
  record : Record
  recordExact : readRecord snapshot request.record = some record
  posts : List Post
  postsExact : posts = [postAt snapshot (stateCell config.domain record.object) (stateImage record.object request.value)]

def writeState {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : StateWriteRequest) : Except Refusal (StateWrite config snapshot request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error .recordMissing
  | some record => .ok ⟨record, recordExact, _, rfl⟩

def StateWrite.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : StateWriteRequest} (written : StateWrite config snapshot request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (stateTransaction request) written.posts [guardAt snapshot request.record] [] sealing

/-! ## The resume contract -/

/-- An accepted durable execution installs exactly its intent. -/
theorem execute_accepted_install {rootBytes : Bytes → Digest} {snapshot next : Snapshot rootBytes}
    {intent : DataIntent rootBytes}
    (accepted : DurableDataIntent.execute .complete snapshot intent = .accepted next) :
    next = DataSnapshot.install snapshot intent := by
  unfold DurableDataIntent.execute at accepted
  split at accepted
  · split at accepted <;> cases accepted
  · split at accepted
    · cases accepted
    · cases accepted; rfl

/-- After an intent spending `spent` installs, NO intent spending it again is
accepted, under any schedule: either the journal answers first (an exact retry
replays, anything else under the same transaction conflicts) or the claim is
already consumed. -/
theorem spent_claim_never_accepted {rootBytes : Bytes → Digest} {snapshot next : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {spent : StableNullifier}
    (carries : spent ∈ intent.nullifiers)
    (installed : DurableDataIntent.execute .complete snapshot intent = .accepted next)
    (later : DataIntent rootBytes) (again : spent ∈ later.nullifiers) (schedule : DurableCommitProtocol.Schedule)
    (after : Snapshot rootBytes) :
    DurableDataIntent.execute schedule next later ≠ .accepted after := by
  have nextExact := execute_accepted_install installed
  have consumed : next.model.consumed spent = true := by
    rw [nextExact]
    exact DurableCommitProtocol.Snapshot.install_consumes snapshot.model intent.erase spent carries
  have refused := DataIntent.consumed_nullifier_refused next later spent again consumed
  intro accepted
  unfold DurableDataIntent.execute at accepted
  split at accepted
  · split at accepted <;> cases accepted
  · split at accepted
    · cases accepted
    · rename_i ok; exact refused ok

/-- An exact retry of an installed intent is a replay, never a second commit. -/
theorem installed_retry_replays {rootBytes : Bytes → Digest} {snapshot next : Snapshot rootBytes}
    {intent : DataIntent rootBytes}
    (installed : DurableDataIntent.execute .complete snapshot intent = .accepted next)
    (schedule : DurableCommitProtocol.Schedule) :
    DurableDataIntent.execute schedule next intent = .replayed intent.erase := by
  rw [execute_accepted_install installed]
  simp [DurableDataIntent.execute, DataSnapshot.install, DurableCommitProtocol.Snapshot.install,
    DurableCommitProtocol.Snapshot.lookupRecorded, DurableCommitProtocol.Intent.sameCheck_self]

/-- Whatever sealing the admitting receiver adds, a delivery's intent spends its
await's claim. -/
theorem Delivery.spends {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) (sealing : Seal) :
    awaitClaim delivery.await.id ∈ (delivery.intent sealing).nullifiers := by
  simp [Delivery.intent, delivery.claimsExact]

/-- **Consume-once.** Once a delivery of an await installs (under any sealing), no
second turn that ends that await (another delivery, a timeout, a forged intent
claiming it) is ever accepted, and the exact retry of the delivery replays. -/
theorem resume_consumes_once {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (delivery.intent sealing) = .accepted next) :
    (∀ (later : DataIntent rootBytes), awaitClaim delivery.await.id ∈ later.nullifiers →
      ∀ schedule after, DurableDataIntent.execute schedule next later ≠ .accepted after) ∧
    (∀ schedule, DurableDataIntent.execute schedule next (delivery.intent sealing) =
      .replayed (delivery.intent sealing).erase) :=
  ⟨fun later again schedule after =>
      spent_claim_never_accepted (delivery.spends sealing) installed later again schedule after,
    installed_retry_replays installed⟩

/-- A delivery from the post-state of a delivery of the same await is never
accepted, whatever seals the two carry. -/
theorem second_delivery_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height later : Nat} {request again : DeliverRequest} (first : Delivery config snapshot height request)
    (sealing : Seal) (installed : DurableDataIntent.execute .complete snapshot (first.intent sealing) = .accepted next)
    (second : Delivery config next later again) (secondSeal : Seal) (sameAwait : second.await.id = first.await.id) :
    ∀ schedule after, DurableDataIntent.execute schedule next (second.intent secondSeal) ≠ .accepted after :=
  (resume_consumes_once first sealing installed).1 (second.intent secondSeal) (sameAwait ▸ second.spends secondSeal)

/-- **The slot is decided once.** -/
theorem slot_decided_once {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (resolution.intent sealing) = .accepted next)
    (later : DataIntent rootBytes) (again : AnswerSlot.decisionClaim request.slot ∈ later.nullifiers)
    (schedule : DurableCommitProtocol.Schedule) (after : Snapshot rootBytes) :
    DurableDataIntent.execute schedule next later ≠ .accepted after :=
  spent_claim_never_accepted (by simp [Resolution.intent]) installed later again schedule after

/-- **Exactly one decider.** An admitted resolution was made by the slot's
decider, on an open slot, at or before its deadline. -/
theorem slot_single_decider {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) :
    request.subject = resolution.slot.decider ∧ resolution.slot.phase = .opened ∧
      height ≤ resolution.slot.deadline :=
  let decided := AnswerSlot.decide_single_decider resolution.decidedExact
  ⟨decided.1, decided.2.1, decided.2.2.1⟩

/-- **Stale reads deliver `conflict`, carrying what was decided.** If any read
the activity recorded at its yield has moved, the activity is resumed with
`conflict`, never with the bare outcome; the count it receives is positive and
the outcome the await resolved to travels inside it. -/
theorem stale_reads_conflict {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (moved : ∃ guard ∈ delivery.record.reads, snapshot.model.roots guard.cellId ≠ guard.expectedRoot) :
    ∃ stale, 0 < stale ∧ delivery.outcome = .conflict stale delivery.settlement.decided := by
  obtain ⟨guard, member, differs⟩ := moved
  have positive : 0 < staleCount snapshot delivery.record.reads := by
    unfold staleCount
    apply List.length_pos_of_mem (a := guard)
    simp [member, differs]
  refine ⟨_, positive, ?_⟩
  rw [delivery.outcomeExact]
  simp [revalidate, Nat.pos_iff_ne_zero.mp positive]

/-- Current reads deliver the settled outcome itself. -/
theorem current_reads_exact {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (current : ∀ guard ∈ delivery.record.reads, snapshot.model.roots guard.cellId = guard.expectedRoot) :
    delivery.outcome = delivery.settlement.decided := by
  have zero : staleCount snapshot delivery.record.reads = 0 := by
    unfold staleCount
    simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, bne_iff_ne, ne_eq, Decidable.not_not]
    exact current
  rw [delivery.outcomeExact, zero]
  rfl

/-- **The resume binds the stored checkpoint.** The machine state a delivery
resumes is decoded from the record cell's own checkpoint bytes, whose digest
the record and the await id name; the response is the typed outcome; nothing
of the state comes from the request. -/
theorem resume_binds_checkpoint {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    ∃ record state,
      readRecord snapshot request.record = some record ∧
      record.phase = .awaiting delivery.await ∧
      delivery.await.id = awaitId request.record record.generation (checkpointDigest record.checkpoint) ∧
      decodeCheckpoint record.checkpoint = some state ∧
      resume delivery.outcome.data.term state = some delivery.resumed ∧
      runSegment config delivery.envelope delivery.resumed = .ok delivery.segment := by
  refine ⟨delivery.record, delivery.state, delivery.recordExact, delivery.awaiting, ?_, delivery.stateExact,
    delivery.resumeExact, delivery.segmentExact⟩
  rw [delivery.digestExact]; exact delivery.idExact

/-- **Resume determinism.** Two deliveries of the same record at the same
snapshot and height resume the same machine state with the same response and,
given the same envelope, end their segments identically. -/
theorem resume_deterministic {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {first second : DeliverRequest} (one : Delivery config snapshot height first)
    (two : Delivery config snapshot height second) (sameRecord : first.record = second.record)
    (sameEnvelope : first.extraTicks = second.extraTicks) :
    one.resumed = two.resumed ∧ one.segment = two.segment ∧ one.next = two.next := by
  have records : one.record = two.record := by
    have := one.recordExact; rw [sameRecord, two.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : one.await = two.await := by
    have a := one.awaiting; have b := two.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : one.settlement = two.settlement := by
    have a := one.settled; have b := two.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  have outcomes : one.outcome = two.outcome := by
    rw [one.outcomeExact, two.outcomeExact, records, settlements]
  have states : one.state = two.state := by
    have a := one.stateExact; rw [records, two.stateExact] at a; exact (Option.some.inj a).symm
  have resumedEq : one.resumed = two.resumed := by
    have a := one.resumeExact; rw [outcomes, states, two.resumeExact] at a; exact (Option.some.inj a).symm
  have envelopes : one.envelope = two.envelope := by
    rw [one.envelopeExact, two.envelopeExact, records, settlements, sameEnvelope]
  have segments : one.segment = two.segment := by
    have a := one.segmentExact; rw [envelopes, resumedEq, two.segmentExact] at a
    exact (Except.ok.inj a).symm
  have yieldeds : one.yielded = two.yielded := by
    have a := one.yieldedExact
    rw [awaits, sameRecord, records, segments, two.yieldedExact] at a
    exact (Except.ok.inj a).symm
  refine ⟨resumedEq, segments, ?_⟩
  rw [one.nextExact, two.nextExact, records, segments, yieldeds]

/-- **No fee depends on computation.** The fee the ending turn takes from the
purse is the used half of the escrowed pair, chosen by how the await ended
(settled from the snapshot and height) and nothing else: two deliveries of the
same record at the same snapshot and height take the same amount, whatever
envelopes they declared and whatever their runs did, and the submitter's added
envelope is the public price of what it DECLARED. -/
theorem refund_measurement_free {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {first second : DeliverRequest} (one : Delivery config snapshot height first)
    (two : Delivery config snapshot height second) (sameRecord : first.record = second.record) :
    (deliveryCharges config one.record first.record one.settlement.path first).operations.head? =
        some (Operation.fee (heldAccount first.record) config.collector config.asset
          (one.record.escrow.used one.settlement.path)) ∧
      one.record.escrow.used one.settlement.path = two.record.escrow.used two.settlement.path ∧
      one.record.escrow.unused one.settlement.path = two.record.escrow.unused two.settlement.path := by
  have records : one.record = two.record := by
    have := one.recordExact; rw [sameRecord, two.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : one.await = two.await := by
    have a := one.awaiting; have b := two.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : one.settlement = two.settlement := by
    have a := one.settled; have b := two.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  exact ⟨rfl, by rw [records, settlements], by rw [records, settlements]⟩

/-- The submitter's charge for added envelope is the public price of what it
DECLARED, never of what ran. -/
theorem submitter_charge_declared (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : DeliverRequest) (extra : 0 < request.extraTicks) :
    Operation.fee request.account config.collector config.asset (config.tariff.price request.extraTicks) ∈
      (deliveryCharges config record cell path request).operations := by
  simp [deliveryCharges, Nat.pos_iff_ne_zero.mp extra]

/-- A yield never leaves its purse short: the postings a yielding segment
commits leave at least the await's fee pair in the purse. -/
theorem yield_reserves_pair (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (before batch : Batch) (state : State) (plan : PlanAwait)
    (settled : settlePurse config book held escrow before (.yielded state plan) = .ok batch) :
    batch = before ∧ escrow.pair ≤ purse (before.apply book) config.asset held := by
  unfold settlePurse at settled
  simp only [Segment.yields] at settled
  by_cases enough : escrow.pair ≤ purse (before.apply book) config.asset held
  · simp [enough] at settled
    exact ⟨settled.symm, enough⟩
  · simp [enough] at settled

/-- An ending segment returns the whole purse to the payer's account. -/
theorem end_returns_purse (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (before batch : Batch) (result : Data)
    (settled : settlePurse config book held escrow before (.finished result) = .ok batch)
    (nonempty : purse (before.apply book) config.asset held ≠ 0) :
    batch.operations = before.operations ++
      [Operation.transfer held escrow.account config.asset (purse (before.apply book) config.asset held)] := by
  unfold settlePurse at settled
  simp only [Segment.yields] at settled
  simp [nonempty] at settled
  subst settled
  rfl

#assert_axioms record_roundTrip
#assert_axioms TypedData.typed
#assert_axioms Postings.conserves
#assert_axioms Birth.conserves
#assert_axioms Delivery.conserves
#assert_axioms TopUp.conserves
#assert_axioms execute_accepted_install
#assert_axioms spent_claim_never_accepted
#assert_axioms installed_retry_replays
#assert_axioms Delivery.spends
#assert_axioms resume_consumes_once
#assert_axioms second_delivery_refused
#assert_axioms slot_decided_once
#assert_axioms slot_single_decider
#assert_axioms stale_reads_conflict
#assert_axioms current_reads_exact
#assert_axioms resume_binds_checkpoint
#assert_axioms resume_deterministic
#assert_axioms refund_measurement_free
#assert_axioms submitter_charge_declared
#assert_axioms yield_reserves_pair
#assert_axioms end_returns_purse
end Minidregg.Kernel.ObjectiveActivity
