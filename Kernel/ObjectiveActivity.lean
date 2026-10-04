/- The kernel activity: a Core4 activity persisted between turns, its awaits,
the resume contract, and its fees on the Book.

An activity of an object is a cell of the deployment's activity role
(`Kernel.ObjectiveActivityCell`) at its protected coordinate
(`recordCell domain object activity`), holding its `Record`: the exact machine
checkpoint (the bytes of `ObjectiveBendCheckpoint.encodeState`, never a
summary), the checkpoint's digest, the pinned package identity, the generation,
the escrow terms, and its phase.
While awaiting, the phase names one `Await`: its id `H(record cell, generation,
checkpoint digest)`, its source (an answer slot with one decider, or a height),
and a mandatory deadline height. The object is a native resource (`object`, a
cell id the authority layer issues capabilities on); its declared state lives in
its own protected state cell (`stateCell domain object`) as an `ObjectState`:
the value and a write version, which every committed write advances by one.

Six kernel turns; each is ONE `DataIntent` built by `intentOf` with the sealing of
the receiver that admitted it (`ObjectiveActivityReceiver`: the signed marker,
the authority guards, the replay event), so its writes commit all together or
not at all (`DurableDataIntent.execute_no_partial_data_commit`):

* `publish`: the package (a checked `ObjectiveBendSourceArtifact`) into its
  content-addressed package cell.
* `birth`: instantiate the pinned definition with typed input, run to the
  first yield, commit the record, the declared-state write, the answer slot it
  awaits and the Book postings, all at once. The first segment has seen no
  state, so its write may `set` a field only when it creates the state cell
  (`blindWrite`); a first yield on an object with no state must create it.
* `resolve`: the slot's one decider decides it (typed against the awaiting
  activity's own response type) at or before the deadline; spends the slot claim.
* `deliver`: anyone resumes the activity with the typed outcome of its await.
  The await id is spent as a nullifier bound to the checkpoint digest, AND the
  record cell is written against its current root: consume-once is a
  compare-and-swap at admission's decide point. RESUME WITH VIEW: the activity
  is resumed with `resumed {outcome, view}`, the outcome its await settled to
  (never replaced, never dropped) and a view of the object's declared state and
  its version read IN THE SAME TURN; the Plan then names a write (per field:
  keep, set or add) that the kernel applies to that view, against the root the
  view was read from. So no write is ever computed from a stale read: a
  delivery prepared on one snapshot is refused on any snapshot where the state
  moved (`moved_state_refuses`), and a fresh delivery sees the move. Past the
  deadline an open slot expires in the same turn and the activity receives
  `timedOut`. The checkpoint is decoded from the record cell (no state is ever
  accepted from a request), resumed with the typed response, run to its next
  yield or end, and the new checkpoint, the Plan's write, the next await and
  the Book postings commit together.
* `topUp`: anyone funds an activity's purse on the Book.
* `writeState`: a holder of the object writes its declared state directly
  (a new version; the next delivery's view shows it).
* `create`: a holder of the object resource installs its `ObjectRecord`
  (`Kernel.ObjectRecord`: pin, law, upgrade policy, payer) at its own protected
  coordinate (`objectCell`).

Objects. A cell is an object to the kernel exactly when it has a record. A
birth on any other cell is refused by name (`birth_refuses_non_object`), and a
birth runs only the package the object pins (`birth_refuses_other_pin`). Every
declared-state write (a birth's or a delivery's yield, a direct write) is judged
by the object's law over the old and new state plus the request facts
(`ObjectRecord.admitWrite`), with the record read in the same turn and its cell
guarded. A delivery's write is judged with the activity's principal (its birth
subject) as subject, never the deliverer. A law refusal refuses the whole turn
and names the clause: nothing commits, and the activity stays at its yield
(`Birth.write_judged`, `Delivery.write_judged`, `StateWrite.write_judged`).

Fees are Book postings in the deployment's credit asset. An activity's purse is
a Book account of its own, `heldAccount cell` (the record cell's id), registered
by the birth. Every turn that runs Core4 pays the public price of its DECLARED
envelope (`ObjectiveTariff.Tariff.workOf`, the native tariff) to the collector. A yield reserves, in the purse, the
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
import Kernel.ObjectState
import Kernel.ObjectRecord
import Kernel.ObjectiveTariff

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
open Minidregg.Kernel.ObjectState (encodeObjectState decodeObjectState)
open Minidregg.Kernel.ObjectRecord (ObjectRecord Facts WriteRefusal admitWrite)
open Minidregg.Kernel.ObjectiveTariff (Tariff zeroCapacity addCapacity)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
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
  /-- The declared envelopes of the turn that resumes the await and of the turn
  that times it out. -/
  resume : Capacity
  timeout : Capacity
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
  escrow : Escrow
  /-- The largest envelope an exhausted attempt at the current await already
  ran under (0: none). A run that exhausts an envelope exhausts every smaller
  one, so an attempt at or below it is refused before it runs, and an
  exhaustion must strictly raise it: no attempt is ever run or paid twice. -/
  tried : Nat
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
      (StreamCodec.product capacityStream (StreamCodec.product capacityStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
    (fun e => (e.payer, e.account, e.resume, e.timeout, e.resumeFee, e.timeoutFee))
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
      (StreamCodec.product digestStream
      (StreamCodec.product escrowStream (StreamCodec.product StreamCodec.nat phaseStream)))))))))
    (fun r => (r.object, r.activity, r.pin, r.input, r.generation, r.checkpoint, r.checkpointDigest,
      r.escrow, r.tried, r.phase))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2.1,
      w.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

/-- v5: the escrow holds declared envelopes (`Capacity`), not tick counts; v4: the record carries `tried` (the envelope its exhausted attempts at the
current await reached); v3: no recorded reads (resume with view reads the state
in the resuming turn); v2: the escrow names the payer's Book account. -/
def recordFrame : Bytes := "DREGG/OBJECTIVE/ACTIVITY-RECORD/v5".toUTF8.toList
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

def objectKey (object : CellId) : Bytes := digestStream.encode object

/-- The object's record (`Kernel.ObjectRecord`): one cell per object, at its
protected coordinate. A cell without one is not an object to the kernel. -/
def objectCell (domain : Digest) (object : CellId) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .object (objectKey object)⟩

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
  /-- Heights past an await's deadline after which anyone may abandon it. -/
  abandonGrace : Nat

/-- A declared envelope covers what the kernel spends on a turn: its source
ticks are within the ceiling, and it declares at least the kernel's fixed heap,
stack, type-checking fuel and Plan extraction budget, so the whole turn's work
(the run, the per-turn package check, the extraction) is in the price. -/
def Config.covers (config : Config) (envelope : Capacity) : Bool :=
  decide (envelope.sourceTicks ≤ config.maxTicks) && decide (config.limits.heap ≤ envelope.heap) &&
    decide (config.limits.stack ≤ envelope.stack) && decide (config.typeFuel ≤ envelope.typeFuel) &&
    decide (config.planBudget.nodes ≤ envelope.outputNodes) && decide (config.planBudget.bytes ≤ envelope.outputBytes)

def Config.domain (config : Config) : Digest := config.deployment.domain
def Config.bookCell (config : Config) : CellId := ⟨config.deployment.resourceBookId⟩

/-- The escrow terms for an activity. -/
def escrowOf (tariff : Tariff) (payer : SubjectId) (account : AccountId) (resume timeout : Capacity) :
    Escrow :=
  ⟨payer, account, resume, timeout, tariff.workOf resume, tariff.workOf timeout⟩

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
def Escrow.capacity (escrow : Escrow) : Path → Capacity
  | .resumed => escrow.resume
  | .timedOut => escrow.timeout

/-! ## Refusals -/

inductive Refusal where
  | packageMissing | packageIdentity | packageType (reason : String) | packageExists
  | inputType | outcomeProtocol (label : String)
  | recordExists | recordMissing | recordMisplaced | notAwaiting | awaitMismatch | checkpointDigest | checkpointCodec
  | patience (patience maximum : Nat)
  /-- A declared envelope does not cover the turn (`Config.covers`). -/
  | uncovered (envelope : Capacity)
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
  /-- A write that `set`s a field of state the activity has not seen (a birth
  on an object whose state exists): only `keep` and `add` are admitted. -/
  | blindWrite
  /-- The Plan's write does not fit the declared state (an unknown field, a
  repeated field, `add` on a non-natural, a creation that does not set every
  field, or a first yield that does not create absent state). -/
  | writeShape (reason : String)
  /-- The object's state cell holds bytes that are not an `ObjectState`. -/
  | stateCodec
  /-- A delivery found no declared state to show the activity. -/
  | stateMissing
  /-- An attempt at an envelope no larger than one that already exhausted:
  refused before it runs (it would exhaust again). -/
  | alreadyExhausted (tried envelope : Nat)
  /-- The await is not yet abandonable: abandonment needs a height past its
  deadline plus the deployment's grace. -/
  | notYetAbandonable (deadline grace height : Nat)
  /-- An exhaustion was submitted for a run that does not exhaust: deliver it. -/
  | notExhausted
  /-- The cell has no object record: it is not an object to the kernel. -/
  | notAnObject
  /-- The object's record cell holds bytes that are not an `ObjectRecord`. -/
  | objectCodec
  /-- The object already has a record. -/
  | objectExists
  /-- A birth names a package other than the one the object pins. -/
  | pinMismatch (pinned requested : Digest)
  /-- The object's law refuses the declared-state write (`ObjectRecord.admitWrite`). -/
  | objectWrite (reason : WriteRefusal)
  /-- A creation pins a package that is not published. -/
  | pinUnpublished
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

/-- Every await resolves to exactly one of these. The outcome is delivered
exactly as the await settled it, never replaced and never dropped; staleness is
not an outcome (resume with view, ROOT ruling 10-05). -/
inductive AwaitOutcome where
  | reply (value : Data)
  | refused
  | unknown
  | timedOut
  | broken
  | upgraded
  deriving Repr

def AwaitOutcome.label : AwaitOutcome → String
  | .reply _ => "reply" | .refused => "refused" | .unknown => "unknown" | .timedOut => "timedOut"
  | .broken => "broken" | .upgraded => "upgraded"

/-- The outcome datum, the `outcome` field of the response. -/
def AwaitOutcome.data : AwaitOutcome → Data
  | .reply value => .variant "reply" value
  | .refused => .variant "refused" (.record [])
  | .unknown => .variant "unknown" (.record [])
  | .timedOut => .variant "timedOut" (.record [])
  | .broken => .variant "broken" (.record [])
  | .upgraded => .variant "upgraded" (.record [])

/-- The view datum: the object's declared state and its write version. -/
def viewData (view : ObjectState) : Data :=
  .record [("version", .natural view.version), ("state", view.value)]

/-- **The response an activity is resumed with**: the settled outcome together
with the view of the object's declared state read in the resuming turn. -/
def responseData (outcome : AwaitOutcome) (view : ObjectState) : Data :=
  .variant "resumed" (.record [("outcome", outcome.data), ("view", viewData view)])

/-- The kernel's own outcomes, which every activity's outcome type must type at
birth (a reply is typed when it is decided). -/
def kernelOutcomes : List AwaitOutcome := [.refused, .unknown, .timedOut, .broken, .upgraded]

/-- The response type's parts: `resumed {outcome : O, view : V}`. -/
def responseParts (assumptions : Assumptions) (response : Ty) : Option (Ty × Ty) := do
  let .variant row := unalias assumptions.bounds response | none
  let step ← row.lookup assumptions.bounds 64 "resumed"
  let outcome ← (unalias assumptions.bounds step).lookup assumptions.bounds 64 "outcome"
  let view ← (unalias assumptions.bounds step).lookup assumptions.bounds 64 "view"
  pure (outcome, view)

/-- The type a reply must have: the `reply` member of the outcome sum. -/
def replyType (assumptions : Assumptions) (response : Ty) : Option Ty := do
  let (outcome, _) ← responseParts assumptions response
  let .variant row := unalias assumptions.bounds outcome | none
  row.lookup assumptions.bounds 64 "reply"

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
def typeResponse {config : Config} {pin : Digest} {input : Data} (program : Program config pin input)
    (outcome : AwaitOutcome) (view : ObjectState) :
    Except Refusal (TypedData program.assumptions (responseData outcome view) program.responseType) :=
  match typeData program.assumptions config.typeFuel (responseData outcome view) program.responseType with
  | some typed => .ok typed
  | none => .error (.responseType outcome.label)

/-- At birth: the response type is `resumed {outcome, view}` and every kernel
outcome is typed at its outcome type, so no outcome the kernel can deliver is
ill-typed later (an ill-typed delivery would park the activity for ever). -/
def outcomeProtocol {config : Config} {pin : Digest} {input : Data} (program : Program config pin input) :
    Except Refusal Unit := do
  let some (outcomeType, _) := responseParts program.assumptions program.responseType
    | throw (.outcomeProtocol "resumed {outcome, view}")
  for outcome in kernelOutcomes do
    if (typeData program.assumptions config.typeFuel outcome.data outcomeType).isNone then
      throw (.outcomeProtocol outcome.label)

/-- At a birth that yields: the response type types the view of the state the
birth leaves, so the next delivery's view is typed. -/
def viewProtocol {config : Config} {pin : Digest} {input : Data} (program : Program config pin input)
    (view : ObjectState) : Except Refusal Unit :=
  match typeData program.assumptions config.typeFuel (responseData .unknown view) program.responseType with
  | some _ => .ok ()
  | none => .error (.outcomeProtocol "view")

/-! ## Plans the kernel performs -/

inductive PlanSource where
  | reply (decider : SubjectId)
  | height (due : Nat)
  deriving DecidableEq, Repr

/-- A yielded Plan: `await {write, on, patience}`. `write` names, per field of
the object's declared state, an edit (`keep`, `set v` or `add n`) that the kernel
applies to the state the activity was resumed with (`stateWrite`); `on` names
what the activity waits for; the deadline is the yield height plus `patience`. -/
structure PlanAwait where
  write : Data
  source : PlanSource
  patience : Nat

def fieldOf (fields : List (String × Data)) (name : String) : Option Data :=
  (fields.find? (fun field => field.1 == name)).map Prod.snd

def decodePlan : Data → Except Refusal PlanAwait
  | .variant "await" (.record fields) => do
    let some write := fieldOf fields "write" | throw (.plan "await.write missing")
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
    pure ⟨write, source, patience⟩
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

@[simp] theorem guardAt_cellId {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) :
    (guardAt snapshot cell).cellId = cell := rfl

@[simp] theorem guardAt_expectedRoot {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) :
    (guardAt snapshot cell).expectedRoot = snapshot.model.roots cell := rfl

/-- The image of a reclaimed activity cell: the cell stays at its coordinate
(so the coordinate is never reused and the registry law still holds) with an
EMPTY kernel body, which every reader refuses by name before decoding
(`recordOfBody_vacant`, `slotOfBody_vacant`: `recordMissing`, `slotMissing`). It is a fixed-size tombstone; the checkpoint, the input,
the result and every other byte the cell held are gone. -/
def vacant (role : Role) (key : Bytes) : Bytes := image role key []

/-- What a record cell holds: the record while it awaits; nothing once it has
ended (`done`/`faulted`). The end of an activity is its disposal: the turn
that ends it reclaims its record (and `settlePurse` returns its purse); the
result is the turn's own (re-derivable by replaying the retained ingress). -/
def recordBody (record : Record) : Bytes :=
  match record.phase with
  | .awaiting _ => encodeRecord record
  | .done _ | .faulted _ => []

def recordPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (cell : CellId) (record : Record) : Post :=
  postAt snapshot cell (image .record (recordKey record.object record.activity) (recordBody record))

/-- Reclaim a slot cell. -/
def slotVacate {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (name : Digest) : Post :=
  postAt snapshot (AnswerSlot.cell config.domain name) (vacant .slot (AnswerSlot.key name))

def slotPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (slot : AnswerSlot.Slot) : Post :=
  postAt snapshot (AnswerSlot.cell config.domain slot.name) (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))

/-- The image a declared-state write installs: the `ObjectState`. -/
def stateImage (object : CellId) (state : ObjectState) : Bytes :=
  image .state (stateKey object) (encodeObjectState state)

/-- The record a record cell's kernel body holds. A reclaimed (empty) body
holds none, refused by name before any decoding (`recordOfBody_vacant`). -/
def recordOfBody (body : Bytes) : Option Record := if body.isEmpty then none else decodeRecord body

def readRecord {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : Option Record :=
  (bodyOf .record (snapshot.canonicalBytes cell)).bind recordOfBody

/-- The slot a slot cell's kernel body holds; a reclaimed body holds none. -/
def slotOfBody (body : Bytes) : Option AnswerSlot.Slot := if body.isEmpty then none else AnswerSlot.decode body

def readSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (name : Digest) :
    Option AnswerSlot.Slot :=
  (bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name))).bind slotOfBody

/-- The object's declared state as its state cell holds it: `none` when the
object has no state yet, refused when the cell holds anything else. -/
def readState {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId) :
    Except Refusal (Option ObjectState) :=
  let bytes := snapshot.canonicalBytes (stateCell config.domain object)
  match bodyOf .state bytes with
  | some body => match decodeObjectState body with
    | some state => .ok (some state)
    | none => .error .stateCodec
  | none => if (payloadOf bytes).isSome then .error .stateCodec else .ok none

/-- The image an object record installs. -/
def objectImage (object : CellId) (record : ObjectRecord) : Bytes :=
  image .object (objectKey object) (ObjectRecord.encodeRecord record)

/-- The object's record: `none` when the cell has none (not an object), refused
when the cell holds anything else. -/
def readObject {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId) :
    Except Refusal (Option ObjectRecord) :=
  let bytes := snapshot.canonicalBytes (objectCell config.domain object)
  match bodyOf .object bytes with
  | some body => match ObjectRecord.decodeRecord body with
    | some record => .ok (some record)
    | none => .error .objectCodec
  | none => if (payloadOf bytes).isSome then .error .objectCodec else .ok none

/-- The request facts a declared-state write is judged under. `turn`: 1 birth,
2 delivery, 3 direct write. A delivery's write is the activity's, so its subject
is the activity's principal (its birth subject, `escrow.payer`: the subject the
native route checked as a holder of the object), never the deliverer. -/
def factsOf (subject : SubjectId) (height : Nat) (object : CellId) (turn : Nat) : Facts :=
  ⟨subject, height, object.value, turn⟩

/-- The object's law judges a write: nothing to judge when nothing is written. -/
def judgeWrite (record : ObjectRecord) (facts : Facts) (old : Option Data) (new : Data) : Except Refusal Unit :=
  match admitWrite record facts old new with
  | .ok () => .ok ()
  | .error reason => .error (.objectWrite reason)

theorem judgeWrite_ok {record : ObjectRecord} {facts : Facts} {old : Option Data} {new : Data}
    (judged : judgeWrite record facts old new = .ok ()) : admitWrite record facts old new = .ok () := by
  unfold judgeWrite at judged
  split at judged
  · assumption
  · cases judged

/-! ### Writes: fields and deltas, applied to the state the activity saw -/

/-- One field's edit. -/
inductive Edit where
  | keep
  | set (value : Data)
  | add (amount : Nat)
  deriving Repr

def Edit.isKeep : Edit → Bool
  | .keep => true
  | _ => false

def Edit.isSet : Edit → Bool
  | .set _ => true
  | _ => false

def decodeEdit : Data → Except Refusal Edit
  | .variant "keep" _ => .ok .keep
  | .variant "set" value => .ok (.set value)
  | .variant "add" (.natural amount) => .ok (.add amount)
  | _ => .error (.writeShape "an edit is keep, set or add (of a natural)")

/-- A Plan's `write`: a record of field edits, each field named once. -/
def decodeWrite : Data → Except Refusal (List (String × Edit))
  | .record fields =>
    if (fields.map Prod.fst).Nodup then fields.mapM fun field => do pure (field.1, ← decodeEdit field.2)
    else .error (.writeShape "a field is edited twice")
  | _ => .error (.writeShape "a write is a record of field edits")

/-- One field of the state after its edit (absent edit: kept). -/
def editField (edits : List (String × Edit)) (name : String) (value : Data) : Except Refusal Data :=
  match (edits.find? (fun edit => edit.1 == name)).map Prod.snd with
  | none => .ok value
  | some .keep => .ok value
  | some (.set replacement) => .ok replacement
  | some (.add amount) => match value with
    | .natural current => .ok (.natural (current + amount))
    | _ => .error (.writeShape s!"add on the non-natural field {name}")

/-- The field-wise edit of present record state, in the state's field order. -/
def editFields (edits : List (String × Edit)) : List (String × Data) → Except Refusal (List (String × Data))
  | [] => .ok []
  | field :: rest =>
    match editField edits field.1 field.2 with
    | .error reason => .error reason
    | .ok value =>
      match editFields edits rest with
      | .error reason => .error reason
      | .ok edited => .ok ((field.1, value) :: edited)

/-- **The write applied to a state.** `none`: nothing to write (every edit
`keep`). Creating absent state needs a `set` of every field it names; editing
present state needs every edited field to exist; the result keeps the state's
field order. Pure and a function of the write and the state alone. -/
def applyWrite (edits : List (String × Edit)) (current : Option Data) : Except Refusal (Option Data) :=
  if edits.all (fun edit => edit.2.isKeep) then .ok none else
  match current with
  | none =>
    (edits.mapM fun (edit : String × Edit) => (match edit.2 with
      | .set value => .ok (edit.1, value)
      | _ => .error (.writeShape s!"creating the state must set {edit.1}") : Except Refusal (String × Data))).map
      fun fields => some (.record fields)
  | some (.record fields) =>
    if edits.all (fun edit => fields.any (fun field => field.1 == edit.1)) then
      (editFields edits fields).map fun edited => some (.record edited)
    else .error (.writeShape "an edit names no field of the declared state")
  | some _ => .error (.writeShape "the declared state is not a record")

/-- What a state write commits: the state it was computed from, the state it
installs (the next version), and the post. -/
structure StateWritten where
  before : Option ObjectState
  after : ObjectState
  post : Post

/-- The object's law judges a built write (`stateWrite`'s `before`, `after`);
nothing is judged when nothing is written. -/
def judgeWritten (record : ObjectRecord) (facts : Facts) : Option StateWritten → Except Refusal Unit
  | none => .ok ()
  | some written => judgeWrite record facts (written.before.map ObjectState.value) written.after.value

theorem judgeWritten_ok {record : ObjectRecord} {facts : Facts} {built : Option StateWritten}
    (judged : judgeWritten record facts built = .ok ()) (written : StateWritten) (is : built = some written) :
    admitWrite record facts (written.before.map ObjectState.value) written.after.value = .ok () := by
  subst is; exact judgeWrite_ok judged

/-- **The one point where a declared-state write is built** (the hook the
object's law and facet check wrap: `before`, `after`). `current` is the state
the writer SAW in this turn; `viewed` says whether the activity was shown it
(a delivery) or not (a birth's first segment, which may only `keep`/`add` on
present state). The post installs version `current + 1` against the root
`current` was read from, so a write is never computed from a stale read. -/
def stateWrite {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (object : CellId) (current : Option ObjectState) (viewed : Bool) (write : Data) :
    Except Refusal (Option StateWritten) := do
  let edits ← decodeWrite write
  if !viewed && current.isSome && edits.any (fun edit => edit.2.isSet) then throw .blindWrite
  match ← applyWrite edits (current.map ObjectState.value) with
  | none =>
    if current.isNone then throw (.writeShape "the first yield must create the declared state")
    pure none
  | some value =>
    let after : ObjectState := ⟨(current.map ObjectState.version).getD 0 + 1, value⟩
    pure (some ⟨current, after, postAt snapshot (stateCell config.domain object) (stateImage object after)⟩)

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

/-- What a yield commits besides the record: the declared-state write (if the
Plan writes), the answer slot it opens, and the await. -/
structure YieldCommit where
  await : Await
  written : Option StateWritten
  posts : List Post

def commitYield {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell : CellId) (object : CellId) (generation : Nat)
    (checkpoint : Digest) (current : Option ObjectState) (viewed : Bool) (plan : PlanAwait) :
    Except Refusal YieldCommit :=
  if plan.patience = 0 ∨ config.maxPatience < plan.patience then
    .error (.patience plan.patience config.maxPatience) else
  match stateWrite config snapshot object current viewed plan.write with
  | .error reason => .error reason
  | .ok written =>
  match plan.source with
  | .reply decider =>
    if (readSlot config snapshot (AnswerSlot.name transaction cell generation)).isSome then .error .slotFresh else
    .ok ⟨⟨awaitId cell generation checkpoint, .reply (AnswerSlot.name transaction cell generation) decider,
        height + plan.patience, height⟩, written,
      (written.map StateWritten.post).toList ++ [slotPost config snapshot
        ⟨AnswerSlot.name transaction cell generation, cell, decider, height + plan.patience, .opened⟩]⟩
  | .height due =>
    if height + plan.patience < due then .error (.plan "a height await is due after its deadline") else
    .ok ⟨⟨awaitId cell generation checkpoint, .height due, height + plan.patience, height⟩, written,
      (written.map StateWritten.post).toList⟩

/-- The record that ends a segment. -/
def nextRecord (base : Record) (generation : Nat) : Segment → Option YieldCommit → Record
  | .yielded state _, some yielded =>
    let encoded := checkpointBytes state
    { base with
      generation := generation
      checkpoint := encoded
      checkpointDigest := ObjectiveActivityWire.checkpointDigest encoded
      tried := 0
      phase := .awaiting yielded.await }
  | .finished result, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      phase := .done (dataBytes result) }
  | .faulted reason, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      phase := .faulted reason }
  | .yielded _ _, none =>
    { base with generation := generation, phase := .faulted "internal: yield without commit" }

/-- The yield commit of a segment, when it yielded. -/
def segmentCommit {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell object : CellId) (generation : Nat)
    (current : Option ObjectState) (viewed : Bool) : Segment → Except Refusal (Option YieldCommit)
  | .yielded state plan => do
    let committed ← commitYield config snapshot height transaction cell object generation
      (checkpointDigest (checkpointBytes state)) current viewed plan
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
  /-- The declared envelope of the birth turn. -/
  envelope : Capacity
  /-- The declared envelopes each await escrows for its resume and its timeout. -/
  resume : Capacity
  timeout : Capacity
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
    ⟨[], [.fee request.account config.collector config.asset (config.tariff.workOf request.envelope)] ++
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
  /-- The object's declared state as the birth found it (the first segment is
  not shown it: its write may not `set` present state). -/
  current : Option ObjectState
  currentExact : readState config snapshot request.object = .ok current
  segment : Segment
  segmentExact : runSegment config request.envelope.sourceTicks (initial program.applied.erase) = .ok segment
  yielded : Option YieldCommit
  yieldedExact : segmentCommit config snapshot height (birthTransaction request) cell request.object 0
    current false segment = .ok yielded
  record : Record
  recordExact : record = nextRecord
    ⟨request.object, activityId request.object (birthTransaction request), request.pin, dataBytes request.input,
      0, [], checkpointDigest [],
      escrowOf config.tariff request.subject request.account request.resume request.timeout,
      0, .faulted "unborn"⟩ 0 segment yielded
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  posts : List Post
  recordFirst : posts.head? = some (recordPost config snapshot cell record)
  postsExact : posts = recordPost config snapshot cell record ::
    ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
  guards : List ReadGuard
  guardsExact : guards = [guardAt snapshot (objectCell config.domain request.object),
    guardAt snapshot (packageCell config.domain request.pin),
    guardAt snapshot (stateCell config.domain request.object)]
  /-- The object's record: the birth is on an object, and runs the package it pins. -/
  object : ObjectRecord
  objectExact : readObject config snapshot request.object = .ok (some object)
  pinned : object.pin = request.pin
  /-- The object's law admitted the first segment's write (if it wrote). -/
  judged : judgeWritten object (factsOf request.subject height request.object 1)
    (yielded.bind YieldCommit.written) = .ok ()

def birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) : Except Refusal (Birth config snapshot height request) := do
  match objectExact : readObject config snapshot request.object with
  | .error reason => throw reason
  | .ok none => throw .notAnObject
  | .ok (some object) =>
    if pinned : object.pin = request.pin then
      if !config.covers request.envelope then throw (.uncovered request.envelope)
      if !config.covers request.resume then throw (.uncovered request.resume)
      if !config.covers request.timeout then throw (.uncovered request.timeout)
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
          match currentExact : readState config snapshot request.object with
          | .error reason => throw reason
          | .ok current =>
          match segmentExact : runSegment config request.envelope.sourceTicks (initial program.applied.erase) with
          | .error reason => throw reason
          | .ok segment =>
            match yieldedExact : segmentCommit config snapshot height transaction cell request.object 0
                current false segment with
            | .error reason => throw reason
            | .ok yielded =>
              match judged : judgeWritten object (factsOf request.subject height request.object 1)
                  (yielded.bind YieldCommit.written) with
              | .error reason => throw reason
              | .ok () =>
                match yielded with
                | some committed =>
                  match (committed.written.map StateWritten.after).orElse (fun _ => current) with
                  | some view => viewProtocol program view
                  | none => throw .stateMissing
                | none => pure ()
                let escrow := escrowOf config.tariff request.subject request.account request.resume request.timeout
                if segment.yields ∧ request.deposit < escrow.pair then
                  throw (.underfunded request.deposit escrow.pair)
                let batch ← birthBatch config (logicalBook book.logical) held request escrow segment
                let posted ← postings book batch
                let base : Record := ⟨request.object, activity, request.pin, dataBytes request.input, 0, [],
                  checkpointDigest [], escrow, 0, .faulted "unborn"⟩
                let record := nextRecord base 0 segment yielded
                let posts := recordPost config snapshot cell record ::
                  ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot])
                pure ⟨program, programExact, cell, rfl, current, currentExact, segment, segmentExact, yielded, yieldedExact,
                  record, rfl, book, bookExact, posted, posts, rfl, rfl,
                  [guardAt snapshot (objectCell config.domain request.object),
                    guardAt snapshot (packageCell config.domain request.pin),
                    guardAt snapshot (stateCell config.domain request.object)], rfl,
                  object, objectExact, pinned, judged⟩
    else throw (.pinMismatch object.pin request.pin)

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
        pure ⟨if decision = .expired then .timedOut else .resumed, outcome,
          [slotVacate config snapshot slotName], [], []⟩
      | .opened =>
        match AnswerSlot.expire slot height with
        | .ok _ => .ok ⟨.timedOut, .timedOut, [slotVacate config snapshot slotName], [],
            [AnswerSlot.decisionClaim slotName]⟩
        | .error _ => .error (.notYetDecided await.deadline height)
  | .height due =>
    if await.deadline < height then .ok ⟨.timedOut, .timedOut, [], [], []⟩
    else if due ≤ height then .ok ⟨.resumed, .reply (.record [("at", .natural height)]), [], [], []⟩
    else .error (.notYetDue due height)

/-- No state, no checkpoint and no outcome is ever taken from a request: the
submitter names the record and may add envelope it pays for from `account`. -/
structure DeliverRequest where
  subject : SubjectId
  record : CellId
  /-- Envelope the submitter adds (and pays for) on top of the escrowed one. -/
  extra : Capacity
  account : AccountId

/-- The ending turn's own postings: the used fee from the purse, and the
submitter's added envelope from its account, both to the collector. -/
def deliveryCharges (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : DeliverRequest) : Batch :=
  ⟨[], [.fee (heldAccount cell) config.collector config.asset (record.escrow.used path)] ++
    (if request.extra = zeroCapacity then []
     else [.fee request.account config.collector config.asset (config.tariff.workOf request.extra)])⟩

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
  /-- The object's declared state and its version, read in THIS turn. -/
  view : ObjectState
  viewExact : readState config snapshot record.object = .ok (some view)
  response : TypedData program.assumptions (responseData settlement.decided view) program.responseType
  state : State
  stateExact : decodeCheckpoint record.checkpoint = some state
  resumed : State
  resumeExact : resume (responseData settlement.decided view).term state = some resumed
  envelope : Capacity
  envelopeExact : envelope = addCapacity (record.escrow.capacity settlement.path) request.extra
  segment : Segment
  segmentExact : runSegment config envelope.sourceTicks resumed = .ok segment
  yielded : Option YieldCommit
  yieldedExact : segmentCommit config snapshot height (deliveryTransaction await.id) request.record record.object
    (record.generation + 1) (some view) true segment = .ok yielded
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
  guardsExact : guards = guardAt snapshot (objectCell config.domain record.object) ::
    guardAt snapshot (packageCell config.domain record.pin) ::
    guardAt snapshot (stateCell config.domain record.object) :: settlement.guards
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: settlement.claims
  /-- The object's record, read in this turn. -/
  object : ObjectRecord
  objectExact : readObject config snapshot record.object = .ok (some object)
  /-- The object's law admitted the segment's write (if it wrote), judged with
  the activity's principal as subject. -/
  judged : judgeWritten object (factsOf record.escrow.payer height record.object 2)
    (yielded.bind YieldCommit.written) = .ok ()

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
  match objectExact : readObject config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some object) =>
  match settled : settle config snapshot height request.record await with
  | .error reason => .error reason
  | .ok settlement =>
  match viewExact : readState config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .stateMissing
  | .ok (some view) =>
  match typeResponse program settlement.decided view with
  | .error reason => .error reason
  | .ok response =>
  match stateExact : decodeCheckpoint record.checkpoint with
  | none => .error .checkpointCodec
  | some state =>
  match resumeExact : resume (responseData settlement.decided view).term state with
  | none => .error .checkpointCodec
  | some resumed =>
  let envelope := addCapacity (record.escrow.capacity settlement.path) request.extra
  if !config.covers envelope then .error (.uncovered envelope) else
  if 0 < record.tried ∧ envelope.sourceTicks ≤ record.tried then .error (.alreadyExhausted record.tried envelope.sourceTicks) else
  match segmentExact : runSegment config envelope.sourceTicks resumed with
  | .error reason => .error reason
  | .ok segment =>
  let transaction := deliveryTransaction await.id
  match yieldedExact : segmentCommit config snapshot height transaction request.record record.object
      (record.generation + 1) (some view) true segment with
  | .error reason => .error reason
  | .ok yielded =>
  match judged : judgeWritten object (factsOf record.escrow.payer height record.object 2)
      (yielded.bind YieldCommit.written) with
  | .error reason => .error reason
  | .ok () =>
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
  let guards := guardAt snapshot (objectCell config.domain record.object) ::
    guardAt snapshot (packageCell config.domain record.pin) ::
    guardAt snapshot (stateCell config.domain record.object) :: settlement.guards
  .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program, programExact,
    settlement, settled, view, viewExact, response, state, stateExact, resumed, resumeExact, envelope, rfl,
    segment, segmentExact, yielded, yieldedExact, next, rfl, book, bookExact, batch, batchExact, posted,
    postedBatch, posts, rfl, rfl, guards, rfl, awaitClaim await.id :: settlement.claims, rfl,
    object, objectExact, judged⟩
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

/-! ### exhaust

An attempt to end an await whose run runs out of its declared envelope. It is
a committed, paid turn, never a free refusal: KeyKOS decremented the meter as
a domain ran, every gas system charges an exhausted envelope, and an attempt
that cost nothing could be repeated at the Host's expense. It is admitted ONLY
when the delivery's own run (the stored checkpoint resumed with the settled,
typed outcome under the declared envelope) exhausts; otherwise the submitter
must deliver. It charges DECLARED amounts only: the purse pays the declared
envelope of the ending path the first time this await exhausts (`tried = 0`),
the submitter pays the public price of the envelope it added. It ends nothing:
the await, the checkpoint, the generation and the slot are unchanged, and
`tried` rises to the envelope it ran under, so the next attempt at this await
must run under a strictly larger envelope (`deliver` and `exhaust` both refuse
one at or below `tried` before running): no attempt is ever run or paid twice. -/

structure ExhaustRequest where
  subject : SubjectId
  record : CellId
  /-- Envelope the submitter adds (and pays for) on top of the escrowed one. -/
  extra : Capacity
  account : AccountId
  nonce : Nat

/-- Distinct attempts are distinct transactions (the submitter and its nonce);
an exact retry replays. -/
def exhaustTransaction (await : Digest) (request : ExhaustRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/EXHAUST/v1"
    (digestStream.encode await ++ subjectStream.encode request.subject ++ StreamCodec.nat.encode request.nonce)

/-- The declared charge of an exhausted attempt. -/
def exhaustCharge (config : Config) (record : Record) (path : Path) (request : ExhaustRequest) : Nat :=
  (if record.tried = 0 then record.escrow.used path else 0) +
    (if request.extra = zeroCapacity then 0 else config.tariff.workOf request.extra)

/-- Its postings: the purse's part, then the submitter's, both to the collector. -/
def exhaustCharges (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : ExhaustRequest) : Batch :=
  ⟨[], (if record.tried = 0 then [.fee (heldAccount cell) config.collector config.asset (record.escrow.used path)]
        else []) ++
    (if request.extra = zeroCapacity then []
     else [.fee request.account config.collector config.asset (config.tariff.workOf request.extra)])⟩

/-- Guard every cell a settlement would write, at the root the attempt read:
an exhaustion is decided against exactly the slot state its run saw. -/
def settlementGuards (settlement : Settlement) : List ReadGuard :=
  settlement.guards ++ settlement.posts.map (fun post => ⟨post.cell, post.pre⟩)

structure Exhaustion {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ExhaustRequest) where
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
  /-- The object's declared state and its version, read in THIS turn (as a
  delivery reads it: the run is the delivery's run). -/
  view : ObjectState
  viewExact : readState config snapshot record.object = .ok (some view)
  response : TypedData program.assumptions (responseData settlement.decided view) program.responseType
  state : State
  stateExact : decodeCheckpoint record.checkpoint = some state
  resumed : State
  resumeExact : resume (responseData settlement.decided view).term state = some resumed
  envelope : Capacity
  envelopeExact : envelope = addCapacity (record.escrow.capacity settlement.path) request.extra
  raises : record.tried < envelope.sourceTicks
  ran : runSegment config envelope.sourceTicks resumed = .error .exhausted
  next : Record
  nextExact : next = { record with tried := envelope.sourceTicks }
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = exhaustCharges config record request.record settlement.path request
  posts : List Post
  postsExact : posts = [recordPost config snapshot request.record next, posted.write config snapshot]
  guards : List ReadGuard
  guardsExact : guards = guardAt snapshot (packageCell config.domain record.pin) ::
    guardAt snapshot (stateCell config.domain record.object) :: settlementGuards settlement

def exhaust {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ExhaustRequest) : Except Refusal (Exhaustion config snapshot height request) :=
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
  match viewExact : readState config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .stateMissing
  | .ok (some view) =>
  match typeResponse program settlement.decided view with
  | .error reason => .error reason
  | .ok response =>
  match stateExact : decodeCheckpoint record.checkpoint with
  | none => .error .checkpointCodec
  | some state =>
  match resumeExact : resume (responseData settlement.decided view).term state with
  | none => .error .checkpointCodec
  | some resumed =>
  let envelope := addCapacity (record.escrow.capacity settlement.path) request.extra
  if !config.covers envelope then .error (.uncovered envelope) else
  if raises : record.tried < envelope.sourceTicks then
  -- The charge must be payable BEFORE the run: an unpayable attempt never runs.
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postings book (exhaustCharges config record request.record settlement.path request) with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = exhaustCharges config record request.record settlement.path request then
  match ran : runSegment config envelope.sourceTicks resumed with
  | .ok _ => .error .notExhausted
  | .error .exhausted =>
    let next := { record with tried := envelope.sourceTicks }
    let posts := [recordPost config snapshot request.record next, posted.write config snapshot]
    let guards := guardAt snapshot (packageCell config.domain record.pin) ::
      guardAt snapshot (stateCell config.domain record.object) :: settlementGuards settlement
    .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program,
      programExact, settlement, settled, view, viewExact, response, state, stateExact, resumed, resumeExact,
      envelope, rfl, raises, ran, next, rfl, book, bookExact, posted, postedBatch, posts, rfl, guards, rfl⟩
  | .error reason => .error reason
  else .error .bookRefused
  else .error (.alreadyExhausted record.tried envelope.sourceTicks)
  else .error .checkpointDigest
  else .error .awaitMismatch
  else .error .recordMisplaced

/-- An exhaustion spends no claim: the await stays open. -/
def Exhaustion.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (ex : Exhaustion config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (exhaustTransaction ex.await.id request) ex.posts ex.guards [] sealing

/-- **An exhaustion conserves every asset.** -/
theorem Exhaustion.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (ex : Exhaustion config snapshot height request) (asset : AssetId) :
    (logicalBook ex.posted.post.logical).totalAsset asset = (logicalBook ex.book.logical).totalAsset asset :=
  ex.posted.conserves asset

/-! ### abandon

An await nobody ended — its decider never decided, its timeout was never
delivered, or every attempt exhausted and nobody funded the next — may be
abandoned by anyone once the height passes its deadline plus the deployment's
grace. Abandonment is the disposal of an activity that cannot end itself
(KeyKOS's "junk queue" needed outside repair; Agoric invented suspended vats
after the fact): it spends the await (so it races deliveries and exhaustions
under consume-once), reclaims the record and the await's slot (an open slot's
decision claim is spent with it, so no late decision lands), pays the timeout
fee (or what the purse still holds of it) to the collector as its own fee, and
returns the rest of the purse to the payer. Every amount is a function of the
record and the Book. -/

structure AbandonRequest where
  subject : SubjectId
  record : CellId

def abandonTransaction (await : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/ABANDON/v1" (digestStream.encode await)

/-- The slot an abandoned await leaves: reclaimed; an open slot's decision
claim is spent with it. -/
def abandonSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (await : Await) :
    Except Refusal (List Post × List StableNullifier) :=
  match await.source with
  | .height _ => .ok ([], [])
  | .reply name _ =>
    match readSlot config snapshot name with
    | none => .error .slotMissing
    | some slot => match slot.phase with
      | .opened => .ok ([slotVacate config snapshot name], [AnswerSlot.decisionClaim name])
      | .decided _ _ => .ok ([slotVacate config snapshot name], [])

/-- The abandonment's own fee: the timeout fee, or what the purse holds of it. -/
def abandonFee (config : Config) (book : Book) (cell : CellId) (escrow : Escrow) : Nat :=
  min (purse book config.asset (heldAccount cell)) escrow.timeoutFee

/-- Its postings: the fee to the collector, the rest of the purse to the payer. -/
def abandonCharges (config : Config) (book : Book) (cell : CellId) (escrow : Escrow) : Batch :=
  let balance := purse book config.asset (heldAccount cell)
  let fee := abandonFee config book cell escrow
  ⟨[], (if fee = 0 then [] else [.fee (heldAccount cell) config.collector config.asset fee]) ++
       (if balance - fee = 0 then [] else [.transfer (heldAccount cell) escrow.account config.asset (balance - fee)])⟩

structure Abandonment {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : AbandonRequest) where
  private mk ::
  record : Record
  recordExact : readRecord snapshot request.record = some record
  located : request.record = recordCell config.domain record.object record.activity
  await : Await
  awaiting : record.phase = .awaiting await
  idExact : await.id = awaitId request.record record.generation record.checkpointDigest
  due : await.deadline + config.abandonGrace < height
  slotPosts : List Post
  slotClaims : List StableNullifier
  slotExact : abandonSlot config snapshot await = .ok (slotPosts, slotClaims)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = abandonCharges config (logicalBook book.logical) request.record record.escrow
  posts : List Post
  postsExact : posts = postAt snapshot request.record (vacant .record (recordKey record.object record.activity)) ::
    (slotPosts ++ [posted.write config snapshot])
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: slotClaims

def abandon {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : AbandonRequest) : Except Refusal (Abandonment config snapshot height request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error .recordMissing
  | some record =>
  if located : request.record = recordCell config.domain record.object record.activity then
  match awaiting : record.phase with
  | .done _ | .faulted _ => .error .notAwaiting
  | .awaiting await =>
  if idExact : await.id = awaitId request.record record.generation record.checkpointDigest then
  if due : await.deadline + config.abandonGrace < height then
  match slotExact : abandonSlot config snapshot await with
  | .error reason => .error reason
  | .ok (slotPosts, slotClaims) =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postings book (abandonCharges config (logicalBook book.logical) request.record record.escrow) with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = abandonCharges config (logicalBook book.logical) request.record record.escrow then
    .ok ⟨record, recordExact, located, await, awaiting, idExact, due, slotPosts, slotClaims, slotExact, book,
      bookExact, posted, postedBatch, _, rfl, _, rfl⟩
  else .error .bookRefused
  else .error (.notYetAbandonable await.deadline config.abandonGrace height)
  else .error .awaitMismatch
  else .error .recordMisplaced

def Abandonment.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (abandonTransaction ab.await.id) ab.posts [] ab.claims sealing

/-- **An abandonment conserves every asset.** -/
theorem Abandonment.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) (asset : AssetId) :
    (logicalBook ab.posted.post.logical).totalAsset asset = (logicalBook ab.book.logical).totalAsset asset :=
  ab.posted.conserves asset

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
  /-- The object whose declared state is written. -/
  object : CellId
  value : Data
  nonce : Nat

def stateTransaction (request : StateWriteRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/STATE/v3"
    (digestStream.encode request.object ++ StreamCodec.nat.encode request.nonce ++ dataBytes request.value)

/-- A direct write of an object's declared state. Who may write it is the
receiver's question (a holder of a capability on the object); what may be
written is the object's law's (`judged`). -/
structure StateWrite {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : StateWriteRequest) where
  private mk ::
  object : ObjectRecord
  objectExact : readObject config snapshot request.object = .ok (some object)
  /-- The state the write replaces: the new value is the next version. -/
  current : Option ObjectState
  currentExact : readState config snapshot request.object = .ok current
  judged : judgeWrite object (factsOf request.subject height request.object 3)
    (current.map ObjectState.value) request.value = .ok ()
  posts : List Post
  postsExact : posts = [postAt snapshot (stateCell config.domain request.object)
    (stateImage request.object ⟨(current.map ObjectState.version).getD 0 + 1, request.value⟩)]

def writeState {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : StateWriteRequest) : Except Refusal (StateWrite config snapshot height request) :=
  match objectExact : readObject config snapshot request.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some object) =>
    match currentExact : readState config snapshot request.object with
    | .error reason => .error reason
    | .ok current =>
      match judged : judgeWrite object (factsOf request.subject height request.object 3)
          (current.map ObjectState.value) request.value with
      | .error reason => .error reason
      | .ok () => .ok ⟨object, objectExact, current, currentExact, judged, _, rfl⟩

def StateWrite.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : StateWriteRequest} (written : StateWrite config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (stateTransaction request) written.posts
    [guardAt snapshot (objectCell config.domain request.object)] [] sealing

/-! ### create: an object's record -/

structure CreateRequest where
  subject : SubjectId
  /-- The object resource (a cell the authority layer issues capabilities on). -/
  object : CellId
  pin : Digest
  law : Minidregg.Pred.Pred
  upgrade : ObjectRecord.UpgradePolicy
  /-- The Book account that funds the record and the state cell; never authority. -/
  payer : AccountId

def createTransaction (request : CreateRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/OBJECT/TX/CREATE/v1" (subjectStream.encode request.subject ++ digestStream.encode request.object)

/-- The record a creation installs: schema version 1, continuity 0. -/
def CreateRequest.record (request : CreateRequest) : ObjectRecord :=
  ⟨request.object, request.pin, 1, request.law, request.upgrade, 0, request.payer⟩

/-- Who may create an object's record is the receiver's question (a holder of
a capability on the object resource). The kernel refuses a second record and a
pin that names no published package. -/
structure Creation {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : CreateRequest) where
  private mk ::
  absent : readObject config snapshot request.object = .ok none
  published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true
  posts : List Post
  postsExact : posts = [postAt snapshot (objectCell config.domain request.object)
    (objectImage request.object request.record)]

def create {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : CreateRequest) : Except Refusal (Creation config snapshot request) :=
  match absent : readObject config snapshot request.object with
  | .error reason => .error reason
  | .ok (some _) => .error .objectExists
  | .ok none =>
    if published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true then
      .ok ⟨absent, published, _, rfl⟩
    else .error .pinUnpublished

def Creation.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : CreateRequest} (created : Creation config snapshot request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (createTransaction request) created.posts
    [guardAt snapshot (packageCell config.domain request.pin)] [] sealing

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

/-! ### Resume with view -/

/-- Every post a kernel turn builds is written against the root the turn read
(`postAt`): the posts are current at the turn's snapshot. -/
def PostsCurrent {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post) : Prop :=
  ∀ post ∈ posts, post.pre = snapshot.model.roots post.cell

theorem settle_posts_current {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement}
    (settled : settle config snapshot height cell await = .ok settlement) :
    PostsCurrent snapshot settlement.posts := by
  unfold settle at settled
  split at settled
  · split at settled
    · cases settled
    · split at settled
      · cases settled
      · split at settled
        · rename_i decision _ _
          cases outcome : outcomeOfDecision decision <;>
            simp [outcome, bind, Except.bind, pure, Except.pure] at settled
          subst settled
          intro post member
          simp only [List.mem_singleton] at member
          subst member; simp only [slotVacate, postAt]
        · split at settled
          · cases settled
            intro post member
            simp only [List.mem_singleton] at member
            subst member; simp only [slotVacate, postAt]
          · cases settled
  · split at settled
    · cases settled; intro post member; simp at member
    · split at settled
      · cases settled; intro post member; simp at member
      · cases settled

theorem stateWrite_spec {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {current : Option ObjectState} {viewed : Bool} {write : Data} {written : StateWritten}
    (ok : stateWrite config snapshot object current viewed write = .ok (some written)) :
    ∃ edits value, decodeWrite write = .ok edits ∧
      applyWrite edits (current.map ObjectState.value) = .ok (some value) ∧
      written = ⟨current, ⟨(current.map ObjectState.version).getD 0 + 1, value⟩,
        postAt snapshot (stateCell config.domain object)
          (stateImage object ⟨(current.map ObjectState.version).getD 0 + 1, value⟩)⟩ := by
  unfold stateWrite at ok
  cases decoded : decodeWrite write with
  | error reason => simp [decoded, bind, Except.bind] at ok
  | ok edits =>
    simp only [decoded, bind, Except.bind] at ok
    split at ok
    · cases ok
    · cases applied : applyWrite edits (current.map ObjectState.value) with
      | error reason => simp [applied, pure, Except.pure] at ok
      | ok result =>
        simp only [applied, pure, Except.pure] at ok
        cases result with
        | none =>
          simp only at ok
          split at ok
          · cases ok
          · cases ok
        | some value =>
          cases ok
          exact ⟨edits, value, rfl, applied, rfl⟩

theorem commitYield_spec {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {plan : PlanAwait} {committed : YieldCommit}
    (ok : commitYield config snapshot height transaction cell object generation checkpoint current viewed plan =
      .ok committed) :
    stateWrite config snapshot object current viewed plan.write = .ok committed.written ∧
      (∀ written, committed.written = some written → written.post ∈ committed.posts) ∧
      PostsCurrent snapshot committed.posts := by
  unfold commitYield at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · rename_i written wrote
      have stateCurrent : PostsCurrent snapshot (written.map StateWritten.post).toList := by
        intro post member
        cases written with
        | none => simp at member
        | some one =>
          simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
          subst member
          obtain ⟨_, _, _, _, exact⟩ := stateWrite_spec wrote
          simp only [exact, postAt]
      split at ok
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          refine ⟨wrote, ?_, ?_⟩
          · intro one some; subst some; simp
          · intro post member
            simp only [List.mem_append, List.mem_singleton] at member
            rcases member with inState | isSlot
            · exact stateCurrent post inState
            · subst isSlot; simp only [slotPost, postAt]
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          refine ⟨wrote, ?_, stateCurrent⟩
          intro one some; subst some; simp

theorem segmentCommit_spec {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {committed : YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment =
      .ok (some committed)) :
    ∃ state plan, segment = .yielded state plan ∧
      commitYield config snapshot height transaction cell object generation
        (checkpointDigest (checkpointBytes state)) current viewed plan = .ok committed := by
  cases segment with
  | yielded state plan =>
    simp only [segmentCommit, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i one equation
      simp only [pure, Except.pure] at ok
      cases ok
      exact ⟨state, plan, rfl, equation⟩
  | finished result => simp [segmentCommit, pure, Except.pure] at ok
  | faulted reason => simp [segmentCommit, pure, Except.pure] at ok

/-- Every post a delivery commits is current at the delivering snapshot. -/
theorem Delivery.posts_current {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    PostsCurrent snapshot delivery.posts := by
  intro post member
  rw [delivery.postsExact] at member
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with isRecord | (inSettlement | inYield) | isBook
  · subst isRecord; simp only [recordPost, postAt]
  · exact settle_posts_current delivery.settled post inSettlement
  · cases yielded : delivery.yielded with
    | none => simp [yielded] at inYield
    | some committed =>
      simp only [yielded, Option.map_some, Option.getD_some] at inYield
      have commit := delivery.yieldedExact
      rw [yielded] at commit
      obtain ⟨_, _, _, committedExact⟩ := segmentCommit_spec commit
      exact (commitYield_spec committedExact).2.2 post inYield
  · rcases isBook with isBook | none
    · subst isBook; simp only [Postings.write, postAt]
    · simp at none

/-- An accepted intent found every post's pre-root current. -/
theorem accepted_posts_current {rootBytes : Bytes → Digest} {snapshot after : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {schedule : DurableCommitProtocol.Schedule}
    (accepted : DurableDataIntent.execute schedule snapshot intent = .accepted after) :
    ∀ write ∈ intent.writes, snapshot.model.roots write.cellId = write.expectedPre := by
  intro write member
  unfold DurableDataIntent.execute at accepted
  split at accepted
  · split at accepted <;> cases accepted
  · split at accepted
    · cases accepted
    · rename_i ok
      unfold DataIntent.preflight at ok
      split at ok
      · cases ok
      split at ok
      · cases ok
      split at ok
      · cases ok
      rename_i lower
      unfold DurableCommitProtocol.Intent.preflight at lower
      split at lower
      · cases lower
      split at lower
      · cases lower
      split at lower
      · cases lower
      split at lower
      · cases lower
      rename_i matched
      have all : ∀ write ∈ intent.writes, snapshot.model.roots write.cellId = write.expectedPre := by
        simpa [DataIntent.erase] using matched
      exact all write member

/-- An accepted intent found every read guard current. -/
theorem accepted_guards_current {rootBytes : Bytes → Digest} {snapshot after : Snapshot rootBytes}
    {intent : DataIntent rootBytes} {schedule : DurableCommitProtocol.Schedule}
    (accepted : DurableDataIntent.execute schedule snapshot intent = .accepted after) :
    ∀ guard ∈ intent.readGuards, snapshot.model.roots guard.cellId = guard.expectedRoot := by
  intro guard member
  unfold DurableDataIntent.execute at accepted
  split at accepted
  · split at accepted <;> cases accepted
  · split at accepted
    · cases accepted
    · rename_i ok
      by_contra stale
      have refused := DurableDataIntent.stale_read_guard_rejected snapshot intent
        ⟨guard, member, by simpa using stale⟩
      rw [refused] at ok
      cases ok

/-- **The outcome is preserved.** An await answered by its slot reaches the
activity exactly as the slot's decider decided it: the response the activity
is resumed with carries `outcomeOfDecision decision`, whatever happened to the
object's state since the yield (no kernel path replaces or drops it). -/
theorem resume_outcome_preserved {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    {slotName : Digest} {decider : SubjectId} {slot : AnswerSlot.Slot} {decision : AnswerSlot.Decision}
    {when : Nat}
    (source : delivery.await.source = .reply slotName decider)
    (read : readSlot config snapshot slotName = some slot)
    (decided : slot.phase = .decided decision when) :
    outcomeOfDecision decision = .ok delivery.settlement.decided ∧
      resume (responseData delivery.settlement.decided delivery.view).term delivery.state =
        some delivery.resumed := by
  refine ⟨?_, delivery.resumeExact⟩
  have settled := delivery.settled
  unfold settle at settled
  rw [source] at settled
  simp only [read, decided] at settled
  split at settled
  · cases settled
  · cases outcome : outcomeOfDecision decision with
    | error reason => simp [outcome, bind, Except.bind] at settled
    | ok value =>
      simp [outcome, bind, Except.bind, pure, Except.pure] at settled
      rw [← settled]

/-- **The view is current.** The view a delivery resumes the activity with is
the object's state cell as the delivering snapshot holds it, and the delivery
is accepted only on a snapshot where that cell's root is still the one the view
was read from: the activity never acts on a state that has moved. -/
theorem resume_view_current {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (sealing : Seal) {later after : Snapshot rootBytes} {schedule : DurableCommitProtocol.Schedule}
    (accepted : DurableDataIntent.execute schedule later (delivery.intent sealing) = .accepted after) :
    readState config snapshot delivery.record.object = .ok (some delivery.view) ∧
      later.model.roots (stateCell config.domain delivery.record.object) =
        snapshot.model.roots (stateCell config.domain delivery.record.object) := by
  refine ⟨delivery.viewExact, ?_⟩
  by_cases posted : stateCell config.domain delivery.record.object ∈
      ((delivery.posts.map (Post.write rootBytes)).map DataWrite.cellId)
  · simp only [List.mem_map] at posted
    obtain ⟨write, ⟨post, member, rfl⟩, same⟩ := posted
    have current := accepted_posts_current accepted (post.write rootBytes)
      (by simp only [Delivery.intent, intentOf_writes, List.mem_map]; exact ⟨post, member, rfl⟩)
    simp only [Post.write] at current same
    rw [← same, current]
    exact delivery.posts_current post member
  · have inGuards : guardAt snapshot (stateCell config.domain delivery.record.object) ∈ delivery.guards := by
      rw [delivery.guardsExact]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have guarded : guardAt snapshot (stateCell config.domain delivery.record.object) ∈
        (delivery.intent sealing).readGuards := by
      show _ ∈ readOnly rootBytes delivery.posts (delivery.guards ++ sealing.guards)
      exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl inGuards), decide_eq_true posted⟩
    have current := accepted_guards_current accepted _ guarded
    rw [guardAt_cellId, guardAt_expectedRoot] at current
    exact current

/-- **Every state write is computed from the view, in the same turn.** If the
segment a delivery runs yields a Plan that writes, the delivery posts the
object's state cell against the root the view was read from, installing the
next version of exactly the Plan's write applied to the view's state. -/
theorem yield_write_from_current_read {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request) {committed : YieldCommit} {written : StateWritten}
    (yielded : delivery.yielded = some committed) (writes : committed.written = some written) :
    written.post ∈ delivery.posts ∧
      written.post.cell = stateCell config.domain delivery.record.object ∧
      written.post.pre = snapshot.model.roots (stateCell config.domain delivery.record.object) ∧
      written.before = some delivery.view ∧
      written.after.version = delivery.view.version + 1 ∧
      ∃ state plan edits, delivery.segment = .yielded state plan ∧ decodeWrite plan.write = .ok edits ∧
        applyWrite edits (some delivery.view.value) = .ok (some written.after.value) := by
  have commit := delivery.yieldedExact
  rw [yielded] at commit
  obtain ⟨state, plan, segmentIs, committedExact⟩ := segmentCommit_spec commit
  obtain ⟨wrote, inPosts, _⟩ := commitYield_spec committedExact
  rw [writes] at wrote
  obtain ⟨edits, value, decoded, applied, exact⟩ := stateWrite_spec wrote
  have member : written.post ∈ delivery.posts := by
    rw [delivery.postsExact, yielded]
    simp only [List.mem_cons, List.mem_append, Option.map_some, Option.getD_some]
    exact Or.inr (Or.inl (Or.inr (inPosts written writes)))
  subst exact
  refine ⟨member, rfl, rfl, rfl, rfl, state, plan, edits, segmentIs, decoded, ?_⟩
  simpa using applied

/-- **A write is refused once the state has moved.** A delivery prepared on one
snapshot whose Plan writes the declared state is never accepted on a snapshot
where the state cell's root is not the one the view was read from: the ruling's
"a Plan state write is refused if the version moved". A fresh delivery reads
the moved state (`resume_view_current`). -/
theorem moved_state_refuses {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (sealing : Seal) {later after : Snapshot rootBytes} (schedule : DurableCommitProtocol.Schedule)
    (moved : later.model.roots (stateCell config.domain delivery.record.object) ≠
      snapshot.model.roots (stateCell config.domain delivery.record.object)) :
    DurableDataIntent.execute schedule later (delivery.intent sealing) ≠ .accepted after := by
  intro accepted
  exact moved (resume_view_current delivery sealing accepted).2

/-! ### Deltas commute -/

/-- An add-only write: every edit adds to a natural field. -/
def AddOnly (edits : List (String × Edit)) : Prop := ∀ edit ∈ edits, ∃ amount, edit.2 = .add amount

theorem editField_addOnly {edits : List (String × Edit)} (adds : AddOnly edits) (name : String) :
    (edits.find? (fun edit => edit.1 == name)).map Prod.snd = none ∨
      ∃ amount, (edits.find? (fun edit => edit.1 == name)).map Prod.snd = some (.add amount) := by
  cases found : edits.find? (fun edit => edit.1 == name) with
  | none => exact Or.inl rfl
  | some edit =>
    obtain ⟨amount, isAdd⟩ := adds edit (List.mem_of_find?_eq_some found)
    exact Or.inr ⟨amount, by simp [isAdd]⟩

/-- Two add-only edits of one field commute. -/
theorem editField_add_comm {one two : List (String × Edit)} (addsOne : AddOnly one) (addsTwo : AddOnly two)
    {name : String} {value v1 v12 v2 v21 : Data}
    (h1 : editField one name value = .ok v1) (h12 : editField two name v1 = .ok v12)
    (h2 : editField two name value = .ok v2) (h21 : editField one name v2 = .ok v21) : v12 = v21 := by
  unfold editField at h1 h12 h2 h21
  rcases editField_addOnly addsOne name with n1 | ⟨k1, a1⟩ <;>
    rcases editField_addOnly addsTwo name with n2 | ⟨k2, a2⟩
  · simp only [n1, n2, Except.ok.injEq] at h1 h12 h2 h21
    subst h1 h12 h2 h21; rfl
  · simp only [n1, a2, Except.ok.injEq] at h1 h12 h2 h21
    subst h1 h21
    cases value <;> simp_all
  · simp only [a1, n2, Except.ok.injEq] at h1 h12 h2 h21
    subst h12 h2
    cases value <;> simp_all
  · simp only [a1, a2] at h1 h12 h2 h21
    cases value <;> simp only [reduceCtorEq] at h1 h2
    rename_i base
    simp only [Except.ok.injEq] at h1 h2
    subst h1 h2
    simp only [Except.ok.injEq] at h12 h21
    subst h12 h21
    congr 1; omega

/-- Two add-only writes applied field-wise, in either order, give the same fields. -/
theorem editFields_add_comm {one two : List (String × Edit)} (addsOne : AddOnly one) (addsTwo : AddOnly two) :
    ∀ {fields a b c d : List (String × Data)},
      editFields one fields = .ok a → editFields two a = .ok b →
      editFields two fields = .ok c → editFields one c = .ok d → b = d
  | [], a, b, c, d, h1, h12, h2, h21 => by
    simp only [editFields, Except.ok.injEq] at h1 h2
    subst h1 h2
    simp only [editFields, Except.ok.injEq] at h12 h21
    rw [← h12, ← h21]
  | field :: rest, a, b, c, d, h1, h12, h2, h21 => by
    simp only [editFields] at h1 h2
    split at h1
    · cases h1
    rename_i v1 e1
    split at h1
    · cases h1
    rename_i a' r1
    split at h2
    · cases h2
    rename_i v2 e2
    split at h2
    · cases h2
    rename_i c' r2
    cases h1; cases h2
    simp only [editFields] at h12 h21
    split at h12
    · cases h12
    rename_i v12 e12
    split at h12
    · cases h12
    rename_i b' r12
    split at h21
    · cases h21
    rename_i v21 e21
    split at h21
    · cases h21
    rename_i d' r21
    cases h12; cases h21
    rw [editField_add_comm addsOne addsTwo e1 e12 e2 e21,
      editFields_add_comm addsOne addsTwo r1 r12 r2 r21]

/-- **Deltas commute.** Two add-only writes applied by `applyWrite` to present
record state, in either order, give the same state: two activities' replies to
one object both land, whichever is delivered first. -/
theorem add_writes_commute {one two : List (String × Edit)} (addsOne : AddOnly one) (addsTwo : AddOnly two)
    {fields : List (String × Data)} {a b c d : Data}
    (h1 : applyWrite one (some (.record fields)) = .ok (some a)) (h12 : applyWrite two (some a) = .ok (some b))
    (h2 : applyWrite two (some (.record fields)) = .ok (some c)) (h21 : applyWrite one (some c) = .ok (some d)) :
    b = d := by
  have shape : ∀ {edits : List (String × Edit)} {fs : List (String × Data)} {r : Data},
      applyWrite edits (some (.record fs)) = .ok (some r) →
        ∃ out, editFields edits fs = .ok out ∧ r = .record out := by
    intro edits fs r h
    simp only [applyWrite] at h
    split at h
    · cases h
    · split at h
      · cases out : editFields edits fs with
        | error reason => simp [out, Except.map] at h
        | ok out' =>
          simp only [out, Except.map, Except.ok.injEq, Option.some.injEq] at h
          exact ⟨out', rfl, h.symm⟩
      · cases h
  obtain ⟨a', ea, rfl⟩ := shape h1
  obtain ⟨b', eb, rfl⟩ := shape h12
  obtain ⟨c', ec, rfl⟩ := shape h2
  obtain ⟨d', ed, rfl⟩ := shape h21
  rw [editFields_add_comm addsOne addsTwo ea eb ec ed]

/-- **Births are never blind.** A birth's first segment has not seen the
object's state, so where state exists its write may not `set` a field. -/
theorem stateWrite_unviewed_never_sets {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {object : CellId} {present : ObjectState} {write : Data}
    {edits : List (String × Edit)} (decoded : decodeWrite write = .ok edits)
    (sets : edits.any (fun edit => edit.2.isSet) = true) :
    stateWrite config snapshot object (some present) false write = .error .blindWrite := by
  simp [stateWrite, decoded, sets, bind, Except.bind]

/-- **The resume binds the stored checkpoint.** The machine state a delivery
resumes is decoded from the record cell's own checkpoint bytes, whose digest
the record and the await id name; the response is the typed outcome with the
view; nothing of the state comes from the request. -/
theorem resume_binds_checkpoint {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    ∃ record state,
      readRecord snapshot request.record = some record ∧
      record.phase = .awaiting delivery.await ∧
      delivery.await.id = awaitId request.record record.generation (checkpointDigest record.checkpoint) ∧
      decodeCheckpoint record.checkpoint = some state ∧
      resume (responseData delivery.settlement.decided delivery.view).term state = some delivery.resumed ∧
      runSegment config delivery.envelope.sourceTicks delivery.resumed = .ok delivery.segment := by
  refine ⟨delivery.record, delivery.state, delivery.recordExact, delivery.awaiting, ?_, delivery.stateExact,
    delivery.resumeExact, delivery.segmentExact⟩
  rw [delivery.digestExact]; exact delivery.idExact

/-- **Resume determinism.** Two deliveries of the same record at the same
snapshot and height resume the same machine state with the same response and,
given the same envelope, end their segments identically. -/
theorem resume_deterministic {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {first second : DeliverRequest} (one : Delivery config snapshot height first)
    (two : Delivery config snapshot height second) (sameRecord : first.record = second.record)
    (sameEnvelope : first.extra = second.extra) :
    one.resumed = two.resumed ∧ one.segment = two.segment ∧ one.next = two.next := by
  have records : one.record = two.record := by
    have := one.recordExact; rw [sameRecord, two.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : one.await = two.await := by
    have a := one.awaiting; have b := two.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : one.settlement = two.settlement := by
    have a := one.settled; have b := two.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  have views : one.view = two.view := by
    have a := one.viewExact; rw [records, two.viewExact] at a
    exact (Option.some.inj (Except.ok.inj a)).symm
  have states : one.state = two.state := by
    have a := one.stateExact; rw [records, two.stateExact] at a; exact (Option.some.inj a).symm
  have resumedEq : one.resumed = two.resumed := by
    have a := one.resumeExact; rw [settlements, views, states, two.resumeExact] at a
    exact (Option.some.inj a).symm
  have envelopes : one.envelope = two.envelope := by
    rw [one.envelopeExact, two.envelopeExact, records, settlements, sameEnvelope]
  have segments : one.segment = two.segment := by
    have a := one.segmentExact; rw [envelopes, resumedEq, two.segmentExact] at a
    exact (Except.ok.inj a).symm
  have yieldeds : one.yielded = two.yielded := by
    have a := one.yieldedExact
    rw [awaits, sameRecord, records, segments, views, two.yieldedExact] at a
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
    (request : DeliverRequest) (extra : request.extra ≠ zeroCapacity) :
    Operation.fee request.account config.collector config.asset (config.tariff.workOf request.extra) ∈
      (deliveryCharges config record cell path request).operations := by
  simp [deliveryCharges, extra]

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


/-! ## Metering and disposal (ACTIVITY-METERING-DISPOSAL) -/

/-- **Exhaustion is never free, and is paid only by declared amounts.** An
admitted exhaustion posts exactly the declared charge (the purse's declared
envelope of the ending path the first time this await exhausts, plus the
public price of the submitter's added envelope), leaves the activity exactly at
its yield (checkpoint, digest, generation, phase), and strictly raises `tried`
to the envelope it ran under. -/
theorem exhaustion_charges_declared {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (ex : Exhaustion config snapshot height request) :
    ex.posted.batch = exhaustCharges config ex.record request.record ex.settlement.path request ∧
    ex.next.checkpoint = ex.record.checkpoint ∧
    ex.next.checkpointDigest = ex.record.checkpointDigest ∧
    ex.next.generation = ex.record.generation ∧
    ex.next.phase = ex.record.phase ∧
    ex.next.tried = (addCapacity (ex.record.escrow.capacity ex.settlement.path) request.extra).sourceTicks ∧
    ex.record.tried < ex.next.tried := by
  have n := ex.nextExact
  refine ⟨ex.postedBatch, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [n]
  · rw [← ex.envelopeExact]
  · exact ex.raises

/-- The declared charge, as postings: the purse pays its declared envelope only
on the first exhaustion of an await; the submitter pays the price of what it
declared, never of what ran. -/
theorem exhaust_charges_are_declared (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : ExhaustRequest) :
    (exhaustCharges config record cell path request).operations =
      (if record.tried = 0 then [Operation.fee (heldAccount cell) config.collector config.asset
          (record.escrow.used path)] else []) ++
      (if request.extra = zeroCapacity then []
       else [Operation.fee request.account config.collector config.asset (config.tariff.workOf request.extra)]) :=
  rfl

/-- **An exhaustion spends no claim of its own**: the await stays open. -/
theorem exhaustion_spends_nothing {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (ex : Exhaustion config snapshot height request) (sealing : Seal) :
    (ex.intent sealing).nullifiers = sealing.nullifiers := by
  simp [Exhaustion.intent]

/-- **Exhaustion is a fact about the run, not a claim of the submitter.** For
one record, snapshot, height and added envelope, an exhaustion and a delivery
never both exist: the run that resumes the stored checkpoint with the settled
outcome either exhausts or ends its segment. -/
theorem exhaustion_excludes_delivery {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {exReq : ExhaustRequest} {delReq : DeliverRequest}
    (ex : Exhaustion config snapshot height exReq) (delivery : Delivery config snapshot height delReq)
    (sameRecord : exReq.record = delReq.record) (sameExtra : exReq.extra = delReq.extra) : False := by
  have records : ex.record = delivery.record := by
    have := ex.recordExact; rw [sameRecord, delivery.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : ex.await = delivery.await := by
    have a := ex.awaiting; have b := delivery.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : ex.settlement = delivery.settlement := by
    have a := ex.settled; have b := delivery.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  have views : ex.view = delivery.view := by
    have a := ex.viewExact; rw [records, delivery.viewExact] at a
    exact (Option.some.inj (Except.ok.inj a)).symm
  have states : ex.state = delivery.state := by
    have a := ex.stateExact; rw [records, delivery.stateExact] at a; exact (Option.some.inj a).symm
  have resumedEq : ex.resumed = delivery.resumed := by
    have a := ex.resumeExact; rw [settlements, views, states, delivery.resumeExact] at a
    exact (Option.some.inj a).symm
  have envelopes : ex.envelope = delivery.envelope := by
    rw [ex.envelopeExact, delivery.envelopeExact, records, settlements, sameExtra]
  have ran := ex.ran
  rw [envelopes, resumedEq, delivery.segmentExact] at ran
  cases ran

/-- **No attempt is paid twice.** Two exhaustions of one record from one
snapshot and height, with equal added envelopes, post the same charge, and
after either installs the other is refused before it runs (its envelope does not
exceed the raised `tried`). -/
theorem exhaustion_charge_measurement_free {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {first second : ExhaustRequest}
    (one : Exhaustion config snapshot height first) (two : Exhaustion config snapshot height second)
    (sameRecord : first.record = second.record) (sameExtra : first.extra = second.extra) :
    one.envelope = two.envelope ∧ one.next.tried = two.next.tried ∧
      exhaustCharge config one.record one.settlement.path first =
        exhaustCharge config two.record two.settlement.path second := by
  have records : one.record = two.record := by
    have := one.recordExact; rw [sameRecord, two.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : one.await = two.await := by
    have a := one.awaiting; have b := two.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : one.settlement = two.settlement := by
    have a := one.settled; have b := two.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  have envelopes : one.envelope = two.envelope := by
    rw [one.envelopeExact, two.envelopeExact, records, settlements, sameExtra]
  refine ⟨envelopes, ?_, ?_⟩
  · rw [one.nextExact, two.nextExact]; simp [envelopes]
  · simp [exhaustCharge, records, settlements, sameExtra]

/-- **A reclaimed cell reads as nothing, by name.** The empty kernel body of a
reclaimed record cell decodes to no record (a delivery, exhaustion or
abandonment of it is refused `recordMissing`), and that of a reclaimed slot to
no slot (a late decision is refused `slotMissing`). -/
theorem recordOfBody_vacant : recordOfBody [] = none := rfl

theorem slotOfBody_vacant : slotOfBody [] = none := rfl

/-- A record that has ended holds nothing: its body is empty. -/
theorem recordBody_ended (record : Record) (ended : ∀ await, record.phase ≠ .awaiting await) :
    recordBody record = [] := by
  unfold recordBody
  cases phase : record.phase with
  | awaiting await => exact absurd phase (ended await)
  | done _ => rfl
  | faulted _ => rfl

/-- The record a segment that does not yield leaves has ended. -/
theorem nextRecord_ended (base : Record) (generation : Nat) (segment : Segment) (yielded : Option YieldCommit)
    (ends : segment.yields = false) : ∀ await, (nextRecord base generation segment yielded).phase ≠ .awaiting await := by
  intro await
  cases segment with
  | yielded _ _ => simp [Segment.yields] at ends
  | finished _ => simp [nextRecord]
  | faulted _ => simp [nextRecord]

theorem nextRecord_names (base : Record) (generation : Nat) (segment : Segment) (yielded : Option YieldCommit) :
    (nextRecord base generation segment yielded).object = base.object ∧
      (nextRecord base generation segment yielded).activity = base.activity := by
  cases segment <;> cases yielded <;> simp [nextRecord]

/-- **Disposal frees the record.** A delivery whose segment ends (finished or
faulted) writes its record cell to the empty tombstone: the checkpoint, the
input and the result leave the store in the turn that ends the activity (and
`settlePurse` returns the purse, `end_returns_purse`). -/
theorem delivery_end_vacates {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (ends : delivery.segment.yields = false) :
    delivery.posts.head? = some (postAt snapshot request.record
      (vacant .record (recordKey delivery.record.object delivery.record.activity))) := by
  rw [delivery.recordFirst]
  have ended := nextRecord_ended delivery.record (delivery.record.generation + 1) delivery.segment
    delivery.yielded ends
  have names := nextRecord_names delivery.record (delivery.record.generation + 1) delivery.segment delivery.yielded
  rw [← delivery.nextExact] at ended names
  simp [recordPost, vacant, recordBody_ended _ ended, names.1, names.2]

/-- The same for a birth whose first segment already ends: no record is kept. -/
theorem birth_end_vacates {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (ends : born.segment.yields = false) :
    born.posts.head? = some (postAt snapshot born.cell
      (vacant .record (recordKey request.object (activityId request.object (birthTransaction request))))) := by
  rw [born.recordFirst]
  have ended : ∀ await, born.record.phase ≠ .awaiting await := by
    rw [born.recordExact]; exact nextRecord_ended _ _ _ _ ends
  have names : born.record.object = request.object ∧
      born.record.activity = activityId request.object (birthTransaction request) := by
    rw [born.recordExact]; exact nextRecord_names _ _ _ _
  simp [recordPost, vacant, recordBody_ended _ ended, names.1, names.2]

/-- **Settled slots are reclaimed.** Whenever a reply await settles (decided,
or expired at its deadline), the settlement reclaims its slot cell. -/
theorem settle_reclaims_slot {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement} {name : Digest} {decider : SubjectId}
    (source : await.source = .reply name decider)
    (settled : settle config snapshot height cell await = .ok settlement) :
    settlement.posts = [slotVacate config snapshot name] := by
  unfold settle at settled
  rw [source] at settled
  simp only at settled
  cases hslot : readSlot config snapshot name with
  | none => rw [hslot] at settled; cases settled
  | some slot =>
    rw [hslot] at settled
    simp only at settled
    split at settled
    · cases settled
    · cases hphase : slot.phase with
      | decided decision decidedAt =>
        rw [hphase] at settled
        cases outcome : outcomeOfDecision decision with
        | error e => simp [outcome, bind, Except.bind] at settled
        | ok value =>
          simp [outcome, bind, Except.bind, pure, Except.pure] at settled
          subst settled
          rfl
      | opened =>
        rw [hphase] at settled
        cases hexp : AnswerSlot.expire slot height with
        | error e => simp [hexp] at settled
        | ok expired =>
          simp [hexp] at settled
          subst settled
          rfl

/-- A delivery of a reply await reclaims the slot it settled. -/
theorem delivery_reclaims_slot {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    {name : Digest} {decider : SubjectId} (source : delivery.await.source = .reply name decider) :
    slotVacate config snapshot name ∈ delivery.posts := by
  rw [delivery.postsExact, settle_reclaims_slot source delivery.settled]
  simp

/-- **Abandonment returns the purse and ends the await.** An admitted
abandonment is past deadline plus grace; it spends the await's claim; it
reclaims the record; its own fee is at most the timeout fee; and the fee plus
what it returns to the payer is the whole purse. -/
theorem abandon_returns_escrow {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) :
    ab.await.deadline + config.abandonGrace < height ∧
    awaitClaim ab.await.id ∈ ab.claims ∧
    ab.posts.head? = some (postAt snapshot request.record (vacant .record (recordKey ab.record.object ab.record.activity))) ∧
    ab.posted.batch = abandonCharges config (logicalBook ab.book.logical) request.record ab.record.escrow ∧
    abandonFee config (logicalBook ab.book.logical) request.record ab.record.escrow ≤ ab.record.escrow.timeoutFee ∧
    abandonFee config (logicalBook ab.book.logical) request.record ab.record.escrow +
        (purse (logicalBook ab.book.logical) config.asset (heldAccount request.record) -
          abandonFee config (logicalBook ab.book.logical) request.record ab.record.escrow) =
      purse (logicalBook ab.book.logical) config.asset (heldAccount request.record) := by
  refine ⟨ab.due, by rw [ab.claimsExact]; simp, by rw [ab.postsExact]; rfl, ab.postedBatch, ?_, ?_⟩
  · unfold abandonFee; omega
  · unfold abandonFee; omega

/-- An abandonment closes an open slot: its decision claim is spent with it,
so no late decision ever lands. -/
theorem abandon_closes_open_slot {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request)
    {name : Digest} {decider : SubjectId} {slot : AnswerSlot.Slot}
    (source : ab.await.source = .reply name decider) (read : readSlot config snapshot name = some slot)
    (opened : slot.phase = .opened) :
    slotVacate config snapshot name ∈ ab.posts ∧ AnswerSlot.decisionClaim name ∈ ab.claims := by
  have exact := ab.slotExact
  unfold abandonSlot at exact
  rw [source] at exact
  simp only [read, opened, Except.ok.injEq, Prod.mk.injEq] at exact
  obtain ⟨hp, hc⟩ := exact
  rw [ab.postsExact, ab.claimsExact, ← hp, ← hc]
  simp

theorem Abandonment.spends {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) (sealing : Seal) :
    awaitClaim ab.await.id ∈ (ab.intent sealing).nullifiers := by
  simp [Abandonment.intent, ab.claimsExact]

/-- **Abandonment and delivery exclude each other.** Once an abandonment
installs, no turn that ends the same await (a delivery, another abandonment)
is ever accepted; and the same claim makes an installed delivery exclude a
later abandonment. -/
theorem abandon_delivery_exclusive {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) (sealing : Seal)
    (installed : DurableDataIntent.execute .complete snapshot (ab.intent sealing) = .accepted next)
    (later : DataIntent rootBytes) (again : awaitClaim ab.await.id ∈ later.nullifiers)
    (schedule : DurableCommitProtocol.Schedule) (after : Snapshot rootBytes) :
    DurableDataIntent.execute schedule next later ≠ .accepted after :=
  spent_claim_never_accepted (ab.spends sealing) installed later again schedule after


#assert_axioms record_roundTrip
#assert_axioms TypedData.typed
#assert_axioms Postings.conserves
#assert_axioms Birth.conserves
#assert_axioms Delivery.conserves
#assert_axioms TopUp.conserves

/-! ## Objects: every declared-state write is judged by the object's law -/

/-- **`activity_write_judged`, birth.** An admitted birth is on an object (the
cell has an `ObjectRecord`), runs the package the object pins, and the write its
first segment built (`stateWrite`: the post `commitYield_spec` places among the
birth's posts) is admitted by the object's law. -/
theorem Birth.write_judged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (written : StateWritten) (wrote : born.yielded.bind YieldCommit.written = some written) :
    ∃ object, readObject config snapshot request.object = .ok (some object) ∧ object.pin = request.pin ∧
      admitWrite object (factsOf request.subject height request.object 1)
        (written.before.map ObjectState.value) written.after.value = .ok () :=
  ⟨born.object, born.objectExact, born.pinned, judgeWritten_ok born.judged written wrote⟩

/-- **`activity_write_judged`, delivery.** The object's record is read in the
delivering turn, and the segment's write is admitted by its law with the
activity's principal (never the deliverer) as the subject. -/
theorem Delivery.write_judged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (written : StateWritten) (wrote : delivery.yielded.bind YieldCommit.written = some written) :
    ∃ object, readObject config snapshot delivery.record.object = .ok (some object) ∧
      admitWrite object (factsOf delivery.record.escrow.payer height delivery.record.object 2)
        (written.before.map ObjectState.value) written.after.value = .ok () :=
  ⟨delivery.object, delivery.objectExact, judgeWritten_ok delivery.judged written wrote⟩

/-- **`activity_write_judged`, direct write.** A direct write is on an object and
admitted by its law. -/
theorem StateWrite.write_judged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : StateWriteRequest} (written : StateWrite config snapshot height request) :
    ∃ object, readObject config snapshot request.object = .ok (some object) ∧
      admitWrite object (factsOf request.subject height request.object 3)
        (written.current.map ObjectState.value) request.value = .ok () :=
  ⟨written.object, written.objectExact, judgeWrite_ok written.judged⟩

/-- **A cell without an object record admits no birth**, refused by name. -/
theorem birth_refuses_non_object {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (absent : readObject config snapshot request.object = .ok none) :
    birth config snapshot height request = .error .notAnObject := by
  unfold birth
  split
  · rename_i reason found; rw [absent] at found; cases found
  · rfl
  · rename_i object found; rw [absent] at found; cases found

/-- **A birth runs only the package the object pins**, refused by name otherwise. -/
theorem birth_refuses_other_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} {object : ObjectRecord}
    (found : readObject config snapshot request.object = .ok (some object)) (other : object.pin ≠ request.pin) :
    birth config snapshot height request = .error (.pinMismatch object.pin request.pin) := by
  unfold birth
  split
  · rename_i reason found'; rw [found] at found'; cases found'
  · rename_i found'; rw [found] at found'; cases found'
  · rename_i object' found'
    rw [found] at found'
    cases found'
    simp [other]
    rfl

/-- **A direct write the object's law refuses is refused**, naming the clause. -/
theorem writeState_refuses_lawless {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : StateWriteRequest} {object : ObjectRecord} {current : Option ObjectState}
    {reason : WriteRefusal}
    (found : readObject config snapshot request.object = .ok (some object))
    (state : readState config snapshot request.object = .ok current)
    (denied : admitWrite object (factsOf request.subject height request.object 3)
      (current.map ObjectState.value) request.value = .error reason) :
    (writeState config snapshot height request).toOption = none := by
  unfold writeState
  split
  · rfl
  · rename_i found'; rw [found] at found'; cases found'
  · rename_i object' found'
    rw [found] at found'
    cases found'
    split
    · rfl
    · rename_i current' state'
      rw [state] at state'
      cases state'
      split
      · rfl
      · rename_i judged
        unfold judgeWrite at judged
        rw [denied] at judged
        cases judged

/-- **A second record is refused.** -/
theorem create_refuses_existing {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : CreateRequest} {object : ObjectRecord}
    (found : readObject config snapshot request.object = .ok (some object)) :
    create config snapshot request = .error .objectExists := by
  unfold create
  split
  · rename_i reason found'; rw [found] at found'; cases found'
  · rfl
  · rename_i found'; rw [found] at found'; cases found'

#assert_axioms execute_accepted_install
#assert_axioms spent_claim_never_accepted
#assert_axioms installed_retry_replays
#assert_axioms Delivery.spends
#assert_axioms resume_consumes_once
#assert_axioms second_delivery_refused
#assert_axioms slot_decided_once
#assert_axioms slot_single_decider
#assert_axioms settle_posts_current
#assert_axioms stateWrite_spec
#assert_axioms commitYield_spec
#assert_axioms segmentCommit_spec
#assert_axioms Delivery.posts_current
#assert_axioms accepted_posts_current
#assert_axioms accepted_guards_current
#assert_axioms resume_outcome_preserved
#assert_axioms resume_view_current
#assert_axioms yield_write_from_current_read
#assert_axioms moved_state_refuses
#assert_axioms stateWrite_unviewed_never_sets
#assert_axioms editField_add_comm
#assert_axioms editFields_add_comm
#assert_axioms add_writes_commute
#assert_axioms resume_binds_checkpoint
#assert_axioms resume_deterministic
#assert_axioms refund_measurement_free
#assert_axioms submitter_charge_declared
#assert_axioms yield_reserves_pair
#assert_axioms end_returns_purse
#assert_axioms Exhaustion.conserves
#assert_axioms Abandonment.conserves
#assert_axioms exhaustion_charges_declared
#assert_axioms exhaust_charges_are_declared
#assert_axioms exhaustion_spends_nothing
#assert_axioms exhaustion_excludes_delivery
#assert_axioms exhaustion_charge_measurement_free
#assert_axioms recordOfBody_vacant
#assert_axioms slotOfBody_vacant
#assert_axioms recordBody_ended
#assert_axioms nextRecord_ended
#assert_axioms nextRecord_names
#assert_axioms delivery_end_vacates
#assert_axioms birth_end_vacates
#assert_axioms settle_reclaims_slot
#assert_axioms delivery_reclaims_slot
#assert_axioms abandon_returns_escrow
#assert_axioms abandon_closes_open_slot
#assert_axioms Abandonment.spends
#assert_axioms abandon_delivery_exclusive
#assert_axioms judgeWrite_ok
#assert_axioms judgeWritten_ok
#assert_axioms Birth.write_judged
#assert_axioms Delivery.write_judged
#assert_axioms StateWrite.write_judged
#assert_axioms birth_refuses_non_object
#assert_axioms birth_refuses_other_pin
#assert_axioms writeState_refuses_lawless
#assert_axioms create_refuses_existing
end Minidregg.Kernel.ObjectiveActivity
