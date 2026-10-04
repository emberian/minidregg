/- The kernel activity: a Core4 activity persisted between turns, its awaits,
and the resume contract.

An activity of an object is a cell under the object (`recordCell object
activity`) holding its `Record`: the exact machine checkpoint (the bytes of
`ObjectiveBendCheckpoint.encodeState`, never a summary), the checkpoint's
digest, the pinned package identity, the generation, the read versions the
continuation depends on, the escrowed fee pair, and its phase. While awaiting,
the phase names one `Await`: its id `H(record cell, generation, checkpoint
digest)`, its source (an answer slot with one decider, or a height), and a
mandatory deadline height.

Five kernel turns; each is ONE `DataIntent` built by `intentOf`, so its writes
commit all together or not at all (`DurableDataIntent.execute_no_partial_data_commit`)
and nothing it does is visible before it commits:

* `publish`: the package (a checked `ObjectiveBendSourceArtifact`) into its
  content-addressed cell.
* `birth`: instantiate the pinned definition with typed input, run to the
  first yield, commit the record, the Plan's declared-state write, the answer
  slot it awaits and the escrow, all at once.
* `resolve`: the slot's one decider decides it (typed against the awaiting
  activity's own response type) at or before the deadline; spends the slot claim.
* `deliver`: anyone resumes the activity with the typed outcome of its await.
  The await id is spent as a nullifier bound to the checkpoint digest, AND the
  record cell is written against its current root: consume-once is a
  compare-and-swap at admission's decide point. Recorded reads are revalidated
  (stale: the activity receives `conflict`, never the bare outcome). Past the
  deadline an open slot expires in the same turn and the activity receives
  `timedOut`. The checkpoint is decoded from the record cell (no state is ever
  accepted from a request), resumed with the typed response, run to its next
  yield or end, and the new checkpoint, the Plan's write and the next await
  commit together.
* `writeState`: the activity owner writes the object's declared state directly
  (what makes a recorded read stale).

Fees. Every await escrows a pair priced from DECLARED envelopes
(`Tariff.price resumeTicks`, `Tariff.price timeoutTicks`); exactly one of the
pair pays the turn that ends the await and the other is returned to the payer.
No refund depends on how much computation ran (`refund_measurement_free`).

What is not here: collection at the yield (checkpoints grow with the heap),
upgrade dispositions, sends/inboxes (a `message` await is refused by name), the
native signed-command route, and the resource Book: fee accounts here are
kernel cells (`accountCell`) that stand in for the Book rail. -/
import Kernel.AnswerSlot
import Compiler.ObjectiveBendSourceArtifact

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
set_option autoImplicit false

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

structure Escrow where
  payer : SubjectId
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
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun e => (e.payer, e.resumeTicks, e.timeoutTicks, e.resumeFee, e.timeoutFee))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩)
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

def recordFrame : Bytes := "DREGG/OBJECTIVE/ACTIVITY-RECORD/v1".toUTF8.toList
def recordCodec := framed recordFrame recordStream
def encodeRecord (record : Record) : Bytes := recordCodec.encode record
def decodeRecord (bytes : Bytes) : Option Record := recordCodec.decode bytes

theorem record_roundTrip (record : Record) : decodeRecord (encodeRecord record) = some record :=
  framed_roundTrip _ _ record

/-- Fee accounts: a kernel cell per payer holding a balance. They stand in for
the resource Book until escrow postings bind to it. -/
def accountFrame : Bytes := "DREGG/OBJECTIVE/ACTIVITY/FEE-ACCOUNT/v1".toUTF8.toList
def accountCodec := framed accountFrame StreamCodec.nat
def balanceBytes (balance : Nat) : Bytes := accountCodec.encode balance
def decodeBalance (bytes : Bytes) : Option Nat := accountCodec.decode bytes

/-! ## Cell and claim identities -/

def recordCell (object : CellId) (activity : Digest) : CellId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/RECORD-CELL/v1" (digestStream.encode object ++ digestStream.encode activity)

def accountCell (payer : SubjectId) : CellId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/FEE-ACCOUNT-CELL/v1" (subjectStream.encode payer)

def packageCell (pin : Digest) : CellId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/PACKAGE-CELL/v1" (digestStream.encode pin)

def activityId (object : CellId) (birth : TransactionId) : Digest :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/ID/v1" (digestStream.encode object ++ digestStream.encode birth)

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

/-! ## Configuration and fees -/

/-- The public price of a DECLARED envelope of ticks. -/
structure Tariff where
  base : Nat
  perTick : Nat
  deriving DecidableEq, Repr

def Tariff.price (tariff : Tariff) (ticks : Nat) : Nat := tariff.base + tariff.perTick * ticks

structure Config where
  limits : Limits
  planBudget : Budget
  maxTicks : Nat
  maxPatience : Nat
  typeFuel : Nat
  maxArtifactBytes : Nat
  tariff : Tariff

/-- The escrow of the fee pair for one await. -/
def escrowOf (tariff : Tariff) (payer : SubjectId) (resumeTicks timeoutTicks : Nat) : Escrow :=
  ⟨payer, resumeTicks, timeoutTicks, tariff.price resumeTicks, tariff.price timeoutTicks⟩

def Escrow.pair (escrow : Escrow) : Nat := escrow.resumeFee + escrow.timeoutFee

/-- How an await ended: by its outcome (reply, refusal, unknown, broken, a due
height) or by its deadline. -/
inductive Path where
  | resumed
  | timedOut
  deriving DecidableEq, Repr

/-- The fee the ending turn uses, and the one returned. Functions of the escrow
and the path only. -/
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
  | accountMissing (payer : SubjectId) | unfunded (payer : SubjectId) (balance needed : Nat)
  | notOwner
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
`conflict` added: B2). -/
inductive AwaitOutcome where
  | reply (value : Data)
  | refused
  | unknown
  | timedOut
  | broken
  | upgraded
  | conflict (stale : Nat)
  deriving Repr

def AwaitOutcome.label : AwaitOutcome → String
  | .reply _ => "reply" | .refused => "refused" | .unknown => "unknown" | .timedOut => "timedOut"
  | .broken => "broken" | .upgraded => "upgraded" | .conflict _ => "conflict"

/-- The response datum the activity is resumed with. -/
def AwaitOutcome.data : AwaitOutcome → Data
  | .reply value => .variant "reply" value
  | .conflict stale => .variant "conflict" (.record [("stale", .natural stale)])
  | other => .variant other.label (.record [])

/-- The kernel's own outcomes, which every activity's response type must type
at birth (a reply is typed when it is decided). -/
def kernelOutcomes : List AwaitOutcome :=
  [.refused, .unknown, .timedOut, .broken, .upgraded, .conflict 0]

/-- The type a reply must have: the `reply` member of the response sum. -/
def replyType (assumptions : Assumptions) (response : Ty) : Option Ty :=
  match unalias assumptions.bounds response with
  | .variant row => row.lookup assumptions.bounds 64 "reply"
  | _ => none

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

/-! ## Plans the kernel performs -/

inductive PlanSource where
  | reply (decider : SubjectId)
  | height (due : Nat)
  deriving DecidableEq, Repr

/-- A yielded Plan: `await {state, on, patience}`. The declared state is
written to the object; `on` names what the activity waits for; the deadline is
the yield height plus `patience`. -/
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

/-- What one segment of an activity ends in. A yield keeps the EXACT yielded
machine state (the Plan is extracted from a copy). -/
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
      pure (.yielded yielded plan)
    | .error (failure, _) => .error (.planExtraction (reprStr failure))
  | .finished _ finished =>
    match ObjectiveBendDemandData.complete config.limits config.planBudget finished with
    | .ok result => .ok (.finished result.value)
    | .error (failure, _) => .error (.resultExtraction (reprStr failure))
  | .divergent _ _ => .ok (.faulted "divergent")
  | .refused reason _ => .ok (.faulted (reprStr reason))
  | .suspended _ _ => .error .exhausted

/-! ## Turns -/

abbrev Snapshot (rootBytes : Bytes → Digest) := DataSnapshot rootBytes

def postAt {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) (bytes : Bytes) : Post :=
  ⟨cell, snapshot.model.roots cell, bytes⟩

def guardAt {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : ReadGuard :=
  ⟨cell, snapshot.model.roots cell⟩

def balanceAt {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (payer : SubjectId) :
    Except Refusal Nat :=
  match decodeBalance (snapshot.canonicalBytes (accountCell payer)) with
  | some balance => .ok balance
  | none => .error (.accountMissing payer)

/-- Movements merged per payer: one (payer, debit, credit) per distinct payer. -/
def aggregate : List (SubjectId × Nat × Nat) → List (SubjectId × Nat × Nat)
  | [] => []
  | (payer, debit, credit) :: rest =>
    let merged := aggregate rest
    match merged.find? (fun entry => entry.1 == payer) with
    | some (_, debits, credits) =>
      (payer, debit + debits, credit + credits) :: merged.filter (fun entry => entry.1 != payer)
    | none => (payer, debit, credit) :: merged

/-- Account posts for a set of (payer, debit, credit) movements, one post per
distinct payer, refused when a balance would go negative. -/
def accountPosts {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes)
    (entries : List (SubjectId × Nat × Nat)) : Except Refusal (List Post) :=
  (aggregate entries).mapM fun (payer, debit, credit) => do
    let balance ← balanceAt snapshot payer
    if balance + credit < debit then throw (.unfunded payer (balance + credit) debit)
    pure (postAt snapshot (accountCell payer) (balanceBytes (balance + credit - debit)))

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
  let stateBytes := dataBytes plan.state
  let statePost := postAt snapshot object stateBytes
  let reads : List ReadGuard := [⟨object, rootBytes stateBytes⟩]
  match plan.source with
  | .reply decider =>
    let slotName := AnswerSlot.name transaction cell generation
    let slotCell := AnswerSlot.cell slotName
    if (AnswerSlot.decode (snapshot.canonicalBytes slotCell)).isSome then throw .slotFresh
    let slot : AnswerSlot.Slot := ⟨slotName, cell, decider, deadline, .opened⟩
    pure ⟨⟨id, .reply slotName decider, deadline, height⟩,
      [statePost, postAt snapshot slotCell (AnswerSlot.encode slot)], reads⟩
  | .height due =>
    if deadline < due then throw (.plan "a height await is due after its deadline")
    pure ⟨⟨id, .height due, deadline, height⟩, [statePost], reads⟩

/-- The record that ends a segment, and the escrow it posts. -/
def nextRecord (base : Record) (escrow : Escrow) (generation : Nat) :
    Segment → Option YieldCommit → Record
  | .yielded state _, some yielded =>
    let encoded := checkpointBytes state
    { base with
      generation := generation
      checkpoint := encoded
      checkpointDigest := ObjectiveActivityWire.checkpointDigest encoded
      reads := yielded.reads
      escrow := escrow
      phase := .awaiting yielded.await }
  | .finished result, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      reads := []
      escrow := ⟨escrow.payer, escrow.resumeTicks, escrow.timeoutTicks, 0, 0⟩
      phase := .done (dataBytes result) }
  | .faulted reason, _ =>
    { base with
      generation := generation
      checkpoint := []
      checkpointDigest := ObjectiveActivityWire.checkpointDigest []
      reads := []
      escrow := ⟨escrow.payer, escrow.resumeTicks, escrow.timeoutTicks, 0, 0⟩
      phase := .faulted reason }
  | .yielded _ _, none =>
    { base with generation := generation, phase := .faulted "internal: yield without commit" }

/-- The escrow a segment posts: the pair, when it yielded. -/
def pairOf (escrow : Escrow) : Option YieldCommit → Nat
  | some _ => escrow.pair
  | none => 0

/-- The yield commit of a segment, when it yielded. -/
def segmentCommit {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell object : CellId) (generation : Nat) :
    Segment → Except Refusal (Option YieldCommit)
  | .yielded state plan => do
    let committed ← commitYield config snapshot height transaction cell object generation
      (checkpointDigest (checkpointBytes state)) plan
    pure (some committed)
  | _ => pure none

/-! ### publish -/

/-- The output codec an activity artifact names: its entry returns an
`Activity<P,R,A>`, never a native method result. -/
def codecId : Digest := tagged "DREGG/OBJECTIVE/ACTIVITY/OUTPUT-CODEC/v1" []

def publishTransaction (pin : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/PUBLISH/v1" (digestStream.encode pin)

def publish {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (subject : SubjectId) (artifactBytes : Bytes) : Except Refusal (Digest × DataIntent rootBytes) := do
  let some artifact := ObjectiveBendSourceArtifact.decode artifactBytes | throw .packageMissing
  if artifact.outputCodec ≠ codecId then throw (.packageType "not an activity artifact")
  let pin := ObjectiveBendSourceArtifact.identity artifact
  let cell := packageCell pin
  if (ObjectiveBendSourceArtifact.decode (snapshot.canonicalBytes cell)).isSome then throw .packageExists
  let definition ← match ObjectiveBendSourceArtifact.checkWithin artifact config.maxArtifactBytes config.typeFuel with
    | .ok checked => pure checked
    | .error reason => throw (.packageType reason)
  match callable definition.typed.type with
  | .arrow _ _ _ (.computation _ _ _) => pure ()
  | _ => throw (.packageType "an activity package selects a definition `Input -> Activity<P,R,A>`")
  let transaction := publishTransaction pin
  pure (pin, intentOf rootBytes transaction [postAt snapshot cell artifactBytes] [] []
    (event "publish" (digestStream.encode pin)) (some subject))


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

def birthTransaction (request : BirthRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/BIRTH/v1"
    (subjectStream.encode request.subject ++ digestStream.encode request.object ++
      digestStream.encode request.pin ++ bytesStream.encode (dataBytes request.input) ++
      StreamCodec.nat.encode request.nonce)

/-- An admitted birth: the program, its first segment from its initial state,
and the one intent that commits the record, the yield and the escrow. -/
structure Birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) where
  private mk ::
  program : Program config request.pin request.input
  programExact : loadProgram config (snapshot.canonicalBytes (packageCell request.pin)) request.pin request.input =
    .ok program
  cell : CellId
  cellExact : cell = recordCell request.object (activityId request.object (birthTransaction request))
  segment : Segment
  segmentExact : runSegment config request.ticks (initial program.applied.erase) = .ok segment
  yielded : Option YieldCommit
  yieldedExact : segmentCommit config snapshot height (birthTransaction request) cell request.object 0 segment =
    .ok yielded
  record : Record
  recordExact : record = nextRecord
    ⟨request.object, activityId request.object (birthTransaction request), request.pin, dataBytes request.input,
      0, [], checkpointDigest [], [], escrowOf config.tariff request.subject request.resumeTicks request.timeoutTicks,
      .faulted "unborn"⟩
    (escrowOf config.tariff request.subject request.resumeTicks request.timeoutTicks) 0 segment yielded
  posts : List Post
  recordPost : posts.head? = some (postAt snapshot cell (encodeRecord record))
  intent : DataIntent rootBytes
  intentExact : intent = intentOf rootBytes (birthTransaction request) posts
    [guardAt snapshot (packageCell request.pin)] []
    (event "birth" (digestStream.encode (birthTransaction request) ++ StreamCodec.nat.encode height))
    (some request.subject)

def birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) : Except Refusal (Birth config snapshot height request) := do
  if config.maxTicks < request.ticks then throw (.envelope request.ticks config.maxTicks)
  if config.maxTicks < request.resumeTicks then throw (.envelope request.resumeTicks config.maxTicks)
  if config.maxTicks < request.timeoutTicks then throw (.envelope request.timeoutTicks config.maxTicks)
  match programExact : loadProgram config (snapshot.canonicalBytes (packageCell request.pin)) request.pin request.input with
  | .error reason => throw reason
  | .ok program =>
    for outcome in kernelOutcomes do
      if (typeData program.assumptions config.typeFuel outcome.data program.responseType).isNone then
        throw (.outcomeProtocol outcome.label)
    let transaction := birthTransaction request
    let activity := activityId request.object transaction
    let cell := recordCell request.object activity
    if (decodeRecord (snapshot.canonicalBytes cell)).isSome then throw .recordExists
    match segmentExact : runSegment config request.ticks (initial program.applied.erase) with
    | .error reason => throw reason
    | .ok segment =>
      match yieldedExact : segmentCommit config snapshot height transaction cell request.object 0 segment with
      | .error reason => throw reason
      | .ok yielded =>
        let escrow := escrowOf config.tariff request.subject request.resumeTicks request.timeoutTicks
        let base : Record := ⟨request.object, activity, request.pin, dataBytes request.input, 0, [],
          checkpointDigest [], [], escrow, .faulted "unborn"⟩
        let record := nextRecord base escrow 0 segment yielded
        let accounts ← accountPosts snapshot
          [(request.subject, config.tariff.price request.ticks + pairOf escrow yielded, 0)]
        let posts := postAt snapshot cell (encodeRecord record) ::
          ((yielded.map YieldCommit.posts).getD [] ++ accounts)
        pure ⟨program, programExact, cell, rfl, segment, segmentExact, yielded, yieldedExact, record, rfl,
          posts, rfl, _, rfl⟩

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
    let some record := decodeRecord (snapshot.canonicalBytes activity) | throw .recordMissing
    let .awaiting await := record.phase | throw .notAwaiting
    let .reply named _ := await.source | throw .slotMismatch
    if named ≠ slot then throw .slotMismatch
    let some input := decodeDataBytes record.input | throw .inputType
    let program ← loadProgram config (snapshot.canonicalBytes (packageCell record.pin)) record.pin input
    match typeData program.assumptions config.typeFuel value program.reply with
    | some _ => pure ()
    | none => throw (.responseType "reply")
  | _ => pure ()

structure Resolution {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ResolveRequest) where
  private mk ::
  slot : AnswerSlot.Slot
  slotExact : AnswerSlot.decode (snapshot.canonicalBytes (AnswerSlot.cell request.slot)) = some slot
  named : slot.name = request.slot
  decided : AnswerSlot.Slot
  decidedExact : AnswerSlot.decide slot request.subject height request.answer.decision = .ok decided
  typed : replyTyped config snapshot slot.activity request.slot request.answer = .ok ()
  intent : DataIntent rootBytes
  intentExact : intent = intentOf rootBytes (resolveTransaction request.slot)
    [postAt snapshot (AnswerSlot.cell request.slot) (AnswerSlot.encode decided)]
    [guardAt snapshot slot.activity] [AnswerSlot.decisionClaim request.slot]
    (event "resolve" (digestStream.encode request.slot ++ StreamCodec.nat.encode height)) (some request.subject)

def resolve {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : ResolveRequest) : Except Refusal (Resolution config snapshot height request) :=
  match slotExact : AnswerSlot.decode (snapshot.canonicalBytes (AnswerSlot.cell request.slot)) with
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
def settle {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (height : Nat)
    (cell : CellId) (await : Await) : Except Refusal Settlement :=
  match await.source with
  | .reply slotName _ =>
    let slotCell := AnswerSlot.cell slotName
    match AnswerSlot.decode (snapshot.canonicalBytes slotCell) with
    | none => .error .slotMissing
    | some slot =>
      if slot.name ≠ slotName ∨ slot.activity ≠ cell then .error .slotMismatch else
      match slot.phase with
      | .decided decision _ => do
        let outcome ← outcomeOfDecision decision
        pure ⟨if decision = .expired then .timedOut else .resumed, outcome, [], [guardAt snapshot slotCell], []⟩
      | .opened =>
        match AnswerSlot.expire slot height with
        | .ok expired => .ok ⟨.timedOut, .timedOut, [postAt snapshot slotCell (AnswerSlot.encode expired)], [],
            [AnswerSlot.decisionClaim slotName]⟩
        | .error _ => .error (.notYetDecided await.deadline height)
  | .height due =>
    if await.deadline < height then .ok ⟨.timedOut, .timedOut, [], [], []⟩
    else if due ≤ height then .ok ⟨.resumed, .reply (.record [("at", .natural height)]), [], [], []⟩
    else .error (.notYetDue due height)

/-- The number of recorded reads whose cell moved since the yield. -/
def staleCount {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (reads : List ReadGuard) : Nat :=
  (reads.filter (fun guard => snapshot.model.roots guard.cellId != guard.expectedRoot)).length

def revalidate (stale : Nat) (decided : AwaitOutcome) : AwaitOutcome :=
  if stale = 0 then decided else .conflict stale

/-- No state, no checkpoint and no outcome is ever taken from a request: the
submitter names the record and may add envelope it pays for. -/
structure DeliverRequest where
  subject : SubjectId
  record : CellId
  extraTicks : Nat

def movements (config : Config) (record : Record) (path : Path) (pair : Nat) (request : DeliverRequest) :
    List (SubjectId × Nat × Nat) :=
  (record.escrow.payer, pair, record.escrow.unused path) ::
    (if request.extraTicks = 0 then [] else [(request.subject, config.tariff.price request.extraTicks, 0)])

structure Delivery {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : DeliverRequest) where
  private mk ::
  record : Record
  recordExact : decodeRecord (snapshot.canonicalBytes request.record) = some record
  located : request.record = recordCell record.object record.activity
  await : Await
  awaiting : record.phase = .awaiting await
  idExact : await.id = awaitId request.record record.generation record.checkpointDigest
  digestExact : checkpointDigest record.checkpoint = record.checkpointDigest
  input : Data
  inputExact : decodeDataBytes record.input = some input
  program : Program config record.pin input
  programExact : loadProgram config (snapshot.canonicalBytes (packageCell record.pin)) record.pin input = .ok program
  settlement : Settlement
  settled : settle snapshot height request.record await = .ok settlement
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
  nextExact : next = nextRecord record
    (escrowOf config.tariff record.escrow.payer record.escrow.resumeTicks record.escrow.timeoutTicks)
    (record.generation + 1) segment yielded
  accounts : List Post
  accountsExact : accountPosts snapshot (movements config record settlement.path
    (pairOf (escrowOf config.tariff record.escrow.payer record.escrow.resumeTicks record.escrow.timeoutTicks) yielded)
    request) = .ok accounts
  posts : List Post
  recordPost : posts.head? = some (postAt snapshot request.record (encodeRecord next))
  intent : DataIntent rootBytes
  intentExact : intent = intentOf rootBytes (deliveryTransaction await.id) posts
    (guardAt snapshot (packageCell record.pin) ::
      (settlement.guards ++ record.reads.map (fun guard => guardAt snapshot guard.cellId)))
    (awaitClaim await.id :: settlement.claims)
    (event "deliver" (digestStream.encode await.id ++ StreamCodec.nat.encode height ++
      stringStream.encode outcome.label ++ StreamCodec.nat.encode envelope))
    (some request.subject)

def deliver {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : DeliverRequest) : Except Refusal (Delivery config snapshot height request) :=
  match recordExact : decodeRecord (snapshot.canonicalBytes request.record) with
  | none => .error .recordMissing
  | some record =>
  if located : request.record = recordCell record.object record.activity then
  match awaiting : record.phase with
  | .done _ | .faulted _ => .error .notAwaiting
  | .awaiting await =>
  if idExact : await.id = awaitId request.record record.generation record.checkpointDigest then
  if digestExact : checkpointDigest record.checkpoint = record.checkpointDigest then
  match inputExact : decodeDataBytes record.input with
  | none => .error .inputType
  | some input =>
  match programExact : loadProgram config (snapshot.canonicalBytes (packageCell record.pin)) record.pin input with
  | .error reason => .error reason
  | .ok program =>
  match settled : settle snapshot height request.record await with
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
  let escrow := escrowOf config.tariff record.escrow.payer record.escrow.resumeTicks record.escrow.timeoutTicks
  let next := nextRecord record escrow (record.generation + 1) segment yielded
  match accountsExact : accountPosts snapshot
      (movements config record settlement.path (pairOf escrow yielded) request) with
  | .error reason => .error reason
  | .ok accounts =>
  let posts := postAt snapshot request.record (encodeRecord next) ::
    (settlement.posts ++ (yielded.map YieldCommit.posts).getD [] ++ accounts)
  .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program, programExact,
    settlement, settled, outcome, rfl, response, state, stateExact, resumed, resumeExact, envelope, rfl,
    segment, segmentExact, yielded, yieldedExact, next, rfl, accounts, accountsExact, posts, rfl, _, rfl⟩
  else .error .checkpointDigest
  else .error .awaitMismatch
  else .error .recordMisplaced

/-! ### writeState -/

structure StateWriteRequest where
  subject : SubjectId
  record : CellId
  value : Data
  nonce : Nat

def writeState {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (request : StateWriteRequest) :
    Except Refusal (DataIntent rootBytes) := do
  let some record := decodeRecord (snapshot.canonicalBytes request.record) | throw .recordMissing
  if request.subject ≠ record.escrow.payer then throw .notOwner
  let transaction := tagged "DREGG/OBJECTIVE/ACTIVITY/TX/STATE/v1"
    (digestStream.encode request.record ++ StreamCodec.nat.encode request.nonce ++ dataBytes request.value)
  pure (intentOf rootBytes transaction [postAt snapshot record.object (dataBytes request.value)]
    [guardAt snapshot request.record] [] (event "state" (digestStream.encode transaction)) (some request.subject))

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

theorem Delivery.spends {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    awaitClaim delivery.await.id ∈ delivery.intent.nullifiers := by
  rw [delivery.intentExact]; simp

/-- **Consume-once.** Once a delivery of an await installs, no second turn that
ends that await (another delivery, a timeout, a forged intent claiming it) is
ever accepted, and the exact retry of the delivery replays. -/
theorem resume_consumes_once {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (installed : DurableDataIntent.execute .complete snapshot delivery.intent = .accepted next) :
    (∀ (later : DataIntent rootBytes), awaitClaim delivery.await.id ∈ later.nullifiers →
      ∀ schedule after, DurableDataIntent.execute schedule next later ≠ .accepted after) ∧
    (∀ schedule, DurableDataIntent.execute schedule next delivery.intent = .replayed delivery.intent.erase) :=
  ⟨fun later again schedule after =>
      spent_claim_never_accepted delivery.spends installed later again schedule after,
    installed_retry_replays installed⟩

/-- A delivery from the post-state of a delivery of the same record can never
again end the await it ended: the await it would spend is a different one, so
the record moved (the generation advanced), or the record is no longer awaiting. -/
theorem second_delivery_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height later : Nat} {request again : DeliverRequest} (first : Delivery config snapshot height request)
    (installed : DurableDataIntent.execute .complete snapshot first.intent = .accepted next)
    (second : Delivery config next later again) (sameAwait : second.await.id = first.await.id) :
    DurableDataIntent.execute .complete next second.intent ≠ .accepted next ∧
      ∀ schedule after, DurableDataIntent.execute schedule next second.intent ≠ .accepted after := by
  have spent := (resume_consumes_once first installed).1 second.intent (sameAwait ▸ second.spends)
  exact ⟨spent .complete next, spent⟩

/-- **The slot is decided once.** -/
theorem slot_decided_once {rootBytes : Bytes → Digest} {config : Config} {snapshot next : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request)
    (installed : DurableDataIntent.execute .complete snapshot resolution.intent = .accepted next)
    (later : DataIntent rootBytes) (again : AnswerSlot.decisionClaim request.slot ∈ later.nullifiers)
    (schedule : DurableCommitProtocol.Schedule) (after : Snapshot rootBytes) :
    DurableDataIntent.execute schedule next later ≠ .accepted after :=
  spent_claim_never_accepted (by rw [resolution.intentExact]; simp) installed later again schedule after

/-- **Exactly one decider.** An admitted resolution was made by the slot's
decider, on an open slot, at or before its deadline. -/
theorem slot_single_decider {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest} (resolution : Resolution config snapshot height request) :
    request.subject = resolution.slot.decider ∧ resolution.slot.phase = .opened ∧
      height ≤ resolution.slot.deadline :=
  let decided := AnswerSlot.decide_single_decider resolution.decidedExact
  ⟨decided.1, decided.2.1, decided.2.2.1⟩

/-- **Stale reads deliver `conflict`.** If any read the activity recorded at
its yield has moved, the activity is resumed with `conflict`, never with the
bare outcome, and the count it receives is positive. -/
theorem stale_reads_conflict {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (moved : ∃ guard ∈ delivery.record.reads, snapshot.model.roots guard.cellId ≠ guard.expectedRoot) :
    ∃ stale, 0 < stale ∧ delivery.outcome = .conflict stale := by
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
      decodeRecord (snapshot.canonicalBytes request.record) = some record ∧
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

/-- **No refund depends on computation.** The fee returned to the payer when an
await ends is the unused half of its escrowed pair, chosen by how the await
ended (settled from the snapshot and height) and nothing else: two deliveries
of the same record at the same snapshot and height return the same amount,
whatever envelopes they declared and whatever their runs did. -/
theorem refund_measurement_free {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {first second : DeliverRequest} (one : Delivery config snapshot height first)
    (two : Delivery config snapshot height second) (sameRecord : first.record = second.record) :
    (movements config one.record one.settlement.path 0 first).head? =
        some (one.record.escrow.payer, 0, one.record.escrow.unused one.settlement.path) ∧
      one.record.escrow.unused one.settlement.path = two.record.escrow.unused two.settlement.path := by
  have records : one.record = two.record := by
    have := one.recordExact; rw [sameRecord, two.recordExact] at this; exact (Option.some.inj this).symm
  have awaits : one.await = two.await := by
    have a := one.awaiting; have b := two.awaiting; rw [records, b] at a
    exact (Phase.awaiting.inj a).symm
  have settlements : one.settlement = two.settlement := by
    have a := one.settled; have b := two.settled
    rw [sameRecord, awaits, b] at a; exact (Except.ok.inj a).symm
  exact ⟨rfl, by rw [records, settlements]⟩

/-- The submitter's charge for added envelope is the public price of what it
DECLARED, never of what ran. -/
theorem submitter_charge_declared (config : Config) (record : Record) (path : Path) (pair : Nat)
    (request : DeliverRequest) (extra : 0 < request.extraTicks) :
    (request.subject, config.tariff.price request.extraTicks, 0) ∈ movements config record path pair request := by
  simp [movements, Nat.pos_iff_ne_zero.mp extra]

#assert_axioms record_roundTrip
#assert_axioms TypedData.typed
#assert_axioms execute_accepted_install
#assert_axioms spent_claim_never_accepted
#assert_axioms installed_retry_replays
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
end Minidregg.Kernel.ObjectiveActivity
