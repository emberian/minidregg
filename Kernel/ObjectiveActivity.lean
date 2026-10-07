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

Kernel turns; each is ONE `DataIntent` built by `intentOf` with the sealing of
the receiver that admitted it (`ObjectiveActivityReceiver`: the signed marker,
the authority guards, the replay event), so its writes commit all together or
not at all (`DurableDataIntent.execute_no_partial_data_commit`):

* `publish`: an activity artifact AND the source package it names (and the
  payer funding the cell's retention, a registered Book account read under a
  guard of the Book cell) into the artifact's content-addressed package cell, only after the kernel re-ran the Lean
  front end on the package and the artifact's typed core is that replay's
  rendering (`ObjectiveBendPublication.Replayed`). Every later turn reloads the
  pair and replays again (`loadProgram`): the term an activity runs is the front
  end's output on the stored sources, never a parse of the core bytes.
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
* `create`: a holder of the object resource installs its `ObjectRecord`
  (`Kernel.ObjectRecord`: pin, declared state type, law, upgrade policy, payer, live
  counters, phase) at its own protected coordinate (`objectCell`), and optionally the
  object's INITIAL declared state (`seed`), the state cell's first and only write of the
  creation, judged by the creator's law alone and typed at the declared state type
  (`create_seed_judged`, `create_seed_refused_names_clause`). There is no direct write of
  declared state after that: it changes only by the object's own package (a birth, a
  delivery, a call frame, a delivered message), under the pin.

Counters. The object record counts its awaiting activities (`ObjectRecord.live`,
`rebirths`, by `ObjectRecord.classOf`): a birth that leaves its activity awaiting
writes the record with `retain`, a turn that ends an awaiting activity (an ending
delivery, an abandonment) writes it with `release` (`recount`, `countPosts`); a
delivery that yields again leaves the record unwritten. The upgrade turns read
these counters (the kernel cannot enumerate the record cells of an object).

Objects. A cell is an object to the kernel exactly when it has a record. A
birth on any other cell is refused by name (`birth_refuses_non_object`), and a
birth runs only the package the object pins (`birth_refuses_other_pin`). Every
declared-state write (a birth's or a delivery's yield, a direct write) is judged
by the object's law over the old and new state plus the request facts
(`ObjectRecord.admitWrite`), with the record read in the same turn and its cell
guarded (a seed is judged at creation by the creator's law alone). The judged law is `ObjectRecord.effectiveLaw`: the KERNEL's package-pin clause
(`ObjectRecord.pinClause`: the write is made by code of the package the record pins) first,
then the creator's law. The clause is derived from the record's `pin`, never stored, so a
creator cannot omit it (`create_installs_pin`, `pin_in_every_judged_law`), no declared-state
write exists that no package makes (every one is a birth, delivery, call frame or message
below), the package's own turns pass it
(`Birth.write_passes_pin`, `Delivery.write_passes_pin`, `ObjectiveCall.invocation_writes_pinned`,
`ObjectiveSend.MessageDelivery.writes_pinned`) and no turn but a creation rewrites the record
it comes from (`pin_not_removable`). A delivery's write is judged with the activity's principal (its birth
subject) as subject, never the deliverer. A law refusal refuses the whole turn
and names the clause: nothing commits, and the activity stays at its yield
(`Birth.write_judged`, `Delivery.write_judged`).

Fees are Book postings in the deployment's credit asset. An activity's purse is
a Book account of its own, `heldAccount cell` (the record cell's id), registered
by the birth. Every turn that runs Core4 pays the public price of its DECLARED
envelope (`ObjectiveTariff.Tariff.workOf`, the native tariff) to the collector. A yield reserves, in the purse, the
fee pair of the await (`resumeFee`, `timeoutFee`): exactly one of the pair pays
the turn that ends the await, the other stays in the purse, and the purse is
returned to the payer's account when the activity ends. A yield also reserves
the record's STORAGE DEPOSIT (`storageDeposit`: the deployment's rate per byte of
the record the yield retains, re-priced at every yield). A yield the purse cannot
reserve is refused (the activity stays parked at its previous yield until a
`topUp`). The turn that ends an activity (an ending delivery or birth, an
abandonment) RETIRES its record cell (`retiredImage`, the registry's retired
lifecycle image: the World's `retires`, never reused), sweeps every asset the purse
holds to the payer's account, and DEREGISTERS the purse on the Book in the same
batch (`Batch.deregistrations`): after it, any posting naming the purse is refused
by the Book by name, and the deposit has left only with the record. Every posting is one `CanonicalResourceKernel.Batch`, admitted on the
loaded Book (`AcceptedBatch`), so every turn conserves every asset
(`Birth.conserves`, `Delivery.conserves`). No amount depends on how much
computation ran (`refund_measurement_free`). -/
import Kernel.AnswerSlot
import Compiler.ObjectiveBendSourceArtifact
import Compiler.ObjectiveBendPublication
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
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook AcceptedBatch
  deregisterAccounts applyOperations registerAccounts)
open Minidregg.Kernel.ObjectState (encodeObjectState decodeObjectState)
open Minidregg.Kernel.ObjectRecord (ObjectRecord Facts WriteRefusal admitWrite)
open Minidregg.Kernel.ObjectiveTariff (Tariff zeroCapacity addCapacity)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
open Minidregg.Kernel.ObjectStateType (typedAt)
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
install the role, and every intent from outside the kernel activity that writes
a coordinate in the protected space is refused by name
(`ObjectiveActivityGate.ordinaryGate`, `protectedWrite`). -/

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

/-- What a package cell holds: the activity artifact's bytes, the bytes of the source
package the artifact names, and the payer: the Book account that funds the cell's
retention (never authority over it). -/
structure Stored where
  artifact : Bytes
  package : Bytes
  payer : AccountId
  deriving DecidableEq, Repr

def storedStream : StreamCodec Stored :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream StreamCodec.nat))
    (fun p => (p.artifact, p.package, p.payer)) (fun w => ⟨w.1, w.2.1, w.2.2⟩) (by intro p; cases p; rfl)

def storedFrame : Bytes := "DREGG/OBJECTIVE/ACTIVITY-PACKAGE/v1".toUTF8.toList
def storedCodec := framed storedFrame storedStream
def encodeStored (stored : Stored) : Bytes := storedCodec.encode stored
def decodeStored (bytes : Bytes) : Option Stored := storedCodec.decode bytes

theorem stored_roundTrip (stored : Stored) : decodeStored (encodeStored stored) = some stored :=
  framed_roundTrip _ _ stored

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
  /-- The storage deposit per byte of a retained activity record: every yield
  reserves `storageRate * |encodeRecord record|` in the purse beside the fee pair. -/
  storageRate : Nat

/-- A declared envelope covers what the kernel spends on a turn: its source
ticks are within the ceiling, and it declares at least the kernel's fixed heap,
stack, type-checking fuel and Plan extraction output sizes, so the whole turn's work
(the run, the per-turn package check, the extraction) is in the price. The extraction's
tick budget is checked by name right after (`extractUncovered`). -/
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
  /-- The source package is absent, not canonical, names another artifact or another front
  end, or selects another declaration. -/
  | packageSource (reason : String)
  /-- The front end's replay of the package refused, or its rendering is not the artifact's
  typed core. -/
  | packageReplay (reason : String)
  | inputType | outcomeProtocol (label : String)
  | recordExists | recordMissing | recordMisplaced | notAwaiting | awaitMismatch | checkpointDigest | checkpointCodec
  /-- The record cell is retired: its activity ended (or was abandoned) and the
  coordinate holds the registry's retired image; it is never read or reborn. -/
  | recordRetired
  | patience (patience maximum : Nat)
  /-- A declared envelope does not cover the turn (`Config.covers`). -/
  | uncovered (envelope : Capacity)
  /-- A resumed run's declared envelope does not cover its heap: the stored checkpoint's
  cells plus the deployment's per-segment allocation (`segmentLimits`). The submitter adds
  heap to the envelope (`extra`, priced by the tariff, paid by the submitter). -/
  | heapUncovered (needed declared : Nat)
  /-- A declared envelope does not cover the deployment's extraction tick budget
  (`planBudget.ticks`): the forcing a Plan or result extraction may do is validator work,
  declared (`Capacity.extractTicks`) and priced by the tariff like the run's own ticks. -/
  | extractUncovered (needed declared : Nat)
  | plan (reason : String) | messageAwaitNeedsInbox
  | planExtraction (reason : String) | resultExtraction (reason : String)
  | exhausted
  | responseType (label : String)
  | slotMissing | slotFresh | slotMismatch | slot (reason : AnswerSlot.Refusal)
  /-- The slot cell is retired: its await settled or was abandoned. -/
  | slotRetired
  | notYetDecided (deadline height : Nat) | notYetDue (due height : Nat)
  /-- The Book is not a live Book cell at the deployment's Book id. -/
  | bookUnavailable
  /-- The purse is already a Book account (a second birth of one record). -/
  | purseTaken
  /-- The payer is the issuer well, the collector or the purse itself. -/
  | payerInvalid
  /-- The deposit cannot reserve the first await's fee pair and storage deposit. -/
  | underfunded (deposit reserve : Nat)
  /-- The purse cannot reserve the next await's fee pair and its record's storage
  deposit: the activity stays parked at its yield until a `topUp`. -/
  | awaitsFunding (available reserve : Nat)
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
  /-- A creation seeds the declared state of an object whose state cell already exists. -/
  | stateExists

  /-- A creation declares a state type that is not first-order data (`Ty.isData`). -/
  | stateTypeNotData
  /-- The object drains toward an upgrade whose migration is not the identity (or
  whose old state type is not a value subtype of the new): no new birth or call
  until MIGRATE; a message to it waits in its inbox. -/
  | draining
  /-- The activity is pinned to a package the object no longer runs: it was chosen
  for REBIRTH and waits for its rebirth turn. -/
  | awaitingRebirth
  /-- The migration declaration does not lower, check, or is not `old -> new`. -/
  | migrationShape (reason : String)
  /-- The migration did not run to a value within its declared envelope. -/
  | migrationFault (reason : String)
  /-- An ADOPT on a `frozen` object. -/
  | frozen
  /-- An ADOPT whose request facts the policy's authority does not admit. -/
  | notUpgradeAuthority
  /-- An ADOPT whose next policy loosens the current one (`UpgradePolicy.permits`). -/
  | policyLoosened
  /-- A floor the next law does not provably entail (the index of the floor): the
  satisfiability decision of `law ∧ ¬floor` returned no checked certificate. -/
  | floorNotEntailed (index : Nat)
  /-- An ADOPT naming the package the object already pins. -/
  | samePin
  /-- An ADOPT while an earlier upgrade's rebirths are still awaiting, or while one drains. -/
  | upgradeUnderWay
  /-- MIGRATE, an abort or a rebirth on an object that is not draining (or not
  migrated, for a rebirth). -/
  | notDraining
  /-- A drain patience outside `1..maxPatience`. -/
  | drainPatience (patience maximum : Nat)
  /-- The identity migration needs the old state type to be a value subtype of the new. -/
  | notSubtype
  /-- Linearity: old fields neither read by the migration nor dropped. -/
  | fieldsForgotten (fields : List String)
  /-- MIGRATE while activities pinned to the old package (and not chosen for rebirth) await. -/
  | liveActivities (count : Nat)
  /-- An abort before the drain deadline. -/
  | notYetDeadline (deadline height : Nat)
  /-- An abort of an activity chosen for rebirth, or a rebirth of one not chosen. -/
  | rebirthDisposition
  /-- A rebirth candidate that is not an awaiting activity of the object on its pin. -/
  | rebirthTarget (reason : String)
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
          -- A recursive sum is declared as its bounded variable: the injection is
          -- annotated AT that variable (the checker's `.variable` inject), so a
          -- nested list position types as its declared name, not its unfolded row.
          (position, ⟨payloadType, (match type with
            | .variable index => .variable index
            | _ => .variant row), .unrestricted, .reusable⟩) ::
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

/-- A package cell's pair, replayed: the artifact (named by the pin) and its source package,
which names this kernel's front end and selects the artifact's declaration, and the front
end's replay of that package, whose rendering is the artifact's typed core. -/
structure Replay (config : Config) (pin : Digest) where
  private mk ::
  artifact : ObjectiveBendSourceArtifact.Artifact
  identity : ObjectiveBendSourceArtifact.identity artifact = pin
  package : ObjectiveSourcePackage.Package
  packageExact : ObjectiveSourcePackage.identity package = artifact.package
  frontEndOwn : package.frontEnd = ObjectiveBendFrontEndIdentity.identity
  declarationExact : ObjectiveSourcePackage.selectedDeclaration package = some artifact.declaration
  replayed : ObjectiveBendPublication.Replayed package artifact.typedCore config.typeFuel

/-- The definition the replay accepted: the elaborator's own term with its annotations. -/
def Replay.source {config : Config} {pin : Digest} (r : Replay config pin) : AnnotatedTerm :=
  r.replayed.accepted.source

def replayPackage (config : Config) (stored : Stored) (pin : Digest) : Except Refusal (Replay config pin) := do
  if stored.artifact.length > config.maxArtifactBytes then throw .packageMissing
  if stored.package.length > config.maxArtifactBytes then throw (.packageSource "package byte capacity")
  let some artifact := ObjectiveBendSourceArtifact.decode stored.artifact | throw .packageMissing
  if identity : ObjectiveBendSourceArtifact.identity artifact = pin then
    let some package := ObjectiveSourcePackage.decode stored.package
      | throw (.packageSource "canonical Objective source package required")
    if packageExact : ObjectiveSourcePackage.identity package = artifact.package then
      if frontEndOwn : package.frontEnd = ObjectiveBendFrontEndIdentity.identity then
        if declarationExact : ObjectiveSourcePackage.selectedDeclaration package = some artifact.declaration then
          match ObjectiveBendPublication.replayAccept package artifact.typedCore config.typeFuel with
          | .ok replayed => pure ⟨artifact, identity, package, packageExact, frontEndOwn, declarationExact, replayed⟩
          | .error d => throw (.packageReplay d.message)
        else throw (.packageSource "the package selects another declaration")
      else throw (.packageSource "the package names another front end")
    else throw (.packageSource "the artifact names another package")
  else throw .packageIdentity

/-- The replayed package of an activity and its instantiation with its input. -/
structure Program (config : Config) (pin : Digest) (input : Data) where
  private mk ::
  definition : Replay config pin
  domain : Ty
  applied : AnnotatedTerm
  appliedExact : applied = ⟨.app definition.source.term input.term,
    fun path => match path with
      | 0 :: rest => definition.source.annotations rest
      | 1 :: rest => annotationsOf (dataAnnotations definition.source.assumptions.bounds 64 input domain []) rest
      | _ => none,
    definition.source.assumptions⟩
  checked : Checked applied []
  planType : Ty
  responseType : Ty
  resultType : Ty
  typeExact : checked.type = .computation planType responseType resultType
  reply : Ty
  replyExact : replyType applied.assumptions responseType = some reply

def Program.assumptions {config : Config} {pin : Digest} {input : Data} (program : Program config pin input) :
    Assumptions := program.applied.assumptions

/-- The package cell body a snapshot holds for a pin (empty when absent). -/
def packageBytes {rootBytes : Bytes → Digest} (config : Config) (snapshot : DataSnapshot rootBytes)
    (pin : Digest) : Bytes :=
  (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain pin))).getD []

/-- A replayed package definition applied to its typed input: the shared prefix
of an activity's program and of a seat contract's one-shot method
(`Kernel.SeatStore`). The stored package is replayed by this kernel's front end
(`replayPackage`), the input is typed at the replayed definition's declared
domain, and the application is checked. -/
structure Instantiated (config : Config) (pin : Digest) (input : Data) where
  private mk ::
  definition : Replay config pin
  domain : Ty
  applied : AnnotatedTerm
  appliedExact : applied = ⟨.app definition.source.term input.term,
    fun path => match path with
      | 0 :: rest => definition.source.annotations rest
      | 1 :: rest => annotationsOf (dataAnnotations definition.source.assumptions.bounds 64 input domain []) rest
      | _ => none,
    definition.source.assumptions⟩
  checked : Checked applied []

/-- Load the artifact and its package from their cell body, replay the front end
on the package (`replayPackage`), instantiate the replayed definition with the
input (typed at the declared domain), and check the instantiation. -/
def instantiate (config : Config) (bytes : Bytes) (pin : Digest) (input : Data) :
    Except Refusal (Instantiated config pin input) := do
  let some stored := decodeStored bytes | throw .packageMissing
  let definition ← replayPackage config stored pin
  let source := definition.source
  match callable definition.replayed.accepted.typed.type with
  | .arrow _ _ domain _ =>
    let applied : AnnotatedTerm := ⟨.app source.term input.term,
      fun path => match path with
        | 0 :: rest => source.annotations rest
        | 1 :: rest => annotationsOf (dataAnnotations source.assumptions.bounds 64 input domain []) rest
        | _ => none,
      source.assumptions⟩
    let some checked := check applied [] config.typeFuel | throw .inputType
    pure ⟨definition, domain, applied, rfl, checked⟩
  | _ => throw (.packageType "the definition takes no input")

/-- Load an activity program: `instantiate`, then the application must be an
`Activity<P,R,A>` whose response protocol has a reply type. -/
def loadProgram (config : Config) (bytes : Bytes) (pin : Digest) (input : Data) :
    Except Refusal (Program config pin input) := do
  let instance_ ← instantiate config bytes pin input
  match typeExact : instance_.checked.type with
  | .computation planType responseType resultType =>
    match replyExact : replyType instance_.applied.assumptions responseType with
    | some reply =>
      pure ⟨instance_.definition, instance_.domain, instance_.applied, instance_.appliedExact, instance_.checked,
        planType, responseType, resultType, typeExact, reply, replyExact⟩
    | none => throw (.outcomeProtocol "reply")
  | _ => throw (.packageType "the definition does not return an Activity")

/-- What a seat contract's method runs is the front end's output on the package
stored with its artifact (as `Program.runs_front_end_output` for an activity). -/
theorem Instantiated.runs_front_end_output {config : Config} {pin : Digest} {input : Data}
    (instance_ : Instantiated config pin input) :
    instance_.definition.package.frontEnd = ObjectiveBendFrontEndIdentity.identity ∧
    ∃ (l : ObjectiveBendFrontEnd.Lowering) (a : ObjectiveBendFrontEnd.Accepted l),
      ObjectiveBendPublication.replay instance_.definition.package = .ok l ∧
      l.packet.compress.toUTF8.toList = instance_.definition.artifact.typedCore ∧
      a.packet.source.term = a.erased ∧
      instance_.applied.term = .app a.erased input.term := by
  let r := instance_.definition.replayed
  refine ⟨instance_.definition.frontEndOwn, r.lowering, r.accepted, r.replayExact, r.coreExact,
    r.accepted.packetTerm, ?_⟩
  rw [instance_.appliedExact]
  simp only [Replay.source, instance_.definition.replayed.accepted.sourceExact]
  rfl

/-- The term an activity runs is the front end's output on the package stored with its
artifact: the package names this kernel's front end, the kernel replayed it, the artifact's
typed core is the replay's rendering, and the program applies the elaborator's erased term
(whose decoding from the packet is a theorem, `ObjectiveBendTermWire.decode_json`) to its
input. -/
theorem Program.runs_front_end_output {config : Config} {pin : Digest} {input : Data}
    (program : Program config pin input) :
    program.definition.package.frontEnd = ObjectiveBendFrontEndIdentity.identity ∧
    ∃ (l : ObjectiveBendFrontEnd.Lowering) (a : ObjectiveBendFrontEnd.Accepted l),
      ObjectiveBendPublication.replay program.definition.package = .ok l ∧
      l.packet.compress.toUTF8.toList = program.definition.artifact.typedCore ∧
      a.packet.source.term = a.erased ∧
      program.applied.term = .app a.erased input.term := by
  let r := program.definition.replayed
  refine ⟨program.definition.frontEndOwn, r.lowering, r.accepted, r.replayExact, r.coreExact,
    r.accepted.packetTerm, ?_⟩
  rw [program.appliedExact]
  simp only [Replay.source, program.definition.replayed.accepted.sourceExact]
  rfl

#assert_axioms Program.runs_front_end_output Instantiated.runs_front_end_output

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

/-- What one segment of an activity ends in. A yield stores the state the Plan
extraction left (`ObjectiveBendDemandData.yieldedPlan`: the yielded control and
stack over the heap in which every cell the extraction forced is cached), settled
and collected (`ObjectiveBendDemandCollect.checkpoint`: cached cells stop retaining
the closures they were forced from; only what the yielded Plan and the stack reach
is kept, compacted). So a checkpoint is storage-charged for what the continuation
can use: a Plan field the extraction evaluated is stored as its value, never as the
chain of suspended computations that produced it. Resuming the stored state is
resuming the extracted one exactly (`ObjectiveResumeContract.runSegment_checkpoint`);
that resuming the extracted state is resuming the yielded one, each under its own
`segmentLimits`, is `ObjectiveResumeContract.forcingTransparent_of_yieldedPlan` (every
lexically valid yield). -/
inductive Segment where
  | yielded (state : State) (plan : PlanAwait)
  | finished (result : Data)
  | faulted (reason : String)

/-- The limits a segment runs under: `config.limits.heap` cells BEYOND the heap it
starts from, and the deployment's stack. A birth starts from the empty heap, so its
limits are `config.limits`. A resumed segment starts from the stored checkpoint, whose
cells are the activity's live state, already paid for by the storage deposit and, at
delivery, by the declared envelope (`heapUncovered`); they do not eat the segment's own
allocation. This is what makes the stored checkpoint resume exactly as the program's own
yield (`ObjectiveResumeContract.runSegment_stored_complete`, no headroom): the lazy yield,
the forced state, the settled state and the collected checkpoint each get the same room
past their own heap. Under limits counted from zero the claim is FALSE: a checkpoint can be
larger than the yield it was made from, and its size then eats the next segment's room
(`ObjectiveResumeContract.absolute_limits_refuted`). -/
def segmentLimits (config : Config) (start : State) : Limits :=
  ObjectiveBendDemandCollect.limitsPast config.limits start

/-- Run one segment from `start` within a declared envelope, under its `segmentLimits`
(the run, and the Plan or result extraction it ends with). Running out of envelope
commits nothing (`exhausted`): the activity stays where it was. -/
def runSegment (config : Config) (ticks : Nat) (start : State) : Except Refusal Segment :=
  match runBounded (segmentLimits config start) ticks start with
  | .yielded _ yielded =>
    match ObjectiveBendDemandData.yieldedPlan (segmentLimits config start) config.planBudget yielded with
    | .ok extracted => do
      let plan ← decodePlan extracted.value
      pure (.yielded (ObjectiveBendDemandCollect.checkpoint extracted.state) plan)
    | .error (failure, _) => .error (.planExtraction (reprStr failure))
  | .finished _ finished =>
    match ObjectiveBendDemandData.complete (segmentLimits config start) config.planBudget finished with
    | .ok result => .ok (.finished result.value)
    | .error (failure, _) => .error (.resultExtraction (reprStr failure))
  | .divergent _ _ => .ok (.faulted "divergent")
  | .refused reason _ => .ok (.faulted (reprStr reason))
  | .suspended _ _ => .error .exhausted

def Segment.yields : Segment → Bool
  | .yielded _ _ => true
  | _ => false

/-- The refusals a RESUMED segment can meet that its own program causes and
that no later delivery could avoid: resumption is deterministic
(`resume_deterministic`), so each recurs on every delivery of the same await,
the timeout delivery included. Exhaustion is one only at the turn cap; below it,
a delivery (or an `exhaust` turn) with more envelope may still run the segment.
A write that does not fit the declared state (`writeShape`) is the Plan's own
malformation. A write the object's law refuses is NOT a program fault: the law
is the object's, and abandonment past deadline plus grace returns the escrow.
(SCHOLAR-CALLS 8d1d3c0e, ported onto resume-with-view and object records.) -/
def programFault (config : Config) (envelope : Nat) : Refusal → Option String
  | .plan reason => some s!"plan: {reason}"
  | .planExtraction reason => some s!"plan extraction: {reason}"
  | .resultExtraction reason => some s!"result extraction: {reason}"
  | .patience patience maximum => some s!"patience {patience} outside 1..{maximum}"
  | .messageAwaitNeedsInbox => some "a message await needs an inbox"
  | .writeShape reason => some s!"write shape: {reason}"
  | .exhausted => if config.maxTicks ≤ envelope then some s!"no yield within the turn cap {config.maxTicks}" else none
  | _ => none

/-- A program fault ends the segment as `faulted`; any other refusal refuses
the turn. -/
def faultOr (config : Config) (envelope : Nat) {α : Type} (refusal : Refusal) :
    Except Refusal (Segment × Option α) :=
  match programFault config envelope refusal with
  | some reason => .ok (.faulted reason, none)
  | none => .error refusal

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

/-- **The image of a retired cell**: the registry's retired lifecycle image. A
turn that writes it retires the cell (the bridge derives the World's `retires`
from it: the cell is emptied by a guarded leg and its id enters the retired set,
so no turn ever recreates it). It holds no role, key or body: the checkpoint,
the input, the result and every other byte the cell held are gone, and no
reader decodes it (`payloadOf_retired`). -/
def retiredImage : Bytes := LifecycleImage.bytes CanonicalCellRegistry.registry .retired

/-- Whether bytes are the retired image. -/
def isRetired (bytes : Bytes) : Bool :=
  match (LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some .retired => true
  | _ => false

theorem isRetired_retiredImage : isRetired retiredImage = true := by
  unfold isRetired retiredImage
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry .retired =
    (LifecycleImage.codec CanonicalCellRegistry.registry).encode .retired from rfl,
    LifecycleImage.decode_encode]

/-- A retired cell holds no activity payload. -/
theorem payloadOf_of_retired {bytes : Bytes} (retired : isRetired bytes = true) : payloadOf bytes = none := by
  unfold isRetired at retired
  unfold payloadOf
  split at retired
  · rename_i decoded; rw [decoded]
  · cases retired

theorem payloadOf_retired : payloadOf retiredImage = none := payloadOf_of_retired isRetired_retiredImage

/-- What a record cell holds: the record while it awaits; the retired image once
it has ended (`done`/`faulted`). The end of an activity is its disposal: the
turn that ends it retires its record (and `settlePurse` sweeps and closes its
purse); the result is the turn's own (re-derivable by replaying the retained
ingress). -/
def recordImage (record : Record) : Bytes :=
  match record.phase with
  | .awaiting _ => image .record (recordKey record.object record.activity) (encodeRecord record)
  | .done _ | .faulted _ => retiredImage

def recordPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (cell : CellId) (record : Record) : Post :=
  postAt snapshot cell (recordImage record)

/-- Retire a slot cell. -/
def slotRetire {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (name : Digest) : Post :=
  postAt snapshot (AnswerSlot.cell config.domain name) retiredImage

def slotPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (slot : AnswerSlot.Slot) : Post :=
  postAt snapshot (AnswerSlot.cell config.domain slot.name) (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))

/-- The image a declared-state write installs: the `ObjectState`. -/
def stateImage (object : CellId) (state : ObjectState) : Bytes :=
  image .state (stateKey object) (encodeObjectState state)

def readRecord {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : Option Record :=
  (bodyOf .record (snapshot.canonicalBytes cell)).bind decodeRecord

def readSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (name : Digest) :
    Option AnswerSlot.Slot :=
  (bodyOf .slot (snapshot.canonicalBytes (AnswerSlot.cell config.domain name))).bind AnswerSlot.decode

/-- Why a record cell holds no record, by name: retired, or never there. -/
def absentRecord {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) : Refusal :=
  if isRetired (snapshot.canonicalBytes cell) then .recordRetired else .recordMissing

/-- Why a slot cell holds no slot, by name. -/
def absentSlot {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (name : Digest) :
    Refusal :=
  if isRetired (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) then .slotRetired else .slotMissing

theorem readRecord_of_retired {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {cell : CellId}
    (retired : isRetired (snapshot.canonicalBytes cell) = true) : readRecord snapshot cell = none := by
  simp [readRecord, bodyOf, payloadOf_of_retired retired]

theorem readSlot_of_retired {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {name : Digest} (retired : isRetired (snapshot.canonicalBytes (AnswerSlot.cell config.domain name)) = true) :
    readSlot config snapshot name = none := by
  simp [readSlot, bodyOf, payloadOf_of_retired retired]

/-- **The declared state a cell's bytes hold as `object`'s**: a state payload whose key is
the object's own (`stateKey object`). Anything else is refused `stateCodec`, a state of
ANOTHER object included: a coordinate the cells of two objects shared would be refused by
name, never read as the wrong object's state. -/
def stateFor (object : CellId) (bytes : Bytes) : Except Refusal (Option ObjectState) :=
  match payloadOf bytes with
  | none => .ok none
  | some payload =>
    if payload.role = .state ∧ payload.key = stateKey object then
      match decodeObjectState payload.body with
      | some state => .ok (some state)
      | none => .error .stateCodec
    else .error .stateCodec

/-- The object's declared state as its state cell holds it: `none` when the
object has no state yet, refused when the cell holds anything else. -/
def readState {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId) :
    Except Refusal (Option ObjectState) :=
  stateFor object (snapshot.canonicalBytes (stateCell config.domain object))

/-- The image an inbox installs. -/
def inboxImage (inbox : Inbox.Inbox) : Bytes :=
  image .inbox (Inbox.key inbox.sender inbox.target) (Inbox.encode inbox)

/-- The inbox an inbox cell holds: `none` when the cell holds no activity cell
(no inbox yet), refused when it holds anything else. -/
def readInbox {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (cell : CellId) :
    Option (Option Inbox.Inbox) :=
  let bytes := snapshot.canonicalBytes cell
  match bodyOf .inbox bytes with
  | some body => (Inbox.decode body).map some
  | none => if (payloadOf bytes).isSome then none else some none

/-- The image an object record installs. -/
def objectImage (object : CellId) (record : ObjectRecord) : Bytes :=
  image .object (objectKey object) (ObjectRecord.encodeRecord record)

/-- Whether a phase is still awaiting (an activity the counters count). -/
def Phase.awaits : Phase → Bool
  | .awaiting _ => true
  | _ => false

/-- **The object record after a turn took one of its activities** from awaiting
(`before`) to awaiting (`after`): `retain` when it starts awaiting, `release` when
it stops, unchanged otherwise. -/
def recount (object : ObjectRecord) (pin activity : Digest) (before after : Bool) : ObjectRecord :=
  if after && !before then object.retain pin activity
  else if before && !after then object.release pin activity
  else object

/-- The post of the object record's counters, when they move: none when the
activity awaited before and after (or neither), so a delivery that yields again
does not write the object record. -/
def countPosts {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId)
    (record : ObjectRecord) (pin activity : Digest) (before after : Bool) : List Post :=
  if before = after then []
  else [postAt snapshot (objectCell config.domain object) (objectImage object (recount record pin activity before after))]

theorem mem_countPosts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord} {pin activity : Digest} {before after : Bool} {post : Post}
    (member : post ∈ countPosts config snapshot object record pin activity before after) :
    post = postAt snapshot (objectCell config.domain object) (objectImage object (recount record pin activity before after)) := by
  unfold countPosts at member
  split at member
  · cases member
  · simpa using member

/-- The post of an object record a turn moved from `before` to `after` (none when
unchanged). -/
def objectPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId)
    (before after : ObjectRecord) : List Post :=
  if after = before then [] else [postAt snapshot (objectCell config.domain object) (objectImage object after)]

theorem mem_objectPost {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {before after : ObjectRecord} {post : Post}
    (member : post ∈ objectPost config snapshot object before after) :
    post = postAt snapshot (objectCell config.domain object) (objectImage object after) := by
  unfold objectPost at member
  split at member
  · cases member
  · simpa using member

/-- **The object record a cell's bytes hold as `object`'s**: an object payload whose key is
the object's own (`objectKey object`); anything else (another object's record included) is
refused `objectCodec`. -/
def objectFor (object : CellId) (bytes : Bytes) : Except Refusal (Option ObjectRecord) :=
  match payloadOf bytes with
  | none => .ok none
  | some payload =>
    if payload.role = .object ∧ payload.key = objectKey object then
      match ObjectRecord.decodeRecord payload.body with
      | some record => .ok (some record)
      | none => .error .objectCodec
    else .error .objectCodec

/-- The object's record: `none` when the cell has none (not an object), refused
when the cell holds anything else. -/
def readObject {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (object : CellId) :
    Except Refusal (Option ObjectRecord) :=
  objectFor object (snapshot.canonicalBytes (objectCell config.domain object))

/-- The request facts a declared-state write is judged under. `turn`: 1 birth,
2 delivery, 4 creation (the seed). A delivery's write is the activity's, so its subject
is the activity's principal (its birth subject, `escrow.payer`: the subject the
native route checked as a holder of the object), never the deliverer.
`artifact`: the package whose code makes the write (a birth's and a delivery's
activity runs the package its record pins) or `none` for a seed, which no package makes. It is what the object's pin clause (`ObjectRecord.pinClause`)
reads as `objective/artifact`. -/
def factsOf (subject : SubjectId) (height : Nat) (object : CellId) (turn : Nat)
    (artifact : Option Digest) : Facts :=
  ⟨some subject, height, object.value, turn, none, artifact.map Digest.value⟩

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
    if (payloadOf (snapshot.canonicalBytes (AnswerSlot.cell config.domain
        (AnswerSlot.name transaction cell generation)))).isSome ||
        isRetired (snapshot.canonicalBytes (AnswerSlot.cell config.domain (AnswerSlot.name transaction cell generation)))
      then .error .slotFresh else
    .ok ⟨⟨awaitId cell generation checkpoint, .reply (AnswerSlot.name transaction cell generation) decider,
        height + plan.patience, height⟩, written,
      (written.map StateWritten.post).toList ++ [slotPost config snapshot
        ⟨AnswerSlot.name transaction cell generation, cell, .subject decider, height + plan.patience, .opened, []⟩]⟩
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

/-- A RESUMED segment and its yield commit, shown `view`. Program faults commit
as `faulted` (the await ends, the unused escrow returns); birth keeps refusing
them, since nothing is escrowed before a birth commits. -/
def resumedSegment {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (transaction : TransactionId) (cell object : CellId) (generation envelope : Nat)
    (view : ObjectState) (start : State) : Except Refusal (Segment × Option YieldCommit) :=
  match runSegment config envelope start with
  | .error refusal => faultOr config envelope refusal
  | .ok segment =>
    match segmentCommit config snapshot height transaction cell object generation (some view) true segment with
    | .error refusal => faultOr config envelope refusal
    | .ok yielded => .ok (segment, yielded)

theorem faultOr_refused {config : Config} {envelope : Nat} {α : Type} {refusal other : Refusal}
    (refused : (faultOr config envelope refusal : Except Refusal (Segment × Option α)) = .error other) :
    other = refusal ∧ programFault config envelope refusal = none := by
  unfold faultOr at refused
  split at refused
  · cases refused
  · rename_i none_
    cases refused
    exact ⟨rfl, none_⟩

theorem faultOr_ok {config : Config} {envelope : Nat} {α : Type} {refusal : Refusal}
    {segment : Segment} {yielded : Option α}
    (ok : (faultOr config envelope refusal : Except Refusal (Segment × Option α)) = .ok (segment, yielded)) :
    ∃ reason, segment = .faulted reason ∧ yielded = none := by
  unfold faultOr at ok
  split at ok
  · rename_i reason _
    cases ok
    exact ⟨reason, rfl, rfl⟩
  · cases ok

/-- **A resumed program never wedges its await.** Whatever a delivery is
refused for, it is not a fault of the resumed program: those commit. -/
theorem resumedSegment_never_refuses_program_fault {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation envelope : Nat} {view : ObjectState} {start : State} {refusal : Refusal}
    (refused : resumedSegment config snapshot height transaction cell object generation envelope view start =
      .error refusal) :
    programFault config envelope refusal = none := by
  unfold resumedSegment at refused
  split at refused
  · obtain ⟨rfl, clean⟩ := faultOr_refused refused
    exact clean
  · split at refused
    · obtain ⟨rfl, clean⟩ := faultOr_refused refused
      exact clean
    · cases refused

/-- A resumed segment that committed a yield is the bounded run's own segment
and its own yield commit. -/
theorem resumedSegment_committed {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation envelope : Nat} {view : ObjectState} {start : State} {segment : Segment}
    {committed : YieldCommit}
    (ran : resumedSegment config snapshot height transaction cell object generation envelope view start =
      .ok (segment, some committed)) :
    runSegment config envelope start = .ok segment ∧
      segmentCommit config snapshot height transaction cell object generation (some view) true segment =
        .ok (some committed) := by
  unfold resumedSegment at ran
  split at ran
  · obtain ⟨_, _, none_⟩ := faultOr_ok ran
    cases none_
  · rename_i run runs
    split at ran
    · obtain ⟨_, _, none_⟩ := faultOr_ok ran
      cases none_
    · rename_i yielded commits
      cases ran
      exact ⟨runs, commits⟩

/-- A resumed segment that yielded is the bounded run's own yield and its own
yield commit. -/
theorem resumedSegment_yielded {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation envelope : Nat} {view : ObjectState} {start state : State} {plan : PlanAwait}
    {committed : Option YieldCommit}
    (ran : resumedSegment config snapshot height transaction cell object generation envelope view start =
      .ok (.yielded state plan, committed)) :
    runSegment config envelope start = .ok (.yielded state plan) ∧
      segmentCommit config snapshot height transaction cell object generation (some view) true
        (.yielded state plan) = .ok committed := by
  unfold resumedSegment at ran
  split at ran
  · obtain ⟨_, faulted, _⟩ := faultOr_ok ran
    cases faulted
  · rename_i run runs
    split at ran
    · obtain ⟨_, faulted, _⟩ := faultOr_ok ran
      cases faulted
    · rename_i yielded commits
      cases ran
      exact ⟨runs, commits⟩

/-- A resumed segment's yield commit is the commit of the segment it carries:
the segment's own commit when it yielded, none when it faulted. -/
theorem resumedSegment_commit {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation envelope : Nat} {view : ObjectState} {start : State} {segment : Segment}
    {yielded : Option YieldCommit}
    (ran : resumedSegment config snapshot height transaction cell object generation envelope view start =
      .ok (segment, yielded)) :
    segmentCommit config snapshot height transaction cell object generation (some view) true segment =
      .ok yielded := by
  unfold resumedSegment at ran
  split at ran
  · obtain ⟨reason, rfl, rfl⟩ := faultOr_ok ran
    rfl
  · split at ran
    · obtain ⟨reason, rfl, rfl⟩ := faultOr_ok ran
      rfl
    · rename_i commits
      cases ran
      exact commits

/-- An exhaustion below the turn cap is refused, never committed as a fault. -/
theorem resumedSegment_exhausted_below_cap {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation envelope : Nat} {view : ObjectState} {start : State}
    (ran : runSegment config envelope start = .error .exhausted) (below : envelope < config.maxTicks) :
    resumedSegment config snapshot height transaction cell object generation envelope view start =
      .error .exhausted := by
  unfold resumedSegment
  rw [ran]
  simp [faultOr, programFault, Nat.not_le.mpr below]

/-- The program faults, by name (regression teeth for the classification). -/
theorem plan_fault_commits (config : Config) (envelope : Nat) (reason : String) :
    (faultOr config envelope (.plan reason) : Except Refusal (Segment × Option YieldCommit)) =
      .ok (.faulted s!"plan: {reason}", none) := rfl

theorem funding_is_not_a_fault (config : Config) (envelope available pair : Nat) :
    programFault config envelope (.awaitsFunding available pair) = none := rfl

theorem law_denial_is_not_a_fault (config : Config) (envelope : Nat) (reason : WriteRefusal) :
    programFault config envelope (.objectWrite reason) = none := rfl

theorem exhaustion_below_cap_is_not_a_fault (config : Config) (envelope : Nat)
    (below : envelope < config.maxTicks) : programFault config envelope .exhausted = none := by
  simp [programFault, Nat.not_le.mpr below]

/-- **The storage deposit** a record reserves while it is retained: the
deployment's rate per byte of the record's encoding. Only an awaiting record is
retained; an ended one is retired and reserves nothing. A function of the record
the yield commits, so it is re-priced at every yield. -/
def storageDeposit (config : Config) (record : Record) : Nat :=
  match record.phase with
  | .awaiting _ => config.storageRate * (encodeRecord record).length
  | .done _ | .faulted _ => 0

/-- The assets a purse holds a nonzero balance of, in ascending order. -/
def purseAssets (book : Book) (held : AccountId) : List AssetId :=
  ((book.balances.support.filter (fun coordinate => coordinate.1 = held)).image Prod.snd).sort

/-- Sweep a purse: every positive balance it holds, in every asset, to `account`.
After it the purse holds no positive balance, so (holding no negative one either:
a purse is no issuer well) it can be closed. -/
def sweep (book : Book) (held account : AccountId) : List Operation :=
  (purseAssets book held).filterMap fun asset =>
    if 0 < book.balance held asset then some (.transfer held account asset (book.balance held asset).toNat) else none

/-- After a segment: a yield must leave the purse able to pay the await's fee
pair AND the next record's storage deposit (both stay reserved there); an end
sweeps the purse to the payer and closes it on the Book. The ending turn's own
postings come first (`before`). -/
def settlePurse (config : Config) (book : Book) (held : AccountId) (escrow : Escrow) (deposit : Nat)
    (before : Batch) (segment : Segment) : Except Refusal Batch :=
  let after := purse (before.apply book) config.asset held
  if segment.yields then
    if escrow.pair + deposit ≤ after then .ok before
    else .error (.awaitsFunding after (escrow.pair + deposit))
  else .ok ⟨before.registrations,
    before.operations ++ sweep (before.apply book) held escrow.account, before.deregistrations ++ [held]⟩

/-! ### publish -/

/-- The output codec an activity artifact names: its entry returns an
`Activity<P,R,A>`, never a native method result. -/
def codecId : Digest := tagged "DREGG/OBJECTIVE/ACTIVITY/OUTPUT-CODEC/v1" []

def publishTransaction (pin : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/PUBLISH/v1" (digestStream.encode pin)

/-- The artifact and its package, posted together into the artifact's package cell. -/
structure Publication {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (stored : Stored) where
  private mk ::
  pin : Digest
  /-- The package cell held no activity cell at all: a package is installed once, never overwritten. -/
  fresh : payloadOf (snapshot.canonicalBytes (packageCell config.domain pin)) = none
  /-- The front end's replay of the stored package, which produced the artifact's core. -/
  replay : Replay config pin
  /-- The payer is a registered account of the loaded Book, and neither the credit asset's
  issuer well nor the collector. -/
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  payerRegistered : stored.payer ∈ (logicalBook book.logical).accounts
  /-- The Book cell the payer was read from, guarded at the root it was read at. -/
  guards : List ReadGuard
  guardsExact : guards = [guardAt snapshot config.bookCell]
  posts : List Post
  postsExact : posts = [postAt snapshot (packageCell config.domain pin) (image .package (packageKey pin) (encodeStored stored))]

def publish {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (stored : Stored) : Except Refusal (Publication config snapshot stored) := do
  let some artifact := ObjectiveBendSourceArtifact.decode stored.artifact | throw .packageMissing
  if artifact.outputCodec ≠ codecId then throw (.packageType "not an activity artifact")
  let pin := ObjectiveBendSourceArtifact.identity artifact
  match fresh : payloadOf (snapshot.canonicalBytes (packageCell config.domain pin)) with
  | some _ => throw .packageExists
  | none =>
  if stored.payer = config.asset ∨ stored.payer = config.collector then throw .payerInvalid
  match bookExact : loadBook config snapshot with
  | .error reason => throw reason
  | .ok book =>
    if payerRegistered : stored.payer ∈ (logicalBook book.logical).accounts then
      let definition ← replayPackage config stored pin
      match callable definition.replayed.accepted.typed.type with
      | .arrow _ _ _ (.computation _ _ _) => pure ()
      -- a call method `View -> Args -> Activity<..>` (`Kernel.ObjectiveCall`): an object pinning
      -- a package of methods only; whether a named method is callable is checked at each call.
      | .arrow _ _ _ (.arrow _ _ _ (.computation _ _ _)) => pure ()
      | _ => throw (.packageType "a package selects an activity `Input -> Activity<P,R,A>` or a call method \
          `View -> Args -> Activity<P,R,A>`")
      pure ⟨pin, fresh, definition, book, bookExact, payerRegistered, _, rfl, _, rfl⟩
    else throw .payerInvalid

def Publication.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {stored : Stored} (publication : Publication config snapshot stored) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (publishTransaction publication.pin) publication.posts publication.guards [] sealing

/-! ### Upgrades: the migration and the drained-write judgment

A migration is a declaration of the NEXT package (`Pending.migration`), lowered
by this kernel's own front end from that package's stored sources with the
declaration selected (as a call method is, `ObjectiveCall.loadMethod`): the
term it runs is the elaborator's output, never an offered core. Its checked type
is a function `old -> new`; it is applied to the state datum (typed at its
domain by the checker) and run to a value within the upgrade's declared
envelope. `none` is the identity. -/

/-- A migration declaration of a stored package: replayed, lowered with the
declaration selected, accepted by the checker, and a function. -/
structure Migration (config : Config) (pin : Digest) (name : String) where
  private mk ::
  definition : Replay config pin
  lowering : ObjectiveBendFrontEnd.Lowering
  replayExact : ObjectiveBendPublication.replay { definition.package with entryDefinition := name } = .ok lowering
  accepted : ObjectiveBendFrontEnd.Accepted lowering
  fuelWithin : accepted.packet.fuel ≤ config.typeFuel
  reuse : Reuse
  quantity : Quantity
  domain : Ty
  codomain : Ty
  arrowExact : callable accepted.typed.type = .arrow reuse quantity domain codomain

def loadMigration (config : Config) (bytes : Bytes) (pin : Digest) (name : String) :
    Except Refusal (Migration config pin name) :=
  match decodeStored bytes with
  | none => .error .packageMissing
  | some stored =>
  match replayPackage config stored pin with
  | .error reason => .error reason
  | .ok definition =>
  match replayExact : ObjectiveBendPublication.replay { definition.package with entryDefinition := name } with
  | .error d => .error (.migrationShape d.message)
  | .ok lowering =>
  match ObjectiveBendFrontEnd.accept lowering with
  | .error d => .error (.migrationShape d.message)
  | .ok accepted =>
  if fuelWithin : accepted.packet.fuel ≤ config.typeFuel then
    match arrowExact : callable accepted.typed.type with
    | .arrow reuse quantity domain codomain =>
      .ok ⟨definition, lowering, replayExact, accepted, fuelWithin, reuse, quantity, domain, codomain, arrowExact⟩
    | _ => .error (.migrationShape "the migration is not a function of the state")
  else .error (.migrationShape "typed core checker fuel exceeds the kernel's capacity")

/-- The migration applied to a state datum, annotated at its domain. -/
def Migration.applied {config : Config} {pin : Digest} {name : String} (migration : Migration config pin name)
    (value : Data) : AnnotatedTerm :=
  ⟨.app migration.accepted.source.term value.term,
    fun path => match path with
      | 0 :: rest => migration.accepted.source.annotations rest
      | 1 :: rest => annotationsOf (dataAnnotations migration.accepted.source.assumptions.bounds 64 value
          migration.domain []) rest
      | _ => none,
    migration.accepted.source.assumptions⟩

/-- Run a migration on a state datum within `ticks`, under the segment limits every run
gets (`segmentLimits`, from the fresh start): the application must check, and the run must
finish with a value. -/
def runMigration (config : Config) {pin : Digest} {name : String} (migration : Migration config pin name)
    (ticks : Nat) (value : Data) : Except Refusal Data :=
  match check (migration.applied value) [] config.typeFuel with
  | none => .error (.migrationFault "the state does not type at the migration's domain")
  | some _ =>
    let start := initial (migration.applied value).erase
    match runBounded (segmentLimits config start) ticks start with
    | .finished _ finished =>
      match ObjectiveBendDemandData.complete (segmentLimits config start) config.planBudget finished with
      | .ok result => .ok result.value
      | .error (failure, _) => .error (.migrationFault s!"result extraction: {reprStr failure}")
    | .suspended _ _ => .error (.migrationFault "it exhausted its declared envelope")
    | _ => .error (.migrationFault "it did not finish with a value")

/-- The migrated state: the migration's result, or the state itself under the identity. -/
def migrateValue (config : Config) (bytes : Bytes) (next : ObjectRecord.Pending) (value : Data) :
    Except Refusal Data :=
  match next.migration with
  | none => .ok value
  | some name =>
    match loadMigration config bytes next.pin name with
    | .error reason => .error reason
    | .ok migration => runMigration config migration next.envelope.sourceTicks value

/-- **The drained judgment of one state** while `record` drains toward `next`:
the state, migrated, is admitted by the record MIGRATE will install
(`ObjectRecord.successor`), under the migration's facts (`migrateFacts`): exactly
the judgment MIGRATE makes. Typing at the next state type is part of it
(`admitWrite`). Returns the migrated state. -/
def judgeMigrated {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (record : ObjectRecord) (object : CellId) (next : ObjectRecord.Pending) (value : Data) : Except Refusal Data :=
  match migrateValue config (packageBytes config snapshot next.pin) next value with
  | .error reason => .error reason
  | .ok migrated =>
    match admitWrite (record.successor next) (ObjectRecord.migrateFacts object.value next) (some migrated) migrated with
    | .ok () => .ok migrated
    | .error reason => .error (.objectWrite (.upgradeConflict reason))

/-- **The drained-write judgment**: while the object drains, the state a write
installs must pass `judgeMigrated` (on top of the object's own law, judged as
before by `judgeWritten`); steady, nothing more. -/
def judgeDrained {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (record : ObjectRecord) (object : CellId) : Option StateWritten → Except Refusal Unit
  | none => .ok ()
  | some written =>
    match record.phase with
    | .steady => .ok ()
    | .draining next _ =>
      match judgeMigrated config snapshot record object next written.after.value with
      | .ok _ => .ok ()
      | .error reason => .error reason

/-- The price of the migration run a drained write costs: the public price of the
upgrade's declared migration envelope, when the write ran a migration term. -/
def drainFee (config : Config) (record : ObjectRecord) (written : Option StateWritten) : Nat :=
  match written, record.phase with
  | some _, .draining next _ => if next.migration.isSome then config.tariff.workOf next.envelope else 0
  | _, _ => 0

/-! ### birth -/

/-- The activity a birth RE-BIRTHS (`ObjectiveActivityUpgrade.rebirth`): in the
birth's own posts and batch, its counter is released and its purse is swept into
the new purse and closed. -/
structure Predecessor where
  pin : Digest
  activity : Digest
  purse : AccountId
  /-- The predecessor's escrow account: the new purse returns there at the end. -/
  refund : AccountId
  deriving DecidableEq, Repr

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
  /-- The activity this birth re-births, if any (`none` for every signed birth). -/
  predecessor : Option Predecessor

def birthTransaction (request : BirthRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/TX/BIRTH/v2"
    (subjectStream.encode request.subject ++ digestStream.encode request.object ++
      digestStream.encode request.pin ++ bytesStream.encode (dataBytes request.input) ++
      StreamCodec.nat.encode request.nonce)

/-- The birth's postings: register the purse, pay the birth's declared envelope
to the collector, move the deposit into the purse; then the purse settles
(`settlePurse`). -/
def birthBatch (config : Config) (book : Book) (held : AccountId) (request : BirthRequest)
    (escrow : Escrow) (deposit : Nat) (segment : Segment) : Except Refusal Batch :=
  let registered := Batch.apply ⟨[held], [], []⟩ book
  let own : List Operation :=
    [.fee request.account config.collector config.asset (config.tariff.workOf request.envelope)] ++
      (if request.deposit = 0 then [] else [.transfer request.account held config.asset request.deposit])
  -- A rebirth sweeps what is left of its predecessor's purse into the new purse and closes it.
  let closing : List Operation := match request.predecessor with
    | none => []
    | some predecessor => sweep (applyOperations registered own) predecessor.purse held
  settlePurse config registered held escrow deposit
    ⟨[], own ++ closing, (request.predecessor.map Predecessor.purse).toList⟩ segment
  |>.map fun settled => ⟨held :: settled.registrations, settled.operations, settled.deregistrations⟩

/-- The account the activity's purse is returned to at its end: the payer's, or
for a rebirth the predecessor's (the request's account is the old purse, closed
by the rebirth). -/
def BirthRequest.escrowAccount (request : BirthRequest) : AccountId :=
  match request.predecessor with
  | some predecessor => predecessor.refund
  | none => request.account

/-- The turn code a birth's write is judged under: 1, or 9 for a rebirth. -/
def BirthRequest.factsTurn (request : BirthRequest) : Nat :=
  if request.predecessor.isSome then 9 else 1

/-- The object record after a birth: its predecessor (if any) released, the new
activity retained when it awaits. -/
def birthCount (object : ObjectRecord) (request : BirthRequest) (activity : Digest) (awaits : Bool) : ObjectRecord :=
  recount (match request.predecessor with
    | none => object
    | some predecessor => object.release predecessor.pin predecessor.activity) request.pin activity false awaits

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
  /-- The record cell held no activity cell at all. -/
  fresh : payloadOf (snapshot.canonicalBytes cell) = none
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
      escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout,
      0, .faulted "unborn"⟩ 0 segment yielded
  /-- The object's record: the birth is on an object, and runs the package it pins. -/
  object : ObjectRecord
  objectExact : readObject config snapshot request.object = .ok (some object)
  /-- The object admits new activities (steady, or draining under the identity). -/
  admits : object.admitsNew = true
  /-- ... of the package it runs for them (its pin; while draining, the next pin). -/
  pinned : object.activePin = request.pin
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  posts : List Post
  recordFirst : posts.head? = some (recordPost config snapshot cell record)
  /-- The record, the yield's posts, the Book, and (when the birth leaves the
  activity awaiting) the object record with the activity counted (`retain`). -/
  postsExact : posts = recordPost config snapshot cell record ::
    ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot] ++
      objectPost config snapshot request.object object
        (birthCount object request (activityId request.object (birthTransaction request)) record.phase.awaits))
  guards : List ReadGuard
  guardsExact : guards = [guardAt snapshot (objectCell config.domain request.object),
    guardAt snapshot (packageCell config.domain request.pin),
    guardAt snapshot (stateCell config.domain request.object)]
  /-- The object's law admitted the first segment's write (if it wrote). -/
  judged : judgeWritten object (factsOf request.subject height request.object request.factsTurn (some request.pin))
    (yielded.bind YieldCommit.written) = .ok ()
  /-- While the object drains, the write's state passes the next record's judgment. -/
  drained : judgeDrained config snapshot object request.object (yielded.bind YieldCommit.written) = .ok ()
  /-- A yielding birth's deposit reserves the first await's fee pair and its
  record's storage deposit. -/
  funded : ¬ (segment.yields ∧ request.deposit <
    (escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout).pair +
      storageDeposit config record)
  /-- The birth's envelope declares the extraction tick budget its segment may spend. -/
  extractCovered : config.planBudget.ticks ≤ request.envelope.extractTicks

def birth {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : BirthRequest) : Except Refusal (Birth config snapshot height request) := do
  match objectExact : readObject config snapshot request.object with
  | .error reason => throw reason
  | .ok none => throw .notAnObject
  | .ok (some object) =>
    if admits : object.admitsNew = true then
    if pinned : object.activePin = request.pin then
      if !config.covers request.envelope then throw (.uncovered request.envelope)
      if !config.covers request.resume then throw (.uncovered request.resume)
      if !config.covers request.timeout then throw (.uncovered request.timeout)
      let ⟨extractCovered⟩ ← (if h : config.planBudget.ticks ≤ request.envelope.extractTicks then pure ⟨h⟩
        else throw (.extractUncovered config.planBudget.ticks request.envelope.extractTicks) :
          Except Refusal (PLift (config.planBudget.ticks ≤ request.envelope.extractTicks)))
      if request.resume.extractTicks < config.planBudget.ticks then
        throw (.extractUncovered config.planBudget.ticks request.resume.extractTicks)
      if request.timeout.extractTicks < config.planBudget.ticks then
        throw (.extractUncovered config.planBudget.ticks request.timeout.extractTicks)
      match programExact : loadProgram config (packageBytes config snapshot request.pin) request.pin request.input with
      | .error reason => throw reason
      | .ok program =>
        outcomeProtocol program
        let transaction := birthTransaction request
        let activity := activityId request.object transaction
        let cell := recordCell config.domain request.object activity
        if isRetired (snapshot.canonicalBytes cell) then throw .recordRetired
        match fresh : payloadOf (snapshot.canonicalBytes cell) with
        | some _ => throw .recordExists
        | none =>
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
              match judged : judgeWritten object (factsOf request.subject height request.object request.factsTurn (some request.pin))
                  (yielded.bind YieldCommit.written) with
              | .error reason => throw reason
              | .ok () =>
              match drained : judgeDrained config snapshot object request.object (yielded.bind YieldCommit.written) with
              | .error reason => throw reason
              | .ok () =>
                match yielded with
                | some committed =>
                  match (committed.written.map StateWritten.after).orElse (fun _ => current) with
                  | some view => viewProtocol program view
                  | none => throw .stateMissing
                | none => pure ()
                let escrow := escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout
                let base : Record := ⟨request.object, activity, request.pin, dataBytes request.input, 0, [],
                  checkpointDigest [], escrow, 0, .faulted "unborn"⟩
                let record := nextRecord base 0 segment yielded
                if short : segment.yields ∧ request.deposit < escrow.pair + storageDeposit config record then
                  throw (.underfunded request.deposit (escrow.pair + storageDeposit config record))
                else
                  let batch ← birthBatch config (logicalBook book.logical) held request escrow
                    (storageDeposit config record) segment
                  let posted ← postings book batch
                  let posts := recordPost config snapshot cell record ::
                    ((yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot] ++
                      objectPost config snapshot request.object object (birthCount object request activity record.phase.awaits))
                  pure ⟨program, programExact, cell, rfl, fresh, current, currentExact, segment, segmentExact, yielded,
                    yieldedExact, record, rfl, object, objectExact, admits, pinned, book, bookExact, posted, posts, rfl, rfl,
                    [guardAt snapshot (objectCell config.domain request.object),
                      guardAt snapshot (packageCell config.domain request.pin),
                      guardAt snapshot (stateCell config.domain request.object)], rfl,
                    judged, drained, short, extractCovered⟩
    else throw (.pinMismatch object.activePin request.pin)
    else throw .draining

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
    let some record := readRecord snapshot activity | throw (absentRecord snapshot activity)
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
  | none => .error (absentSlot config snapshot request.slot)
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
    | none => .error (absentSlot config snapshot slotName)
    | some slot =>
      if slot.name ≠ slotName ∨ slot.activity ≠ cell then .error .slotMismatch else
      match slot.phase with
      | .decided decision _ => do
        let outcome ← outcomeOfDecision decision
        pure ⟨if decision = .expired then .timedOut else .resumed, outcome,
          [slotRetire config snapshot slotName], [], []⟩
      | .opened =>
        match AnswerSlot.expire slot height with
        | .ok _ => .ok ⟨.timedOut, .timedOut, [slotRetire config snapshot slotName], [],
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
    (request : DeliverRequest) (migration : Nat) : Batch :=
  ⟨[], [.fee (heldAccount cell) config.collector config.asset (record.escrow.used path)] ++
    (if request.extra = zeroCapacity then []
     else [.fee request.account config.collector config.asset (config.tariff.workOf request.extra)]) ++
    (if migration = 0 then [] else [.fee (heldAccount cell) config.collector config.asset migration]), []⟩

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
  /-- The deployment covers the declared envelope (`Config.covers`). -/
  covered : config.covers envelope = true
  /-- The declared envelope covers the resumed run's heap (`segmentLimits`): growth of the
  checkpoint is paid by the delivery that runs it. -/
  heapCovered : (segmentLimits config resumed).heap ≤ envelope.heap
  /-- The declared envelope covers the extraction tick budget the segment may spend. -/
  extractCovered : config.planBudget.ticks ≤ envelope.extractTicks
  segment : Segment
  yielded : Option YieldCommit
  /-- The resumed run and its yield commit; a program fault ends it `faulted`. -/
  endExact : resumedSegment config snapshot height (deliveryTransaction await.id) request.record record.object
    (record.generation + 1) envelope.sourceTicks view resumed = .ok (segment, yielded)
  next : Record
  nextExact : next = nextRecord record (record.generation + 1) segment yielded
  /-- The object's record, read in this turn. -/
  object : ObjectRecord
  objectExact : readObject config snapshot record.object = .ok (some object)
  /-- The object still runs the activity's package (not frozen for rebirth). -/
  runsPin : object.runs record.pin = true
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  batch : Batch
  batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow
    (storageDeposit config next)
    (deliveryCharges config record request.record settlement.path request
      (drainFee config object (yielded.bind YieldCommit.written))) segment =
      .ok batch
  posted : Postings book
  postedBatch : posted.batch = batch
  posts : List Post
  recordFirst : posts.head? = some (recordPost config snapshot request.record next)
  /-- ... and, when the activity ends, the object record with it uncounted (`release`). -/
  postsExact : posts = recordPost config snapshot request.record next ::
    (settlement.posts ++ (yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot] ++
      countPosts config snapshot record.object object record.pin record.activity true next.phase.awaits)
  guards : List ReadGuard
  guardsExact : guards = guardAt snapshot (objectCell config.domain record.object) ::
    guardAt snapshot (packageCell config.domain record.pin) ::
    guardAt snapshot (stateCell config.domain record.object) :: settlement.guards
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: settlement.claims
  /-- The object's law admitted the segment's write (if it wrote), judged with
  the activity's principal as subject. -/
  judged : judgeWritten object (factsOf record.escrow.payer height record.object 2 (some record.pin))
    (yielded.bind YieldCommit.written) = .ok ()
  /-- While the object drains, the write's state, migrated, passes the next
  record's judgment (the drained-write judgment). -/
  drained : judgeDrained config snapshot object record.object (yielded.bind YieldCommit.written) = .ok ()

def deliver {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : DeliverRequest) : Except Refusal (Delivery config snapshot height request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error (absentRecord snapshot request.record)
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
  if runsPin : object.runs record.pin = true then
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
  if covered : config.covers envelope = true then
  if heapCovered : (segmentLimits config resumed).heap ≤ envelope.heap then
  if extractCovered : config.planBudget.ticks ≤ envelope.extractTicks then
  if 0 < record.tried ∧ envelope.sourceTicks ≤ record.tried then .error (.alreadyExhausted record.tried envelope.sourceTicks) else
  match endExact : resumedSegment config snapshot height (deliveryTransaction await.id) request.record
      record.object (record.generation + 1) envelope.sourceTicks view resumed with
  | .error reason => .error reason
  | .ok (segment, yielded) =>
  match judged : judgeWritten object (factsOf record.escrow.payer height record.object 2 (some record.pin))
      (yielded.bind YieldCommit.written) with
  | .error reason => .error reason
  | .ok () =>
  match drained : judgeDrained config snapshot object record.object (yielded.bind YieldCommit.written) with
  | .error reason => .error reason
  | .ok () =>
  let next := nextRecord record (record.generation + 1) segment yielded
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match batchExact : settlePurse config (logicalBook book.logical) (heldAccount request.record) record.escrow
      (storageDeposit config next)
      (deliveryCharges config record request.record settlement.path request
        (drainFee config object (yielded.bind YieldCommit.written))) segment with
  | .error reason => .error reason
  | .ok batch =>
  match postings book batch with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = batch then
  let posts := recordPost config snapshot request.record next ::
    (settlement.posts ++ (yielded.map YieldCommit.posts).getD [] ++ [posted.write config snapshot] ++
      countPosts config snapshot record.object object record.pin record.activity true next.phase.awaits)
  let guards := guardAt snapshot (objectCell config.domain record.object) ::
    guardAt snapshot (packageCell config.domain record.pin) ::
    guardAt snapshot (stateCell config.domain record.object) :: settlement.guards
  .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program, programExact,
    settlement, settled, view, viewExact, response, state, stateExact, resumed, resumeExact, envelope, rfl,
    covered, heapCovered, extractCovered, segment, yielded, endExact, next, rfl, object, objectExact, runsPin, book,
    bookExact, batch, batchExact, posted,
    postedBatch, posts, rfl, rfl, guards, rfl, awaitClaim await.id :: settlement.claims, rfl,
    judged, drained⟩
  else .error .bookRefused
  else .error (.extractUncovered config.planBudget.ticks envelope.extractTicks)
  else .error (.heapUncovered (segmentLimits config resumed).heap envelope.heap)
  else .error (.uncovered envelope)
  else .error .awaitingRebirth
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
     else [.fee request.account config.collector config.asset (config.tariff.workOf request.extra)]), []⟩

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
  /-- As a delivery: the deployment covers the declared envelope. -/
  covered : config.covers envelope = true
  /-- As a delivery: the declared envelope covers the resumed run's heap. -/
  heapCovered : (segmentLimits config resumed).heap ≤ envelope.heap
  /-- As a delivery: the declared envelope covers the extraction tick budget. -/
  extractCovered : config.planBudget.ticks ≤ envelope.extractTicks
  raises : record.tried < envelope.sourceTicks
  /-- At the turn cap an exhaustion is a program fault: a delivery commits it `faulted`. -/
  belowCap : envelope.sourceTicks < config.maxTicks
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
  | none => .error (absentRecord snapshot request.record)
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
  if covered : config.covers envelope = true then
  if heapCovered : (segmentLimits config resumed).heap ≤ envelope.heap then
  if extractCovered : config.planBudget.ticks ≤ envelope.extractTicks then
  if raises : record.tried < envelope.sourceTicks then
  -- The charge must be payable BEFORE the run: an unpayable attempt never runs.
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postings book (exhaustCharges config record request.record settlement.path request) with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = exhaustCharges config record request.record settlement.path request then
  if belowCap : envelope.sourceTicks < config.maxTicks then
  match ran : runSegment config envelope.sourceTicks resumed with
  | .ok _ => .error .notExhausted
  | .error .exhausted =>
    let next := { record with tried := envelope.sourceTicks }
    let posts := [recordPost config snapshot request.record next, posted.write config snapshot]
    let guards := guardAt snapshot (packageCell config.domain record.pin) ::
      guardAt snapshot (stateCell config.domain record.object) :: settlementGuards settlement
    .ok ⟨record, recordExact, located, await, awaiting, idExact, digestExact, input, inputExact, program,
      programExact, settlement, settled, view, viewExact, response, state, stateExact, resumed, resumeExact,
      envelope, rfl, covered, heapCovered, extractCovered, raises, belowCap, ran, next, rfl, book, bookExact, posted, postedBatch, posts, rfl,
      guards, rfl⟩
  | .error reason => .error reason
  else .error .notExhausted
  else .error .bookRefused
  else .error (.alreadyExhausted record.tried envelope.sourceTicks)
  else .error (.extractUncovered config.planBudget.ticks envelope.extractTicks)
  else .error (.heapUncovered (segmentLimits config resumed).heap envelope.heap)
  else .error (.uncovered envelope)
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
    | none => .error (absentSlot config snapshot name)
    | some slot => match slot.phase with
      | .opened => .ok ([slotRetire config snapshot name], [AnswerSlot.decisionClaim name])
      | .decided _ _ => .ok ([slotRetire config snapshot name], [])

/-- The abandonment's own fee: the timeout fee, or what the purse holds of it. -/
def abandonFee (config : Config) (book : Book) (cell : CellId) (escrow : Escrow) : Nat :=
  min (purse book config.asset (heldAccount cell)) escrow.timeoutFee

/-- The abandonment's own fee posting. -/
def abandonFeeOps (config : Config) (book : Book) (cell : CellId) (escrow : Escrow) : List Operation :=
  let fee := abandonFee config book cell escrow
  if fee = 0 then [] else [.fee (heldAccount cell) config.collector config.asset fee]

/-- Its postings: the fee to the collector, then the whole rest of the purse
(every asset) swept to the payer, and the purse closed. -/
def abandonCharges (config : Config) (book : Book) (cell : CellId) (escrow : Escrow) : Batch :=
  let feeOps := abandonFeeOps config book cell escrow
  ⟨[], feeOps ++ sweep (applyOperations book feeOps) (heldAccount cell) escrow.account, [heldAccount cell]⟩

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
  /-- The object's record, read to uncount the activity. -/
  object : ObjectRecord
  objectExact : readObject config snapshot record.object = .ok (some object)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  postedBatch : posted.batch = abandonCharges config (logicalBook book.logical) request.record record.escrow
  posts : List Post
  postsExact : posts = postAt snapshot request.record retiredImage ::
    (slotPosts ++ [posted.write config snapshot] ++
      countPosts config snapshot record.object object record.pin record.activity true false)
  claims : List StableNullifier
  claimsExact : claims = awaitClaim await.id :: slotClaims

def abandon {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : AbandonRequest) : Except Refusal (Abandonment config snapshot height request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error (absentRecord snapshot request.record)
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
  match objectExact : readObject config snapshot record.object with
  | .error reason => .error reason
  | .ok none => .error .notAnObject
  | .ok (some object) =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error reason
  | .ok book =>
  match postings book (abandonCharges config (logicalBook book.logical) request.record record.escrow) with
  | .error reason => .error reason
  | .ok posted =>
  if postedBatch : posted.batch = abandonCharges config (logicalBook book.logical) request.record record.escrow then
    .ok ⟨record, recordExact, located, await, awaiting, idExact, due, slotPosts, slotClaims, slotExact, object,
      objectExact, book, bookExact, posted, postedBatch, _, rfl, _, rfl⟩
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
  postedBatch : posted.batch = ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount], []⟩

def topUp {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : TopUpRequest) : Except Refusal (TopUp config snapshot request) :=
  match recordExact : readRecord snapshot request.record with
  | none => .error (absentRecord snapshot request.record)
  | some record =>
    match record.phase with
    | .done _ | .faulted _ => .error .notAwaiting
    | .awaiting _ =>
    if request.amount = 0 then .error .zeroAmount else
    if request.account = config.asset ∨ request.account = heldAccount request.record then .error .payerInvalid else
    match bookExact : loadBook config snapshot with
    | .error reason => .error reason
    | .ok book =>
      match postings book ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount], []⟩ with
      | .error reason => .error reason
      | .ok posted =>
        if postedBatch : posted.batch = ⟨[], [.transfer request.account (heldAccount request.record) config.asset request.amount], []⟩ then
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

/-! ### create: an object's record, and its initial declared state -/

structure CreateRequest where
  subject : SubjectId
  /-- The object resource (a cell the authority layer issues capabilities on). -/
  object : CellId
  pin : Digest
  /-- The declared state type: every write of the object's state is typed at it. -/
  stateType : Ty
  law : Minidregg.Pred.Pred
  upgrade : ObjectRecord.UpgradePolicy
  /-- The object's initial declared state, if any. It is the first and only state write of the
  creation (the state cell must not exist) and is judged by the CREATOR'S law alone
  (`ObjectRecord.admitSeed`): the pin governs the writes after the object exists, and an object
  cannot be born violating its own state clauses. The state is otherwise changed only by the
  package's own turns, under the pin. -/
  seed : Option Data
  /-- The Book account that funds the record and the state cell; never authority. -/
  payer : AccountId

def createTransaction (request : CreateRequest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/OBJECT/TX/CREATE/v2" (subjectStream.encode request.subject ++
    digestStream.encode request.object ++ (StreamCodec.option bytesStream).encode (request.seed.map dataBytes))

/-- The record a creation installs: schema version 1, continuity 0, no live
activity, steady. -/
def CreateRequest.record (request : CreateRequest) : ObjectRecord :=
  ⟨request.object, request.pin, request.stateType, 1, request.law, request.upgrade, 0, request.payer, 0, 0, .steady⟩

/-- The request facts a seed is judged under: turn 4, and no package writes (the artifact slot
reads `-1`; the creator's law, not the pin, judges it). -/
def seedFacts (request : CreateRequest) (height : Nat) : Facts :=
  factsOf request.subject height request.object 4 none

/-- The state cell a seed installs: version 1. -/
def seedPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (request : CreateRequest) (seed : Data) : Post :=
  postAt snapshot (stateCell config.domain request.object) (stateImage request.object ⟨1, seed⟩)

/-- Who may create an object's record is the receiver's question (a holder of
a capability on the object resource). The kernel refuses a second record, a
pin that names no published package, a seed onto an existing state cell, and a seed the
creator's own law refuses. -/
structure Creation {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : CreateRequest) where
  private mk ::
  absent : readObject config snapshot request.object = .ok none
  published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true
  /-- A seed is the state cell's first write: the cell holds nothing. -/
  stateFresh : ∀ seed, request.seed = some seed → readState config snapshot request.object = .ok none
  /-- A seed is admitted by the creator's law, over no old state. -/
  seedJudged : ∀ seed, request.seed = some seed →
    ObjectRecord.admitSeed request.record (seedFacts request height) seed = .ok ()

  /-- The declared state type is first-order data. -/
  data : request.stateType.isData = true
  posts : List Post
  postsExact : posts = postAt snapshot (objectCell config.domain request.object)
      (objectImage request.object request.record) ::
    (request.seed.map (seedPost config snapshot request)).toList

def create {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : CreateRequest) : Except Refusal (Creation config snapshot height request) :=
  match absent : readObject config snapshot request.object with
  | .error reason => .error reason
  | .ok (some _) => .error .objectExists
  | .ok none =>
    if published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true then
      if data : request.stateType.isData = true then
      match seedPlan : request.seed with
      | none =>
        .ok ⟨absent, published, (fun _ h => by rw [seedPlan] at h; cases h),
          (fun _ h => by rw [seedPlan] at h; cases h), data, _, rfl⟩
      | some seed =>
        match stateRead : readState config snapshot request.object with
        | .error reason => .error reason
        | .ok (some _) => .error .stateExists
        | .ok none =>
          match judged : ObjectRecord.admitSeed request.record (seedFacts request height) seed with
          | .error reason => .error (.objectWrite reason)
          | .ok () =>
            .ok ⟨absent, published,
              (fun _ h => by rw [seedPlan] at h; cases h; exact stateRead),
              (fun _ h => by rw [seedPlan] at h; cases h; exact judged), data, _, rfl⟩
      else .error .stateTypeNotData
    else .error .pinUnpublished

def Creation.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request) (sealing : Seal) :
    DataIntent rootBytes :=
  intentOf rootBytes (createTransaction request) created.posts
    [guardAt snapshot (packageCell config.domain request.pin), guardAt snapshot (stateCell config.domain request.object)]
    [] sealing

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
    resolution.slot.decider = .subject request.subject ∧ resolution.slot.phase = .opened ∧
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
          subst member; simp only [slotRetire, postAt]
        · split at settled
          · cases settled
            intro post member
            simp only [List.mem_singleton] at member
            subst member; simp only [slotRetire, postAt]
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
  rcases member with isRecord | ((inSettlement | inYield) | isBook) | inCount
  · subst isRecord; simp only [recordPost, postAt]
  · exact settle_posts_current delivery.settled post inSettlement
  · cases yielded : delivery.yielded with
    | none => simp [yielded] at inYield
    | some committed =>
      simp only [yielded, Option.map_some, Option.getD_some] at inYield
      have ended := delivery.endExact
      rw [yielded] at ended
      have commit := (resumedSegment_committed ended).2
      obtain ⟨_, _, _, committedExact⟩ := segmentCommit_spec commit
      exact (commitYield_spec committedExact).2.2 post inYield
  · rcases isBook with isBook | none
    · subst isBook; simp only [Postings.write, postAt]
    · simp at none
  · rw [mem_countPosts inCount]; simp only [postAt]

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
  have ended := delivery.endExact
  rw [yielded] at ended
  have commit := (resumedSegment_committed ended).2
  obtain ⟨state, plan, segmentIs, committedExact⟩ := segmentCommit_spec commit
  obtain ⟨wrote, inPosts, _⟩ := commitYield_spec committedExact
  rw [writes] at wrote
  obtain ⟨edits, value, decoded, applied, exact⟩ := stateWrite_spec wrote
  have member : written.post ∈ delivery.posts := by
    rw [delivery.postsExact, yielded]
    simp only [List.mem_cons, List.mem_append, Option.map_some, Option.getD_some]
    exact Or.inr (Or.inl (Or.inl (Or.inr (inPosts written writes))))
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

/-- **An admitted delivery's fields bind the stored checkpoint.** A projection
of the `Delivery` witness, not a computation: its content is that `Delivery` is
`private mk`, built only by `deliver`, which decodes the machine state from the
record cell's own checkpoint bytes (whose digest the record and the await id
name) and resumes it with the typed outcome and view; nothing of the state
comes from the request. -/
theorem delivery_fields_bind_checkpoint {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    ∃ record state,
      readRecord snapshot request.record = some record ∧
      record.phase = .awaiting delivery.await ∧
      delivery.await.id = awaitId request.record record.generation (checkpointDigest record.checkpoint) ∧
      decodeCheckpoint record.checkpoint = some state ∧
      resume (responseData delivery.settlement.decided delivery.view).term state = some delivery.resumed ∧
      resumedSegment config snapshot height (deliveryTransaction delivery.await.id) request.record record.object
        (record.generation + 1) delivery.envelope.sourceTicks delivery.view delivery.resumed =
          .ok (delivery.segment, delivery.yielded) := by
  refine ⟨delivery.record, delivery.state, delivery.recordExact, delivery.awaiting, ?_, delivery.stateExact,
    delivery.resumeExact, delivery.endExact⟩
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
  have ends : (one.segment, one.yielded) = (two.segment, two.yielded) := by
    have a := one.endExact
    rw [awaits, sameRecord, records, envelopes, views, resumedEq, two.endExact] at a
    exact (Except.ok.inj a).symm
  have segments : one.segment = two.segment := congrArg Prod.fst ends
  have yieldeds : one.yielded = two.yielded := congrArg Prod.snd ends
  refine ⟨resumedEq, segments, ?_⟩
  rw [one.nextExact, two.nextExact, records, segments, yieldeds]

/-- Settling the purse keeps the ending turn's own postings first. -/
theorem settlePurse_prefix {config : Config} {book : Book} {held : AccountId} {escrow : Escrow}
    {deposit : Nat} {before batch : Batch} {segment : Segment}
    (ok : settlePurse config book held escrow deposit before segment = .ok batch) :
    ∃ rest, batch.operations = before.operations ++ rest := by
  unfold settlePurse at ok
  dsimp only at ok
  split at ok
  · split at ok
    · cases ok; exact ⟨[], by simp⟩
    · cases ok
  · cases ok; exact ⟨_, rfl⟩

/-- **No fee depends on computation.** The fee the ending turn takes from the
purse is the used half of the escrowed pair, chosen by how the await ended
(settled from the snapshot and height) and nothing else: two deliveries of the
same record at the same snapshot and height take the same amount, whatever
envelopes they declared and whatever their runs did, and the submitter's added
envelope is the public price of what it DECLARED. -/
theorem refund_measurement_free {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {first second : DeliverRequest} (one : Delivery config snapshot height first)
    (two : Delivery config snapshot height second) (sameRecord : first.record = second.record) :
    one.posted.batch.operations.head? =
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
  have posted : one.posted.batch.operations.head? =
      (deliveryCharges config one.record first.record one.settlement.path first
        (drainFee config one.object (one.yielded.bind YieldCommit.written))).operations.head? := by
    rw [one.postedBatch]
    obtain ⟨rest, prefix_⟩ := settlePurse_prefix one.batchExact
    rw [prefix_]
    simp [deliveryCharges]
  exact ⟨posted, by rw [records, settlements], by rw [records, settlements]⟩

/-- The submitter's charge for added envelope is the public price of what it
DECLARED, never of what ran. -/
theorem submitter_charge_declared (config : Config) (record : Record) (cell : CellId) (path : Path)
    (request : DeliverRequest) (migration : Nat) (extra : request.extra ≠ zeroCapacity) :
    Operation.fee request.account config.collector config.asset (config.tariff.workOf request.extra) ∈
      (deliveryCharges config record cell path request migration).operations := by
  simp [deliveryCharges, extra]

/-- A yield never leaves its purse short: the postings a yielding segment
commits leave at least the await's fee pair AND the storage deposit of the
record it commits in the purse, and add nothing to the turn's own postings. -/
theorem yield_reserves_pair (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (deposit : Nat) (before batch : Batch) (state : State) (plan : PlanAwait)
    (settled : settlePurse config book held escrow deposit before (.yielded state plan) = .ok batch) :
    batch = before ∧ escrow.pair + deposit ≤ purse (before.apply book) config.asset held := by
  unfold settlePurse at settled
  simp only [Segment.yields] at settled
  by_cases enough : escrow.pair + deposit ≤ purse (before.apply book) config.asset held
  · simp [enough] at settled
    exact ⟨settled.symm, enough⟩
  · simp [enough] at settled

/-- **A yield the purse cannot reserve is parked, by name**: when the purse after
the turn's own postings is short of the fee pair plus the deposit of the record
the yield would commit, the yield is refused `awaitsFunding`. -/
theorem yield_short_parks (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (deposit : Nat) (before : Batch) (state : State) (plan : PlanAwait)
    (short : purse (before.apply book) config.asset held < escrow.pair + deposit) :
    ∃ available reserve, settlePurse config book held escrow deposit before (.yielded state plan) =
      .error (.awaitsFunding available reserve) ∧ reserve = escrow.pair + deposit := by
  refine ⟨purse (before.apply book) config.asset held, escrow.pair + deposit, ?_, rfl⟩
  unfold settlePurse
  simp only [Segment.yields, if_true]
  rw [if_neg (Nat.not_le.mpr short)]

/-- **An ending segment sweeps the purse and closes it**: every positive
balance the purse holds after the turn's own postings goes to the payer's
account, and the purse is deregistered in the same batch. -/
theorem end_returns_purse (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (deposit : Nat) (before batch : Batch) (segment : Segment) (ends : segment.yields = false)
    (settled : settlePurse config book held escrow deposit before segment = .ok batch) :
    batch.registrations = before.registrations ∧
    batch.operations = before.operations ++ sweep (before.apply book) held escrow.account ∧
    batch.deregistrations = before.deregistrations ++ [held] := by
  unfold settlePurse at settled
  simp only [ends, Bool.false_eq_true, if_false, Except.ok.injEq] at settled
  subst settled
  exact ⟨rfl, rfl, rfl⟩

/-- **The deposit leaves the purse only at the end.** A settlement that adds any
posting to the turn's own (the only way purse funds reach the payer) is the
settlement of an ending segment: a yield adds nothing and closes nothing. -/
theorem purse_released_only_at_end (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (deposit : Nat) (before batch : Batch) (segment : Segment)
    (settled : settlePurse config book held escrow deposit before segment = .ok batch)
    (released : batch ≠ before) : segment.yields = false := by
  cases yields : segment.yields
  · rfl
  · unfold settlePurse at settled
    simp only [yields, if_true] at settled
    split at settled
    · exact absurd (Except.ok.inj settled).symm released
    · cases settled

/-- A yielding settlement adds nothing and leaves the reserve in the purse. -/
theorem settlePurse_yields (config : Config) (book : Book) (held : AccountId) (escrow : Escrow)
    (deposit : Nat) (before batch : Batch) (segment : Segment) (yields : segment.yields = true)
    (settled : settlePurse config book held escrow deposit before segment = .ok batch) :
    batch = before ∧ escrow.pair + deposit ≤ purse (before.apply book) config.asset held := by
  unfold settlePurse at settled
  simp only [yields, if_true] at settled
  split at settled
  · exact ⟨(Except.ok.inj settled).symm, by assumption⟩
  · cases settled

/-- **A resume re-prices the deposit**: a delivery that yields again leaves, in
the purse after its own postings, the fee pair plus the storage deposit of the
record it commits (`next`, at its new size). -/
theorem Delivery.yield_reserves_deposit {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request) (yields : delivery.segment.yields = true) :
    delivery.record.escrow.pair + storageDeposit config delivery.next ≤
      purse ((deliveryCharges config delivery.record request.record delivery.settlement.path request
        (drainFee config delivery.object (delivery.yielded.bind YieldCommit.written))).apply
        (logicalBook delivery.book.logical)) config.asset (heldAccount request.record) :=
  (settlePurse_yields _ _ _ _ _ _ _ _ yields delivery.batchExact).2

/-- The same at birth: the first yield reserves the pair and its record's deposit. -/
theorem Birth.yield_reserves_deposit {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : BirthRequest}
    (born : Birth config snapshot height request) (yields : born.segment.yields = true) :
    (escrowOf config.tariff request.subject request.escrowAccount request.resume request.timeout).pair +
        storageDeposit config born.record ≤ request.deposit := by
  have checked := born.funded
  simp only [yields, true_and, Nat.not_lt] at checked
  exact checked

/-- The deposit is a function of the record the yield commits: re-priced at
every yield from that record's encoded size. -/
theorem storageDeposit_awaiting (config : Config) (record : Record) (await : Await)
    (awaiting : record.phase = .awaiting await) :
    storageDeposit config record = config.storageRate * (encodeRecord record).length := by
  simp [storageDeposit, awaiting]

/-- **The deposit tracks the record's size**: at a positive rate, an awaiting
record whose encoding is longer reserves strictly more. -/
theorem storageDeposit_tracks_size (config : Config) (rate : 0 < config.storageRate)
    (smaller larger : Record) (one two : Await)
    (awaitingSmaller : smaller.phase = .awaiting one) (awaitingLarger : larger.phase = .awaiting two)
    (longer : (encodeRecord smaller).length < (encodeRecord larger).length) :
    storageDeposit config smaller < storageDeposit config larger := by
  rw [storageDeposit_awaiting config smaller one awaitingSmaller,
    storageDeposit_awaiting config larger two awaitingLarger]
  exact Nat.mul_lt_mul_of_pos_left longer rate

/-- An ended record reserves nothing: it is retired. -/
theorem storageDeposit_ended (config : Config) (record : Record) (ended : ∀ await, record.phase ≠ .awaiting await) :
    storageDeposit config record = 0 := by
  unfold storageDeposit
  cases phase : record.phase with
  | awaiting await => exact absurd phase (ended await)
  | done _ => rfl
  | faulted _ => rfl



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
  have ended := delivery.endExact
  rw [← envelopes, ← resumedEq, ← views, resumedSegment_exhausted_below_cap ex.ran ex.belowCap] at ended
  cases ended

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

/-- **A retired record refuses every turn on it, by name.** At a record
coordinate holding the retired image, a delivery, an exhaustion, an abandonment
and a top-up are each refused `recordRetired`, and a birth that would land on
it too. -/
theorem absentRecord_retired {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} {cell : CellId}
    (retired : isRetired (snapshot.canonicalBytes cell) = true) : absentRecord snapshot cell = .recordRetired := by
  simp [absentRecord, retired]

theorem deliver_retired_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (retired : isRetired (snapshot.canonicalBytes request.record) = true) :
    ∃ reason, deliver config snapshot height request = .error reason ∧ reason = .recordRetired := by
  have none := readRecord_of_retired retired
  unfold deliver
  split
  · exact ⟨_, rfl, absentRecord_retired retired⟩
  · rename_i record found; rw [none] at found; cases found

theorem exhaust_retired_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ExhaustRequest} (retired : isRetired (snapshot.canonicalBytes request.record) = true) :
    ∃ reason, exhaust config snapshot height request = .error reason ∧ reason = .recordRetired := by
  have none := readRecord_of_retired retired
  unfold exhaust
  split
  · exact ⟨_, rfl, absentRecord_retired retired⟩
  · rename_i record found; rw [none] at found; cases found

theorem abandon_retired_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (retired : isRetired (snapshot.canonicalBytes request.record) = true) :
    ∃ reason, abandon config snapshot height request = .error reason ∧ reason = .recordRetired := by
  have none := readRecord_of_retired retired
  unfold abandon
  split
  · exact ⟨_, rfl, absentRecord_retired retired⟩
  · rename_i record found; rw [none] at found; cases found

theorem topUp_retired_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {request : TopUpRequest} (retired : isRetired (snapshot.canonicalBytes request.record) = true) :
    ∃ reason, topUp config snapshot request = .error reason ∧ reason = .recordRetired := by
  have none := readRecord_of_retired retired
  unfold topUp
  split
  · exact ⟨_, rfl, absentRecord_retired retired⟩
  · rename_i record found; rw [none] at found; cases found

/-- A retired slot refuses a late decision by name. -/
theorem resolve_retired_refused {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : ResolveRequest}
    (retired : isRetired (snapshot.canonicalBytes (AnswerSlot.cell config.domain request.slot)) = true) :
    ∃ reason, resolve config snapshot height request = .error reason ∧ reason = .slotRetired := by
  have none := readSlot_of_retired retired
  unfold resolve
  split
  · exact ⟨_, rfl, by simp [absentSlot, retired]⟩
  · rename_i slot found; rw [none] at found; cases found

/-- A record that has ended is retired: its image is the retired image. -/
theorem recordImage_ended (record : Record) (ended : ∀ await, record.phase ≠ .awaiting await) :
    recordImage record = retiredImage := by
  unfold recordImage
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

/-- **Disposal retires the record.** A delivery whose segment ends (finished or
faulted) writes its record cell to the retired image: the checkpoint, the input
and the result leave the store in the turn that ends the activity, and the
coordinate is never reused (and `settlePurse` sweeps and closes the purse,
`end_returns_purse`). -/
theorem delivery_end_vacates {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (ends : delivery.segment.yields = false) :
    delivery.posts.head? = some (postAt snapshot request.record retiredImage) := by
  rw [delivery.recordFirst]
  have ended := nextRecord_ended delivery.record (delivery.record.generation + 1) delivery.segment
    delivery.yielded ends
  rw [← delivery.nextExact] at ended
  simp [recordPost, recordImage_ended _ ended]

/-- The same for a birth whose first segment already ends: no record is kept. -/
theorem birth_end_vacates {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (ends : born.segment.yields = false) :
    born.posts.head? = some (postAt snapshot born.cell retiredImage) := by
  rw [born.recordFirst]
  have ended : ∀ await, born.record.phase ≠ .awaiting await := by
    rw [born.recordExact]; exact nextRecord_ended _ _ _ _ ends
  simp [recordPost, recordImage_ended _ ended]

/-- **An ending delivery closes the purse on the Book.** After the delivery's
postings, the purse is no Book account: every later posting naming it (a top-up,
a fee) is refused by the Book, which names it unregistered
(`CanonicalResourceKernel.deregistered_refuses_posting`). -/
theorem Delivery.end_closes_purse {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (ends : delivery.segment.yields = false) :
    heldAccount request.record ∉ (logicalBook delivery.posted.post.logical).accounts := by
  have closed := (end_returns_purse _ _ _ _ _ _ _ _ ends delivery.batchExact).2.2
  rw [Postings.post, delivery.posted.accepted.post_logicalBook, delivery.postedBatch]
  exact CanonicalResourceKernel.Batch.apply_deregistered _ _ _ (by rw [closed]; simp)

/-- **An abandonment closes the purse on the Book**, and retires the record. -/
theorem Abandonment.closes_purse {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : AbandonRequest} (ab : Abandonment config snapshot height request) :
    heldAccount request.record ∉ (logicalBook ab.posted.post.logical).accounts ∧
      ab.posts.head? = some (postAt snapshot request.record retiredImage) := by
  refine ⟨?_, by rw [ab.postsExact]; rfl⟩
  rw [Postings.post, ab.posted.accepted.post_logicalBook, ab.postedBatch]
  exact CanonicalResourceKernel.Batch.apply_deregistered _ _ _ (by simp [abandonCharges])

/-- **Settled slots are reclaimed.** Whenever a reply await settles (decided,
or expired at its deadline), the settlement reclaims its slot cell. -/
theorem settle_reclaims_slot {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement} {name : Digest} {decider : SubjectId}
    (source : await.source = .reply name decider)
    (settled : settle config snapshot height cell await = .ok settlement) :
    settlement.posts = [slotRetire config snapshot name] := by
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
    slotRetire config snapshot name ∈ delivery.posts := by
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
    ab.posts.head? = some (postAt snapshot request.record retiredImage) ∧
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
    slotRetire config snapshot name ∈ ab.posts ∧ AnswerSlot.decisionClaim name ∈ ab.claims := by
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
    ∃ object, readObject config snapshot request.object = .ok (some object) ∧ object.activePin = request.pin ∧
      admitWrite object (factsOf request.subject height request.object request.factsTurn (some request.pin))
        (written.before.map ObjectState.value) written.after.value = .ok () :=
  ⟨born.object, born.objectExact, born.pinned, judgeWritten_ok born.judged written wrote⟩

/-- **`activity_write_judged`, delivery.** The object's record is read in the
delivering turn, and the segment's write is admitted by its law with the
activity's principal (never the deliverer) as the subject. -/
theorem Delivery.write_judged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (written : StateWritten) (wrote : delivery.yielded.bind YieldCommit.written = some written) :
    ∃ object, readObject config snapshot delivery.record.object = .ok (some object) ∧
      admitWrite object (factsOf delivery.record.escrow.payer height delivery.record.object 2
        (some delivery.record.pin))
        (written.before.map ObjectState.value) written.after.value = .ok () :=
  ⟨delivery.object, delivery.objectExact, judgeWritten_ok delivery.judged written wrote⟩

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
    (found : readObject config snapshot request.object = .ok (some object)) (admits : object.admitsNew = true)
    (other : object.activePin ≠ request.pin) :
    birth config snapshot height request = .error (.pinMismatch object.activePin request.pin) := by
  unfold birth
  split
  · rename_i reason found'; rw [found] at found'; cases found'
  · rename_i found'; rw [found] at found'; cases found'
  · rename_i object' found'
    rw [found] at found'
    cases found'
    simp [admits, other]
    try rfl

/-- **`draining_refuses_births`** (brief §2, theorem 4). On an object draining
toward a state type its old one is not a value subtype of, a birth is refused
`draining`, whatever it names. -/
theorem draining_refuses_births {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} {object : ObjectRecord} {next : ObjectRecord.Pending} {deadline : Nat}
    (found : readObject config snapshot request.object = .ok (some object))
    (draining : object.phase = .draining next deadline)
    (notSubtype : ObjectStateType.stateSubtype object.stateType next.stateType = false) :
    birth config snapshot height request = .error .draining := by
  have refused : object.admitsNew = false := by simp [ObjectRecord.admitsNew, draining, notSubtype]
  unfold birth
  split
  · rename_i reason found'; rw [found] at found'; cases found'
  · rename_i found'; rw [found] at found'; cases found'
  · rename_i object' found'
    rw [found] at found'
    cases found'
    simp [refused]
    try rfl

/-- A delivery of an activity the object no longer runs (left on the old package
after a migration, chosen for rebirth) is refused before anything runs. -/
theorem Delivery.runs_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request) :
    delivery.object.runs delivery.record.pin = true := delivery.runsPin

/-- **A second record is refused.** -/
theorem create_refuses_existing {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} {object : ObjectRecord}
    (found : readObject config snapshot request.object = .ok (some object)) :
    create config snapshot height request = .error .objectExists := by
  unfold create
  split
  · rename_i reason found'; rw [found] at found'; cases found'
  · rfl
  · rename_i found'; rw [found] at found'; cases found'

/-! ## The package pin: installed at creation, passed by every package turn, refused to every other

The pin is the kernel's clause on an object's declared state (`ObjectRecord.pinClause`):
every write is judged by `ObjectRecord.effectiveLaw record = all [pinClause record.pin, record.law]`,
whatever law the creator supplied. The clause is not stored beside the creator's law, it is
derived from the record's `pin`, so no creator can omit or loosen it and nothing but the record's
own `pin` (written once, by `create`) says what it is. The turns that write declared state, and the
artifact each makes its write under:

| turn | artifact slot (`factsOf`) |
|---|---|
| `birth` | `request.pin`, which is `object.activePin` (`birth_refuses_other_pin`) |
| `deliver` | the activity record's `pin`, one the object still runs (`Delivery.runs_pin`) |
| `invoke` call frames, `deliverMessage` frames | the frame's own object's `activePin` (`ObjectiveCall.Ctx.facts`) |

The judged clause is `objectivePin record.pins`: the pin, and while the object drains toward an
upgrade also the next pin (`ObjectRecord.pins`), so old activities and identity-migration
births both pass it; MIGRATE re-pins by writing the record's `pin`.
| `create` seed | none, and not judged by the pin: the creator's law only (turn 4); nothing has run |
-/

theorem nextRecord_pin (base : Record) (generation : Nat) (segment : Segment) (yielded : Option YieldCommit) :
    (nextRecord base generation segment yielded).pin = base.pin := by
  cases segment <;> cases yielded <;> rfl

/-- The record an admitted birth installs pins the package the object runs for it. -/
theorem Birth.record_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request) :
    born.record.pin = born.object.activePin := by
  rw [born.recordExact, nextRecord_pin]
  exact born.pinned.symm

/-- **`objective_turns_pass_pin`, birth.** The write of an admitted birth is judged under the
artifact `request.pin`, which is the pin of the object it is judged by: the object's pin clause
accepts it on the very views the law judged. -/
theorem Birth.write_passes_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (written : StateWritten) (wrote : born.yielded.bind YieldCommit.written = some written) :
    ∃ before after,
      ObjectRecord.views (factsOf request.subject height request.object request.factsTurn (some request.pin))
        (written.before.map ObjectState.value) written.after.value = some (before, after) ∧
      Minidregg.Pred.eval (Minidregg.Pred.objectivePin born.object.pins) before after = true := by
  have admitted := judgeWritten_ok born.judged written wrote
  obtain ⟨⟨before, after, viewed, _⟩, _⟩ := (ObjectRecord.admitWrite_ok_iff _ _ _ _).mp admitted
  refine ⟨before, after, viewed,
    ObjectRecord.objectivePin_accepts_run _ _ _ _ request.pin.value (by simp [factsOf]) ?_ before after viewed⟩
  rw [← born.pinned]
  exact ObjectRecord.activePin_mem_pins born.object

/-- **`objective_turns_pass_pin`, delivery.** The write of an admitted delivery is judged under
the artifact of the activity record's pin; where that is the object's pin (every activity a
birth made: `Birth.record_pin`), the object's pin clause accepts it. -/
theorem Delivery.write_passes_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    (written : StateWritten) (wrote : delivery.yielded.bind YieldCommit.written = some written) :
    ∃ before after,
      ObjectRecord.views (factsOf delivery.record.escrow.payer height delivery.record.object 2
          (some delivery.record.pin))
        (written.before.map ObjectState.value) written.after.value = some (before, after) ∧
      Minidregg.Pred.eval (Minidregg.Pred.objectivePin delivery.object.pins) before after = true := by
  have admitted := judgeWritten_ok delivery.judged written wrote
  obtain ⟨⟨before, after, viewed, _⟩, _⟩ := (ObjectRecord.admitWrite_ok_iff _ _ _ _).mp admitted
  exact ⟨before, after, viewed,
    ObjectRecord.objectivePin_accepts_run _ _ _ _ delivery.record.pin.value (by simp [factsOf])
      (ObjectRecord.runs_mem_pins delivery.runsPin) before after viewed⟩

/-- **No creator law removes the pin**: for every record, a view the judged law accepts is one
the pin clause accepts. -/
theorem pin_in_every_judged_law (record : ObjectRecord) (old new : Minidregg.Pred.State)
    (admitted : Minidregg.Pred.eval record.effectiveLaw old new = true) :
    Minidregg.Pred.eval (Minidregg.Pred.objectivePin record.pins) old new = true :=
  ((ObjectRecord.effectiveLaw_accepts_iff record old new).mp admitted).1

#assert_axioms nextRecord_pin
#assert_axioms Birth.record_pin
#assert_axioms Birth.write_passes_pin
#assert_axioms Delivery.write_passes_pin
#assert_axioms pin_in_every_judged_law
#assert_axioms execute_accepted_install
#assert_axioms spent_claim_never_accepted
#assert_axioms installed_retry_replays
#assert_axioms Delivery.spends
#assert_axioms resume_consumes_once
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
#assert_axioms delivery_fields_bind_checkpoint
#assert_axioms faultOr_refused
#assert_axioms faultOr_ok
#assert_axioms resumedSegment_never_refuses_program_fault
#assert_axioms resumedSegment_committed
#assert_axioms resumedSegment_yielded
#assert_axioms resumedSegment_exhausted_below_cap
#assert_axioms plan_fault_commits
#assert_axioms funding_is_not_a_fault
#assert_axioms law_denial_is_not_a_fault
#assert_axioms exhaustion_below_cap_is_not_a_fault
#assert_axioms resume_deterministic
#assert_axioms settlePurse_prefix
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
#assert_axioms isRetired_retiredImage
#assert_axioms payloadOf_retired
#assert_axioms readRecord_of_retired
#assert_axioms readSlot_of_retired
#assert_axioms absentRecord_retired
#assert_axioms deliver_retired_refused
#assert_axioms exhaust_retired_refused
#assert_axioms abandon_retired_refused
#assert_axioms topUp_retired_refused
#assert_axioms resolve_retired_refused
#assert_axioms recordImage_ended
#assert_axioms yield_short_parks
#assert_axioms purse_released_only_at_end
#assert_axioms storageDeposit_awaiting
#assert_axioms settlePurse_yields
#assert_axioms Delivery.yield_reserves_deposit
#assert_axioms Birth.yield_reserves_deposit
#assert_axioms storageDeposit_tracks_size
#assert_axioms storageDeposit_ended
#assert_axioms Delivery.end_closes_purse
#assert_axioms Abandonment.closes_purse
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
#assert_axioms birth_refuses_non_object
#assert_axioms birth_refuses_other_pin
#assert_axioms draining_refuses_births
#assert_axioms create_refuses_existing

/-! ## Retention: every retained activity cell names its payer

Retained storage is paid for. Every activity cell a turn leaves LIVE (an activity
payload at its coordinate) names the Book account that pays for its retention,
read from the cell's own bytes along its role's route (`payerOf`):

| role      | route            | payer                                          |
|-----------|------------------|------------------------------------------------|
| `record`  | `escrow`         | the record's `escrow.account`                  |
| `slot`    | `activityOfSlot` | the escrow of the awaiting record it answers   |
| `state`   | `objectOfState`  | `ObjectRecord.payer` of the object its key names |
| `package` | `stored`         | the package cell's `Stored.payer`              |
| `object`  | `objectRecord`   | the record's own `ObjectRecord.payer`          |

An ended record and a settled slot are RETIRED: they hold no payload and nobody
retains them. The census (`activityCensus`) lists every role with its route and
is checked complete and paid (`retention_census_paid`); a census with one more
retained kind that names no payer fails the same check (`planted_census_unpaid`).
`payerOf` matches on the role, so a new role cannot be added without naming its
route. The semantic half is stated over the real post-state of each admitted
turn (`afterPosts`, which is `DataSnapshot.install`'s bytes, `install_afterPosts`):
every cell the turn writes that holds a payload afterwards resolves to a payer
(`Birth.retention_cells_have_payer`, `Delivery.retention_cells_have_payer`,
`Exhaustion.retention_cells_have_payer`, `Publication.retention_cells_have_payer`,
`Creation.retention_cells_have_payer`,
`Resolution.retention_cells_have_payer`; a top-up leaves no live activity cell, an
abandonment only the object record, whose route is its own payer). The Book side of the accounting is `Batch.deregistrations`: an
ending turn closes the purse it emptied (`Delivery.end_closes_purse`,
`Abandonment.closes_purse`). -/

/-- Where a retained cell's payer is read from. -/
inductive PayerRoute where
  | escrow
  | activityOfSlot
  | objectOfState
  | objectRecord
  | stored
  /-- An inbox: its sender object's payer. -/
  | objectOfInbox
  deriving DecidableEq, Repr

def payerRoute : Role → Option PayerRoute
  | .record => some .escrow
  | .slot => some .activityOfSlot
  | .state => some .objectOfState
  | .package => some .stored
  | .object => some .objectRecord
  | .inbox => some .objectOfInbox

/-- A census of retained cell kinds: every kind listed, each with its payer route. -/
structure RetentionCensus (Kind : Type) where
  kinds : List Kind
  complete : ∀ kind, kind ∈ kinds
  route : Kind → Option PayerRoute

/-- Every listed kind names a payer route. -/
def RetentionCensus.Paid {Kind : Type} (census : RetentionCensus Kind) : Prop :=
  ∀ kind ∈ census.kinds, (census.route kind).isSome = true

instance {Kind : Type} (census : RetentionCensus Kind) : Decidable census.Paid := by
  unfold RetentionCensus.Paid; infer_instance

/-- The activity registry's retained kinds: every activity role. -/
def activityCensus : RetentionCensus Role where
  kinds := [.record, .slot, .state, .package, .object, .inbox]
  complete := by intro kind; cases kind <;> simp
  route := payerRoute

/-- **`retention_cells_have_payer`, the census half**: every retained kind of the
activity registry names its payer route. -/
theorem retention_census_paid : activityCensus.Paid := by decide

/-- The tooth: the same census with one more retained kind that names no payer. -/
def plantedCensus : RetentionCensus (Option Role) where
  kinds := none :: activityCensus.kinds.map some
  complete := by
    intro kind
    cases kind with
    | none => simp
    | some role => cases role <;> simp [activityCensus]
  route
    | none => none
    | some role => payerRoute role

theorem planted_census_unpaid : ¬ plantedCensus.Paid := by decide

/-- The record a record cell holds, over any byte map. -/
def recordAt (bytesAt : CellId → Bytes) (cell : CellId) : Option Record :=
  (bodyOf .record (bytesAt cell)).bind decodeRecord

/-- The object record of an object, over any byte map. -/
def objectAt (config : Config) (bytesAt : CellId → Bytes) (object : CellId) : Option ObjectRecord :=
  (bodyOf .object (bytesAt (objectCell config.domain object))).bind ObjectRecord.decodeRecord

/-- The inbox an inbox cell holds, over any byte map. -/
def inboxAt (bytesAt : CellId → Bytes) (cell : CellId) : Option Inbox.Inbox :=
  (bodyOf .inbox (bytesAt cell)).bind Inbox.decode

/-- The payer a payload's route resolves to. A slot's is its awaiting
activity's escrow account, or (a delivery slot) its inbox's sender's payer. -/
def routePayer (config : Config) (bytesAt : CellId → Bytes) (payload : ObjectiveActivityCell.Payload) :
    PayerRoute → Option AccountId
  | .escrow => (decodeRecord payload.body).map fun record => record.escrow.account
  | .activityOfSlot => (AnswerSlot.decode payload.body).bind fun slot =>
      ((recordAt bytesAt slot.activity).map fun record => record.escrow.account).orElse fun _ =>
        (inboxAt bytesAt slot.activity).bind fun inbox => (objectAt config bytesAt ⟨inbox.sender⟩).map ObjectRecord.payer
  | .objectOfInbox => (Inbox.decode payload.body).bind fun inbox =>
      (objectAt config bytesAt ⟨inbox.sender⟩).map ObjectRecord.payer
  | .objectOfState => (digestStream.toLawful.decode payload.key).bind fun object =>
      (objectAt config bytesAt object).map ObjectRecord.payer
  | .objectRecord => (ObjectRecord.decodeRecord payload.body).map ObjectRecord.payer
  | .stored => (decodeStored payload.body).map Stored.payer

/-- The payer of a cell's bytes: its payload's role's route. -/
def payerOfBytes (config : Config) (bytesAt : CellId → Bytes) (bytes : Bytes) : Option AccountId := do
  let payload ← payloadOf bytes
  let route ← payerRoute payload.role
  routePayer config bytesAt payload route

/-- The payer of a cell. -/
def payerOf (config : Config) (bytesAt : CellId → Bytes) (cell : CellId) : Option AccountId :=
  payerOfBytes config bytesAt (bytesAt cell)

/-- Every listed cell that holds an activity payload has a payer. -/
def CellsPaid (config : Config) (bytesAt : CellId → Bytes) (cells : List CellId) : Prop :=
  ∀ cell ∈ cells, (payloadOf (bytesAt cell)).isSome = true → (payerOf config bytesAt cell).isSome = true

/-- The bytes after a turn's posts: the first post at a cell, else the snapshot's. -/
def afterPosts {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post)
    (cell : CellId) : Bytes :=
  ((posts.find? fun post => post.cell = cell).map Post.bytes).getD (snapshot.canonicalBytes cell)

theorem lookupPostBytes_posts (rootBytes : Bytes → Digest) (cell : CellId) :
    ∀ posts : List Post, DataSnapshot.lookupPostBytes cell (posts.map (Post.write rootBytes)) =
      (posts.find? fun post => post.cell = cell).map Post.bytes
  | [] => rfl
  | post :: rest => by
    simp only [List.map_cons, DataSnapshot.lookupPostBytes, List.find?_cons]
    by_cases same : post.cell = cell
    · simp [same, Post.write]
    · simp [same, Post.write, lookupPostBytes_posts rootBytes cell rest]

/-- **`afterPosts` is the installed state**: the bytes `DataSnapshot.install`
leaves for a kernel intent. -/
theorem install_afterPosts {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes)
    (transaction : TransactionId) (posts : List Post) (guards : List ReadGuard)
    (nullifiers : List StableNullifier) (sealing : Seal) (cell : CellId) :
    (DataSnapshot.install snapshot (intentOf rootBytes transaction posts guards nullifiers sealing)).canonicalBytes
      cell = afterPosts snapshot posts cell := by
  rw [DataSnapshot.install_canonicalBytes, intentOf_writes, lookupPostBytes_posts]
  rfl

theorem afterPosts_first {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (first : Post)
    (rest : List Post) : afterPosts snapshot (first :: rest) first.cell = first.bytes := by
  simp [afterPosts]

theorem afterPosts_unwritten {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post)
    (cell : CellId) (unwritten : ∀ post ∈ posts, post.cell ≠ cell) :
    afterPosts snapshot posts cell = snapshot.canonicalBytes cell := by
  unfold afterPosts
  rw [List.find?_eq_none.mpr (fun post member => by simpa using unwritten post member)]
  rfl

theorem afterPosts_mem {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post)
    (post : Post) (member : post ∈ posts) :
    ∃ found ∈ posts, afterPosts snapshot posts post.cell = found.bytes := by
  unfold afterPosts
  cases found : posts.find? (fun candidate => candidate.cell = post.cell) with
  | none =>
    have := List.find?_eq_none.mp found post member
    simp at this
  | some first => exact ⟨first, List.mem_of_find?_eq_some found, rfl⟩

/-- Reduce a turn's census to its posts: if every post holding a payload has a
payer in the post-state, every written cell does. -/
theorem cellsPaid_of_posts {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post)
    (each : ∀ post ∈ posts, (payloadOf post.bytes).isSome = true →
      (payerOfBytes config (afterPosts snapshot posts) post.bytes).isSome = true) :
    CellsPaid config (afterPosts snapshot posts) (posts.map Post.cell) := by
  intro cell member live
  obtain ⟨post, inPosts, rfl⟩ := List.mem_map.mp member
  obtain ⟨found, foundIn, exact⟩ := afterPosts_mem snapshot posts post inPosts
  unfold payerOf
  rw [exact] at live ⊢
  exact each found foundIn live

theorem payloadOf_image (role : Role) (key body : Bytes) :
    payloadOf (image role key body) = some ⟨role, key, body⟩ := by
  unfold payloadOf image
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry
      (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩) =
    (LifecycleImage.codec CanonicalCellRegistry.registry).encode
      (.live ⟨.objectiveActivity, ObjectiveActivityCell.cellOf ⟨role, key, body⟩⟩) from rfl,
    LifecycleImage.decode_encode]
  simp

theorem bodyOf_image (role : Role) (key body : Bytes) : bodyOf role (image role key body) = some body := by
  simp [bodyOf, payloadOf_image]

/-- A live Book image is no activity cell. -/
theorem payloadOf_book (book : BookCell) :
    payloadOf (LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, book⟩)) = none := by
  unfold payloadOf
  rw [show LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, book⟩) =
    (LifecycleImage.codec CanonicalCellRegistry.registry).encode (.live ⟨.resourceBook, book⟩) from rfl,
    LifecycleImage.decode_encode]

theorem objectAt_of_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {object : CellId} {record : ObjectRecord} (read : readObject config snapshot object = .ok (some record)) :
    objectAt config snapshot.canonicalBytes object = some record := by
  unfold readObject objectFor at read
  unfold objectAt
  cases present : payloadOf (snapshot.canonicalBytes (objectCell config.domain object)) with
  | none => rw [present] at read; cases read
  | some payload =>
    rw [present] at read
    simp only at read
    split at read
    · rename_i owned
      cases hd : ObjectRecord.decodeRecord payload.body with
      | none => rw [hd] at read; cases read
      | some found =>
        rw [hd] at read
        cases read
        simp [bodyOf, present, owned.1, hd]
    · cases read

/-- The payer of a record image: its escrow's account. -/
theorem payer_record_image (config : Config) (bytesAt : CellId → Bytes) (record : Record) (await : Await)
    (awaiting : record.phase = .awaiting await) :
    payerOfBytes config bytesAt (recordImage record) = some record.escrow.account := by
  simp [recordImage, awaiting, payerOfBytes, payloadOf_image, payerRoute, routePayer, record_roundTrip]

theorem payloadOf_recordImage_live (record : Record) (live : (payloadOf (recordImage record)).isSome = true) :
    ∃ await, record.phase = .awaiting await := by
  unfold recordImage at live
  split at live
  · exact ⟨_, by assumption⟩
  · rw [payloadOf_retired] at live; cases live
  · rw [payloadOf_retired] at live; cases live

/-- The payer of a slot image whose activity is the record a byte map holds. -/
theorem payer_slot_image (config : Config) (bytesAt : CellId → Bytes) (slot : AnswerSlot.Slot) (record : Record)
    (held : recordAt bytesAt slot.activity = some record) :
    payerOfBytes config bytesAt (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) =
      some record.escrow.account := by
  simp [payerOfBytes, payloadOf_image, payerRoute, routePayer, AnswerSlot.roundTrip, held]

/-- The payer of a state image whose object's record a byte map holds. -/
theorem payer_state_image (config : Config) (bytesAt : CellId → Bytes) (object : CellId) (state : ObjectState)
    (record : ObjectRecord) (held : objectAt config bytesAt object = some record) :
    payerOfBytes config bytesAt (stateImage object state) = some record.payer := by
  have key : digestStream.toLawful.decode (stateKey object) = some object :=
    digestStream.toLawful.decode_encode object
  simp [payerOfBytes, stateImage, payloadOf_image, payerRoute, routePayer, key, held]

theorem recordAt_recordImage (bytesAt : CellId → Bytes) (cell : CellId) (record : Record) (await : Await)
    (awaiting : record.phase = .awaiting await) (holds : bytesAt cell = recordImage record) :
    recordAt bytesAt cell = some record := by
  simp [recordAt, holds, recordImage, awaiting, bodyOf_image, record_roundTrip]

/-- What a yield commit posts: the declared-state write (a state image of the
object) and, for a reply await, the slot it opens for this record cell, OPEN
(`slot.phase = .opened`: a yield decides nothing). -/
theorem commitYield_posts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {plan : PlanAwait} {committed : YieldCommit}
    (ok : commitYield config snapshot height transaction cell object generation checkpoint current viewed plan =
      .ok committed) :
    ∀ post ∈ committed.posts, (∃ state, post.bytes = stateImage object state) ∨
      (∃ slot : AnswerSlot.Slot, slot.activity = cell ∧ slot.phase = .opened ∧
        post.bytes = image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) := by
  have stateShape : ∀ written : Option StateWritten,
      stateWrite config snapshot object current viewed plan.write = .ok written →
      ∀ post ∈ (written.map StateWritten.post).toList, ∃ state, post.bytes = stateImage object state := by
    intro written wrote post member
    cases written with
    | none => simp at member
    | some one =>
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
      subst member
      obtain ⟨_, _, _, _, exact⟩ := stateWrite_spec wrote
      subst exact
      exact ⟨_, rfl⟩
  unfold commitYield at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · rename_i written wrote
      split at ok
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          intro post member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with inState | isSlot
          · exact .inl (stateShape _ wrote post inState)
          · subst isSlot
            exact .inr ⟨_, rfl, rfl, rfl⟩
      · split at ok
        · cases ok
        · simp only [Except.ok.injEq] at ok
          subst ok
          intro post member
          exact .inl (stateShape _ wrote post member)

/-- The record a yielding segment commits is awaiting. -/
theorem nextRecord_yielded_awaiting (base : Record) (generation : Nat) (segment : Segment)
    (committed : YieldCommit) (yields : ∃ state plan, segment = .yielded state plan) :
    ∃ await, (nextRecord base generation segment (some committed)).phase = .awaiting await := by
  obtain ⟨state, plan, rfl⟩ := yields
  exact ⟨committed.await, rfl⟩

theorem Postings.write_payload {rootBytes : Bytes → Digest} {pre : BookCell} (config : Config)
    (snapshot : Snapshot rootBytes) (posted : Postings pre) :
    payloadOf (posted.write config snapshot).bytes = none :=
  payloadOf_book posted.post

theorem slotImage_live (slot : AnswerSlot.Slot) :
    (payloadOf (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))).isSome = true := by
  simp [payloadOf_image]

/-- What a post of a turn is, for the census: a state image of the object, a
slot image for the record cell, a retired image, no activity cell (the Book), or
the object's record (its counters moved). -/
def CensusPost (object cell : CellId) (post : Post) : Prop :=
  (∃ state, post.bytes = stateImage object state) ∨
    (∃ slot : AnswerSlot.Slot, slot.activity = cell ∧
      post.bytes = image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) ∨
    post.bytes = retiredImage ∨ payloadOf post.bytes = none ∨ (∃ record, post.bytes = objectImage object record)

/-- The payer of an object record image: the record's own payer. -/
theorem payer_object_image (config : Config) (bytesAt : CellId → Bytes) (object : CellId) (record : ObjectRecord) :
    payerOfBytes config bytesAt (objectImage object record) = some record.payer := by
  simp [payerOfBytes, objectImage, payloadOf_image, payerRoute, routePayer, ObjectRecord.record_roundTrip]

/-- An object image is no slot image. -/
theorem objectImage_ne_slot (object : CellId) (record : ObjectRecord) (slot : AnswerSlot.Slot) :
    objectImage object record ≠ image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot) := by
  intro same
  have roles := congrArg (fun bytes => (payloadOf bytes).map (·.role)) same
  simp [objectImage, payloadOf_image] at roles

/-- The object record a byte map holds after posts that write the object cell only
with object images: the snapshot's (unwritten), or the first one posted. -/
theorem objectAt_afterPosts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {posts : List Post} {object : CellId} {objectRecord : ObjectRecord}
    (objectRead : readObject config snapshot object = .ok (some objectRecord))
    (objectOnly : ∀ post ∈ posts, post.cell = objectCell config.domain object →
      ∃ record, post.bytes = objectImage object record) :
    ∃ record, objectAt config (afterPosts snapshot posts) object = some record := by
  unfold afterPosts
  cases found : posts.find? (fun post => post.cell = objectCell config.domain object) with
  | none =>
    refine ⟨objectRecord, ?_⟩
    have read := objectAt_of_read objectRead
    unfold objectAt at read ⊢
    simpa [found] using read
  | some post =>
    have member := List.mem_of_find?_eq_some found
    have at_ : post.cell = objectCell config.domain object := by simpa using List.find?_some found
    obtain ⟨record, bytes⟩ := objectOnly post member at_
    refine ⟨record, ?_⟩
    unfold objectAt
    simp [found, bytes, objectImage, bodyOf_image, ObjectRecord.record_roundTrip]

/-- The census of a record-first turn: the record post heads the turn's posts;
the rest are the yield's state images (of `object`) and slot images (for this
record cell), retired images, or the Book; a slot is opened only beside an
awaiting record; the object's record is read under a cell no post writes. -/
theorem recordFirst_cells_paid {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (cell object : CellId) (record : Record) (objectRecord : ObjectRecord)
    (objectRead : readObject config snapshot object = .ok (some objectRecord))
    (rest : List Post) (shape : ∀ post ∈ rest, CensusPost object cell post)
    (slotsNeedRecord : (∃ post ∈ rest, ∃ slot : AnswerSlot.Slot, slot.activity = cell ∧
        post.bytes = image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) →
      ∃ await, record.phase = .awaiting await)
    (objectOnly : ∀ post ∈ recordPost config snapshot cell record :: rest,
      post.cell = objectCell config.domain object → ∃ held, post.bytes = objectImage object held) :
    CellsPaid config (afterPosts snapshot (recordPost config snapshot cell record :: rest))
      ((recordPost config snapshot cell record :: rest).map Post.cell) := by
  apply cellsPaid_of_posts
  obtain ⟨objectHeldRecord, objectHeld⟩ := objectAt_afterPosts objectRead objectOnly
  have headBytes : afterPosts snapshot (recordPost config snapshot cell record :: rest) cell = recordImage record :=
    afterPosts_first snapshot (recordPost config snapshot cell record) rest
  intro post member live
  rcases List.mem_cons.mp member with head | inRest
  · subst head
    obtain ⟨await, awaiting⟩ := payloadOf_recordImage_live record live
    show (payerOfBytes config _ (recordImage record)).isSome = true
    rw [payer_record_image config _ record await awaiting]
    rfl
  · rcases shape post inRest with ⟨state, isState⟩ | ⟨slot, activity, isSlot⟩ | retired | none | ⟨held, isObject⟩
    · rw [isState, payer_state_image config _ object state objectHeldRecord objectHeld]
      rfl
    · obtain ⟨await, awaiting⟩ := slotsNeedRecord ⟨post, inRest, slot, activity, isSlot⟩
      have held := recordAt_recordImage (afterPosts snapshot (recordPost config snapshot cell record :: rest))
        slot.activity record await awaiting (by rw [activity]; exact headBytes)
      rw [isSlot, payer_slot_image config _ slot record held]
      rfl
    · rw [retired, payloadOf_retired] at live; cases live
    · rw [none] at live; cases live
    · rw [isObject, payer_object_image]
      rfl

/-- A yield commit's posts are census posts of its object and record cell. -/
theorem segmentCommit_census {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {yielded : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment =
      .ok yielded) :
    ∀ post ∈ (yielded.map YieldCommit.posts).getD [], CensusPost object cell post := by
  intro post member
  cases yielded with
  | none => simp at member
  | some committed =>
    obtain ⟨_, _, _, committedOk⟩ := segmentCommit_spec ok
    exact (commitYield_posts committedOk post member).elim .inl
      (fun ⟨slot, activity, _, isSlot⟩ => .inr (.inl ⟨slot, activity, isSlot⟩))

/-- A turn that opens a slot commits an awaiting record. -/
theorem segmentCommit_awaiting {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat}
    {current : Option ObjectState} {viewed : Bool} {segment : Segment} {yielded : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation current viewed segment =
      .ok yielded) (base : Record) (generation' : Nat)
    (opens : ∃ post ∈ (yielded.map YieldCommit.posts).getD [], (payloadOf post.bytes).isSome = true) :
    ∃ await, (nextRecord base generation' segment yielded).phase = .awaiting await := by
  cases yielded with
  | none => obtain ⟨post, member, _⟩ := opens; simp at member
  | some committed =>
    obtain ⟨state, plan, rfl, _⟩ := segmentCommit_spec ok
    exact ⟨committed.await, rfl⟩

theorem slotPosted_live {post : Post} {slot : AnswerSlot.Slot}
    (isSlot : post.bytes = image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot)) :
    (payloadOf post.bytes).isSome = true := by
  rw [isSlot]; exact slotImage_live slot

/-- **`retention_cells_have_payer`, birth.** Every cell an admitted birth leaves
holding an activity payload names its payer in the installed state: the record
its escrow account, the opened slot that record's, the state cell its object's
`ObjectRecord.payer`, the object record (its counters moved) its own payer.
(Premise: a post of the birth lands on the object's record cell only as an
object image, i.e. no other coordinate collides with it.) -/
theorem Birth.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : BirthRequest} (born : Birth config snapshot height request)
    (objectOnly : ∀ post ∈ born.posts, post.cell = objectCell config.domain request.object →
      ∃ held, post.bytes = objectImage request.object held) :
    CellsPaid config (afterPosts snapshot born.posts) (born.posts.map Post.cell) := by
  have commits := segmentCommit_census born.yieldedExact
  rw [born.postsExact] at objectOnly ⊢
  apply recordFirst_cells_paid config snapshot born.cell request.object born.record born.object born.objectExact
  · intro post member
    rcases List.mem_append.mp member with inFront | inCount
    · rcases List.mem_append.mp inFront with inYield | isBook
      · exact commits post inYield
      · simp only [List.mem_singleton] at isBook
        subst isBook
        exact .inr (.inr (.inr (.inl (Postings.write_payload config snapshot born.posted))))
    · rw [mem_objectPost inCount]
      exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))
  · rintro ⟨post, inRest, slot, _, isSlot⟩
    rcases List.mem_append.mp inRest with inFront | inCount
    · rcases List.mem_append.mp inFront with inYield | isBook
      · rw [born.recordExact]
        exact segmentCommit_awaiting born.yieldedExact _ 0 ⟨post, inYield, slotPosted_live isSlot⟩
      · simp only [List.mem_singleton] at isBook
        subst isBook
        have live := slotPosted_live isSlot
        rw [Postings.write_payload] at live
        cases live
    · rw [mem_objectPost inCount] at isSlot
      exact absurd isSlot (objectImage_ne_slot _ _ slot)
  · exact objectOnly

/-- A settlement's posts retire the settled slot. -/
theorem settle_posts_retired {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {cell : CellId} {await : Await} {settlement : Settlement}
    (settled : settle config snapshot height cell await = .ok settlement) :
    ∀ post ∈ settlement.posts, post.bytes = retiredImage := by
  cases source : await.source with
  | reply name decider =>
    rw [settle_reclaims_slot source settled]
    intro post member
    simp only [List.mem_singleton] at member
    subst member; rfl
  | height due =>
    unfold settle at settled
    rw [source] at settled
    simp only at settled
    split at settled
    · cases settled; intro post member; simp at member
    · split at settled
      · cases settled; intro post member; simp at member
      · cases settled

/-- **`retention_cells_have_payer`, delivery.** Every cell an admitted delivery
leaves live names its payer: the record its escrow (it still awaits, or it is
retired), the state cell its object's payer, the opened slot the record's; the
settled slot is retired. -/
theorem Delivery.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    (objectOnly : ∀ post ∈ delivery.posts, post.cell = objectCell config.domain delivery.record.object →
      ∃ held, post.bytes = objectImage delivery.record.object held) :
    CellsPaid config (afterPosts snapshot delivery.posts) (delivery.posts.map Post.cell) := by
  have commits := segmentCommit_census (resumedSegment_commit delivery.endExact)
  have retired := settle_posts_retired delivery.settled
  rw [delivery.postsExact] at objectOnly ⊢
  apply recordFirst_cells_paid config snapshot request.record delivery.record.object delivery.next delivery.object
    delivery.objectExact
  · intro post member
    rcases List.mem_append.mp member with inFront | inCount
    · rcases List.mem_append.mp inFront with inFront | isBook
      · rcases List.mem_append.mp inFront with inSettle | inYield
        · exact .inr (.inr (.inl (retired post inSettle)))
        · exact commits post inYield
      · simp only [List.mem_singleton] at isBook
        subst isBook
        exact .inr (.inr (.inr (.inl (Postings.write_payload config snapshot delivery.posted))))
    · rw [mem_countPosts inCount]
      exact .inr (.inr (.inr (.inr ⟨_, rfl⟩)))
  · rintro ⟨post, inRest, slot, _, isSlot⟩
    have live := slotPosted_live isSlot
    rcases List.mem_append.mp inRest with inFront | inCount
    · rcases List.mem_append.mp inFront with inFront | isBook
      · rcases List.mem_append.mp inFront with inSettle | inYield
        · rw [retired post inSettle, payloadOf_retired] at live; cases live
        · rw [delivery.nextExact]
          exact segmentCommit_awaiting (resumedSegment_commit delivery.endExact) _ _ ⟨post, inYield, live⟩
      · simp only [List.mem_singleton] at isBook
        subst isBook
        rw [Postings.write_payload] at live
        cases live
    · rw [mem_countPosts inCount] at isSlot
      exact absurd isSlot (objectImage_ne_slot _ _ slot)
  · exact objectOnly

/-- **`retention_cells_have_payer`, exhaustion**: it rewrites the awaiting
record (its escrow pays) and the Book. -/
theorem Exhaustion.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : ExhaustRequest}
    (ex : Exhaustion config snapshot height request) :
    CellsPaid config (afterPosts snapshot ex.posts) (ex.posts.map Post.cell) := by
  apply cellsPaid_of_posts
  rw [ex.postsExact]
  intro post member live
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with isRecord | isBook
  · subst isRecord
    have awaiting : ex.next.phase = .awaiting ex.await := by rw [ex.nextExact]; exact ex.awaiting
    show (payerOfBytes config _ (recordImage ex.next)).isSome = true
    rw [payer_record_image config _ ex.next ex.await awaiting]; rfl
  · subst isBook
    rw [Postings.write_payload] at live; cases live

/-- **`retention_cells_have_payer`, publication**: the package cell names its
`Stored.payer`, a registered Book account (`Publication.payerRegistered`). -/
theorem Publication.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {stored : Stored} (publication : Publication config snapshot stored) :
    CellsPaid config (afterPosts snapshot publication.posts) (publication.posts.map Post.cell) ∧
      ∀ post ∈ publication.posts,
        payerOfBytes config (afterPosts snapshot publication.posts) post.bytes = some stored.payer := by
  have each : ∀ post ∈ publication.posts,
      payerOfBytes config (afterPosts snapshot publication.posts) post.bytes = some stored.payer := by
    intro post member
    rw [publication.postsExact] at member
    simp only [List.mem_singleton] at member
    subst member
    simp [postAt, payerOfBytes, payloadOf_image, payerRoute, routePayer, stored_roundTrip]
  refine ⟨cellsPaid_of_posts config snapshot _ (fun post member _ => ?_), each⟩
  rw [each post member]; rfl

/-- **The record a creation installs is what the post-state holds**: read back from the bytes
the creation commits, the object's record is `request.record`. -/
theorem Creation.object_installed {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} (created : Creation config snapshot height request) :
    objectAt config (afterPosts snapshot created.posts) request.object = some request.record := by
  have headBytes : afterPosts snapshot
      (postAt snapshot (objectCell config.domain request.object) (objectImage request.object request.record) ::
        (request.seed.map (seedPost config snapshot request)).toList)
      (objectCell config.domain request.object) = objectImage request.object request.record :=
    afterPosts_first snapshot
      (postAt snapshot (objectCell config.domain request.object) (objectImage request.object request.record))
      (request.seed.map (seedPost config snapshot request)).toList
  unfold objectAt
  rw [created.postsExact, headBytes]
  simp [objectImage, bodyOf_image, ObjectRecord.record_roundTrip]

/-- **`create_installs_pin`.** An admitted creation installs one record, read back from the
post-state it commits; the law that will judge every write of that object is the pin clause of
exactly the package the request pins (published: `created.published`), then the creator's law. -/
theorem create_installs_pin {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} {created : Creation config snapshot height request}
    (_admitted : create config snapshot height request = .ok created) :
    objectAt config (afterPosts snapshot created.posts) request.object = some request.record ∧
      request.record.pin = request.pin ∧
      request.record.effectiveLaw =
        Minidregg.Pred.Pred.all [ObjectRecord.pinClause request.pin, request.law] ∧
      (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true :=
  ⟨created.object_installed, rfl, rfl, created.published⟩

/-- **`create_seed_judged`.** An admitted creation with a seed installs it only if the creator's
law accepts it over no old state (turn 4, no package): the object is not born violating its own
state clauses. The pin clause is not asked (`seed_teeth`: the same value is refused as a write). -/
theorem create_seed_judged {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : CreateRequest} {created : Creation config snapshot height request}
    (_admitted : create config snapshot height request = .ok created) {seed : Data}
    (seeded : request.seed = some seed) :
    ∃ before after,
      ObjectRecord.views (seedFacts request height) none seed = some (before, after) ∧
        Minidregg.Pred.eval request.law before after = true ∧
        readState config snapshot request.object = .ok none ∧
        seedPost config snapshot request seed ∈ created.posts := by
  obtain ⟨⟨before, after, viewed, accepted⟩, _⟩ :=
    (ObjectRecord.admitSeed_ok_iff _ _ _).mp (created.seedJudged seed seeded)
  refine ⟨before, after, viewed, accepted, created.stateFresh seed seeded, ?_⟩
  rw [created.postsExact, seeded]
  simp

/-- **`create_seed_refused_names_clause`.** A seed the creator's law refuses is refused, and the
refusal names the failing clause of the creator's law on the seed's own views. -/
theorem create_seed_refused_names_clause {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : CreateRequest} {seed : Data}
    {reason : ObjectRecord.WriteRefusal}
    (absent : readObject config snapshot request.object = .ok none)
    (published : (bodyOf .package (snapshot.canonicalBytes (packageCell config.domain request.pin))).isSome = true)
    (data : request.stateType.isData = true)
    (seeded : request.seed = some seed)
    (fresh : readState config snapshot request.object = .ok none)
    (refused : ObjectRecord.admitSeed request.record (seedFacts request height) seed = .error reason) :
    create config snapshot height request = .error (.objectWrite reason) := by
  unfold create
  split
  · rename_i reason' found; rw [absent] at found; cases found
  · rename_i found; rw [absent] at found; cases found
  · rename_i found
    rw [dif_pos published, dif_pos data]
    split
    next plan => rw [seeded] at plan; cases plan
    next seed2 plan =>
      rw [seeded] at plan; cases plan
      split
      next reason2 sr => rw [fresh] at sr; cases sr
      next found2 sr => rw [fresh] at sr; cases sr
      next sr =>
        split
        next reason3 judged => rw [refused] at judged; cases judged; rfl
        next judged => rw [refused] at judged; cases judged

/-- **`pin_not_removable`.** Whatever turn commits `posts` on a snapshot where the object's
record reads as `record`, if no post lands on the object's record coordinate the record reads
the same afterwards, so the law that judges the object's writes still leads with the pin clause
of the record's pins (`ObjectRecord.pins`). Posts that land on an object record coordinate are
`create`'s, the counters' (`countPosts`, `objectPost`: they keep the pins, `ObjectRecord.bump_pins`)
and the upgrade turns' (ADOPT adds the next pin, MIGRATE re-pins); the `unwritten` premise is the
coordinate-separation premise every theorem about other posts carries. -/
theorem pin_not_removable {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (posts : List Post) {object : CellId} {record : ObjectRecord}
    (read : readObject config snapshot object = .ok (some record))
    (unwritten : ∀ post ∈ posts, post.cell ≠ objectCell config.domain object) :
    objectAt config (afterPosts snapshot posts) object = some record ∧
      record.effectiveLaw = Minidregg.Pred.Pred.all [Minidregg.Pred.objectivePin record.pins, record.law] := by
  refine ⟨?_, rfl⟩
  unfold objectAt
  rw [afterPosts_unwritten snapshot _ _ unwritten]
  exact objectAt_of_read read

/-- **`retention_cells_have_payer`, creation**: the object's record, and its seeded state cell,
name the object's payer. -/
theorem Creation.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : CreateRequest}
    (created : Creation config snapshot height request) :
    ∀ post ∈ created.posts,
      payerOfBytes config (afterPosts snapshot created.posts) post.bytes = some request.record.payer := by
  intro post member
  rw [created.postsExact] at member
  rcases List.mem_cons.mp member with head | tail
  · subst head
    simp [postAt, objectImage, payerOfBytes, payloadOf_image, payerRoute, routePayer, ObjectRecord.record_roundTrip]
  · cases seeded : request.seed with
    | none => simp [seeded] at tail
    | some seed =>
      simp only [seeded, Option.map_some, Option.toList_some, List.mem_singleton] at tail
      subst tail
      exact payer_state_image config _ request.object _ request.record created.object_installed

theorem decide_activity {slot decided : AnswerSlot.Slot} {subject : SubjectId} {height : Nat}
    {decision : AnswerSlot.Decision} (ok : AnswerSlot.decide slot subject height decision = .ok decided) :
    decided.activity = slot.activity := by
  unfold AnswerSlot.decide at ok
  split at ok
  · cases ok
  · split_ifs at ok
    all_goals cases ok
    rfl

/-- **`retention_cells_have_payer`, a resolution**: the decided slot names the
escrow of the record it answers (premise: that record is the one the turn reads
under its guard of `slot.activity`, at a coordinate other than the slot's). -/
theorem Resolution.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : ResolveRequest}
    (resolution : Resolution config snapshot height request) {record : Record}
    (answers : readRecord snapshot resolution.slot.activity = some record)
    (distinct : AnswerSlot.cell config.domain resolution.decided.name ≠ resolution.slot.activity) :
    ∀ post ∈ resolution.posts,
      payerOfBytes config (afterPosts snapshot resolution.posts) post.bytes = some record.escrow.account := by
  have activity := decide_activity resolution.decidedExact
  have unwritten : ∀ post ∈ resolution.posts, post.cell ≠ resolution.slot.activity := by
    intro post member
    rw [resolution.postsExact] at member
    simp only [List.mem_singleton] at member
    subst member
    exact distinct
  have held : recordAt (afterPosts snapshot resolution.posts) resolution.decided.activity = some record := by
    rw [activity]
    unfold recordAt
    rw [afterPosts_unwritten snapshot _ _ unwritten]
    exact answers
  intro post member
  have shape := member
  rw [resolution.postsExact] at shape
  simp only [List.mem_singleton] at shape
  rw [shape]
  exact payer_slot_image config _ resolution.decided record held

#assert_axioms retention_census_paid
#assert_axioms planted_census_unpaid
#assert_axioms install_afterPosts
#assert_axioms cellsPaid_of_posts
#assert_axioms payloadOf_image
#assert_axioms payloadOf_book
#assert_axioms recordFirst_cells_paid
#assert_axioms payer_object_image
#assert_axioms objectImage_ne_slot
#assert_axioms objectAt_afterPosts
#assert_axioms mem_countPosts
#assert_axioms mem_objectPost
#assert_axioms Birth.retention_cells_have_payer
#assert_axioms Delivery.retention_cells_have_payer
#assert_axioms Exhaustion.retention_cells_have_payer
#assert_axioms Publication.retention_cells_have_payer
#assert_axioms Creation.retention_cells_have_payer
#assert_axioms Creation.object_installed
#assert_axioms create_installs_pin
#assert_axioms create_seed_judged
#assert_axioms create_seed_refused_names_clause
#assert_axioms pin_not_removable
#assert_axioms Resolution.retention_cells_have_payer

end Minidregg.Kernel.ObjectiveActivity
