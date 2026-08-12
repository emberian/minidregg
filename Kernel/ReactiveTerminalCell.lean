/-
# Kernel.ReactiveTerminalCell -- one durable terminal state for reactive promises

Logical reactive finalization is not yet durable settlement.  This module
supplies the missing narrow kernel carrier.  Every promise has one terminal
cell and one outbox cell.  Finalize, cancel, expire, and break all contend for
the same terminal pre-root, transaction id, and nullifier.  The winning
decision installs the terminal record and its exact outbox message in one
`DurableDataIntent`; a different decision under the same transaction id is a
payload conflict, while an exact retry is a replay.

The settlement height is not a caller-authored Boolean.  Its canonical clock
image is an exact read guard checked in the same snapshot as the two writes.
The semantic trigger root is a second exact read guard.  Finalize, cancel, and
break are admitted only at or before the deadline; expiry is admitted only
strictly after it.

This remains a logical atomic-settlement model.  The final section states the
physical refinement and liveness obligations explicitly; it does not claim
that a filesystem, database, scheduler, or transport discharges them.
-/
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.ReactiveTerminalCell

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v

/-! ## Canonical terminal decision -/

inductive TerminalKind where
  | finalized
  | cancelled
  | expired
  | broken
  deriving DecidableEq, Repr

def TerminalKind.tag : TerminalKind → UInt8
  | .finalized => 1
  | .cancelled => 2
  | .expired => 3
  | .broken => 4

theorem TerminalKind.tag_injective : Function.Injective TerminalKind.tag := by
  intro left right equal
  cases left <;> cases right <;> simp_all [TerminalKind.tag]

/-- The deadline relation is part of the decision constructor.  There is no
unchecked `expired : Bool` or executor-supplied status tag. -/
inductive Decision (deadline settledAt : Nat) where
  | finalize (within : settledAt ≤ deadline)
  | cancel (within : settledAt ≤ deadline)
  | expire (after : deadline < settledAt)
  | broken (within : settledAt ≤ deadline)

namespace Decision

def kind {deadline settledAt : Nat} : Decision deadline settledAt → TerminalKind
  | .finalize _ => .finalized
  | .cancel _ => .cancelled
  | .expire _ => .expired
  | .broken _ => .broken

theorem timely_not_expired {deadline settledAt : Nat}
    (decision : Decision deadline settledAt)
    (timely : decision.kind ≠ .expired) : settledAt ≤ deadline := by
  cases decision with
  | finalize within => exact within
  | cancel within => exact within
  | expire after => simp [kind] at timely
  | broken within => exact within

theorem expired_after {deadline settledAt : Nat}
    (decision : Decision deadline settledAt)
    (expired : decision.kind = .expired) : deadline < settledAt := by
  cases decision with
  | finalize within => simp [kind] at expired
  | cancel within => simp [kind] at expired
  | expire after => exact after
  | broken within => simp [kind] at expired

end Decision

/-! ## Stable open cell and canonical wire payloads -/

/-- All identities and pre-images are fixed when the promise opens.  In
particular, every terminal alternative uses the same transaction and
nullifier identities. -/
structure OpenCell where
  codecVersion : Nat
  domain : Digest
  promiseId : Digest
  deadline : Nat
  transactionId : TransactionId
  nullifierId : Digest
  eventId : Digest
  terminalCell : CellId
  outboxCell : CellId
  clockCell : CellId
  triggerCell : CellId
  openTerminalBytes : List UInt8
  openOutboxBytes : List UInt8
  exactCharge : Charge
  terminalOutboxDistinct : terminalCell ≠ outboxCell
  terminalClockDistinct : terminalCell ≠ clockCell
  outboxClockDistinct : outboxCell ≠ clockCell
  terminalTriggerDistinct : terminalCell ≠ triggerCell
  outboxTriggerDistinct : outboxCell ≠ triggerCell

/-- Unary-length framing is deliberately simple Lean semantics: deterministic,
prefix-delimited, and independent of host serialization.  A deployment may
refine it to a bounded production codec only by preserving the exact bytes
used by roots, replay identity, and events. -/
def encodeNat (value : Nat) : List UInt8 :=
  List.replicate value 0 ++ [255]

def encodeDigest (digest : Digest) : List UInt8 :=
  encodeNat digest.value

def frame (tag : UInt8) (fields : List (List UInt8)) : List UInt8 :=
  tag :: fields.flatMap fun field => encodeNat field.length ++ field

structure OutboxRecord where
  codecVersion : Nat
  domain : Digest
  promiseId : Digest
  settledAt : Nat
  kind : TerminalKind
  evidenceRoot : Digest
  deriving DecidableEq, Repr

def OutboxRecord.canonicalBytes (record : OutboxRecord) : List UInt8 :=
  frame 161 [encodeNat record.codecVersion, encodeDigest record.domain,
    encodeDigest record.promiseId, encodeNat record.settledAt,
    [record.kind.tag], encodeDigest record.evidenceRoot]

structure TerminalRecord where
  codecVersion : Nat
  domain : Digest
  promiseId : Digest
  deadline : Nat
  settledAt : Nat
  kind : TerminalKind
  evidenceRoot : Digest
  outboxRoot : Digest
  deriving DecidableEq, Repr

/-- The decision tag is the first framed field.  This makes distinct terminal
alternatives byte-distinct even when `rootBytes` is collision-prone. -/
def TerminalRecord.canonicalBytes (record : TerminalRecord) : List UInt8 :=
  record.kind.tag :: frame 162 [encodeNat record.codecVersion,
    encodeDigest record.domain, encodeDigest record.promiseId,
    encodeNat record.deadline, encodeNat record.settledAt,
    encodeDigest record.evidenceRoot, encodeDigest record.outboxRoot]

structure SettlementEvent where
  codecVersion : Nat
  domain : Digest
  promiseId : Digest
  transactionId : TransactionId
  kind : TerminalKind
  terminalRoot : Digest
  outboxRoot : Digest
  clockRoot : Digest
  triggerRoot : Digest
  deriving DecidableEq, Repr

def SettlementEvent.canonicalBytes (event : SettlementEvent) : List UInt8 :=
  frame 163 [[event.kind.tag], encodeNat event.codecVersion,
    encodeDigest event.domain, encodeDigest event.promiseId,
    encodeDigest event.transactionId, encodeDigest event.terminalRoot,
    encodeDigest event.outboxRoot, encodeDigest event.clockRoot,
    encodeDigest event.triggerRoot]

/-! ## One exact terminal settlement plan -/

structure Plan (rootBytes : List UInt8 → Digest) (openCell : OpenCell) where
  settledAt : Nat
  decision : Decision openCell.deadline settledAt
  evidenceRoot : Digest
  triggerRoot : Digest

namespace Plan

variable {rootBytes : List UInt8 → Digest} {openCell : OpenCell}

def kind (plan : Plan rootBytes openCell) : TerminalKind :=
  plan.decision.kind

def clockBytes (plan : Plan rootBytes openCell) : List UInt8 :=
  frame 160 [encodeNat openCell.codecVersion, encodeDigest openCell.domain,
    encodeNat plan.settledAt]

def clockRoot (plan : Plan rootBytes openCell) : Digest :=
  rootBytes plan.clockBytes

def outboxRecord (plan : Plan rootBytes openCell) : OutboxRecord where
  codecVersion := openCell.codecVersion
  domain := openCell.domain
  promiseId := openCell.promiseId
  settledAt := plan.settledAt
  kind := plan.kind
  evidenceRoot := plan.evidenceRoot

def outboxBytes (plan : Plan rootBytes openCell) : List UInt8 :=
  plan.outboxRecord.canonicalBytes

def outboxRoot (plan : Plan rootBytes openCell) : Digest :=
  rootBytes plan.outboxBytes

def terminalRecord (plan : Plan rootBytes openCell) : TerminalRecord where
  codecVersion := openCell.codecVersion
  domain := openCell.domain
  promiseId := openCell.promiseId
  deadline := openCell.deadline
  settledAt := plan.settledAt
  kind := plan.kind
  evidenceRoot := plan.evidenceRoot
  outboxRoot := plan.outboxRoot

def terminalBytes (plan : Plan rootBytes openCell) : List UInt8 :=
  plan.terminalRecord.canonicalBytes

def terminalRoot (plan : Plan rootBytes openCell) : Digest :=
  rootBytes plan.terminalBytes

def settlementEvent (plan : Plan rootBytes openCell) : SettlementEvent where
  codecVersion := openCell.codecVersion
  domain := openCell.domain
  promiseId := openCell.promiseId
  transactionId := openCell.transactionId
  kind := plan.kind
  terminalRoot := plan.terminalRoot
  outboxRoot := plan.outboxRoot
  clockRoot := plan.clockRoot
  triggerRoot := plan.triggerRoot

def terminalWrite (plan : Plan rootBytes openCell) : DataWrite where
  cellId := openCell.terminalCell
  expectedPre := rootBytes openCell.openTerminalBytes
  exactPost := plan.terminalRoot
  canonicalPostBytes := plan.terminalBytes

def outboxWrite (plan : Plan rootBytes openCell) : DataWrite where
  cellId := openCell.outboxCell
  expectedPre := rootBytes openCell.openOutboxBytes
  exactPost := plan.outboxRoot
  canonicalPostBytes := plan.outboxBytes

def clockGuard (plan : Plan rootBytes openCell) : ReadGuard where
  cellId := openCell.clockCell
  expectedRoot := plan.clockRoot

def triggerGuard (plan : Plan rootBytes openCell) : ReadGuard where
  cellId := openCell.triggerCell
  expectedRoot := plan.triggerRoot

def nullifier (_plan : Plan rootBytes openCell) : StableNullifier where
  codecVersion := openCell.codecVersion
  domain := openCell.domain
  nullifierId := openCell.nullifierId
  canonicalBytes := frame 164 [encodeDigest openCell.promiseId,
    encodeDigest openCell.transactionId]

def event (plan : Plan rootBytes openCell) : StableEvent where
  codecVersion := openCell.codecVersion
  domain := openCell.domain
  eventId := openCell.eventId
  canonicalBytes := plan.settlementEvent.canonicalBytes

/-- The exact two-write, two-guard durable intent.  Terminal state and outbox
cannot split; clock and trigger roots are checked against the same snapshot. -/
def intent (plan : Plan rootBytes openCell) : DataIntent rootBytes where
  transactionId := openCell.transactionId
  writes := [plan.terminalWrite, plan.outboxWrite]
  readGuards := [plan.clockGuard, plan.triggerGuard]
  nullifiers := [plan.nullifier]
  exactCharge := openCell.exactCharge
  event := plan.event
  postRootsBound := by
    intro write member
    simp at member
    rcases member with rfl | rfl <;> rfl
  guardsReadOnly := by
    intro guard member
    simp at member
    rcases member with rfl | rfl
    · simpa [clockGuard, terminalWrite, outboxWrite] using
        And.intro openCell.terminalClockDistinct.symm
          openCell.outboxClockDistinct.symm
    · simpa [triggerGuard, terminalWrite, outboxWrite] using
        And.intro openCell.terminalTriggerDistinct.symm
          openCell.outboxTriggerDistinct.symm

@[simp] theorem intent_writes (plan : Plan rootBytes openCell) :
    plan.intent.writes = [plan.terminalWrite, plan.outboxWrite] := rfl

@[simp] theorem intent_readGuards (plan : Plan rootBytes openCell) :
    plan.intent.readGuards = [plan.clockGuard, plan.triggerGuard] := rfl

@[simp] theorem intent_event_bytes (plan : Plan rootBytes openCell) :
    plan.intent.event.canonicalBytes = plan.settlementEvent.canonicalBytes := rfl

@[simp] theorem intent_transaction (plan : Plan rootBytes openCell) :
    plan.intent.transactionId = openCell.transactionId := rfl

@[simp] theorem terminal_post_bytes (plan : Plan rootBytes openCell) :
    plan.terminalWrite.canonicalPostBytes = plan.terminalBytes := rfl

@[simp] theorem outbox_post_bytes (plan : Plan rootBytes openCell) :
    plan.outboxWrite.canonicalPostBytes = plan.outboxBytes := rfl

theorem terminal_and_outbox_atomic
    (plan : Plan rootBytes openCell) (schedule : Schedule)
    (before : DataSnapshot rootBytes) :
    (DurableDataIntent.execute schedule before plan.intent).storeAfter before = before ∨
      (DurableDataIntent.execute schedule before plan.intent).storeAfter before =
        DataSnapshot.install before plan.intent :=
  DurableDataIntent.execute_no_partial_data_commit schedule before plan.intent

theorem complete_ready (plan : Plan rootBytes openCell)
    (before : DataSnapshot rootBytes)
    (unrecorded : Snapshot.lookupRecorded openCell.transactionId
      before.model.journal = none)
    (ready : plan.intent.preflight before = .ok ()) :
    DurableDataIntent.execute .complete before plan.intent =
      .accepted (DataSnapshot.install before plan.intent) :=
  DurableDataIntent.execute_complete_ready before plan.intent unrecorded ready

@[simp] theorem retry_after_install (plan : Plan rootBytes openCell)
    (schedule : Schedule) (before : DataSnapshot rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before plan.intent) plan.intent =
      .replayed plan.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install,
    Snapshot.install, Snapshot.lookupRecorded,
    Intent.sameCheck_self]

/-- The installed canonical bytes are exactly the terminal and outbox payloads
selected by this plan. -/
theorem installed_exact (plan : Plan rootBytes openCell)
    (before : DataSnapshot rootBytes) :
    (DataSnapshot.install before plan.intent).canonicalBytes
        openCell.terminalCell = plan.terminalBytes ∧
      (DataSnapshot.install before plan.intent).canonicalBytes
        openCell.outboxCell = plan.outboxBytes := by
  constructor <;>
    simp [DataSnapshot.install_canonicalBytes, DataSnapshot.lookupPostBytes,
      intent, terminalWrite, outboxWrite, openCell.terminalOutboxDistinct]

end Plan

/-! ## Race exclusion and replay identity -/

private theorem terminalBytes_kind_ne
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    {left right : Plan rootBytes openCell}
    (different : left.kind ≠ right.kind) :
    left.terminalBytes ≠ right.terminalBytes := by
  intro equal
  have heads := congrArg List.head? equal
  simp [Plan.terminalBytes, Plan.terminalRecord,
    TerminalRecord.canonicalBytes, frame] at heads
  exact different (TerminalKind.tag_injective heads)

theorem competing_decision_conflicts
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (first second : Plan rootBytes openCell)
    (different : first.kind ≠ second.kind)
    (schedule : Schedule) (before : DataSnapshot rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before first.intent) second.intent =
      .rejected (.durable .transactionConflict) := by
  have writesNe : first.intent.writes ≠ second.intent.writes := by
    intro equal
    have firstWrite := congrArg List.head? equal
    simp [Plan.intent, Plan.terminalWrite] at firstWrite
    exact terminalBytes_kind_ne different firstWrite.2
  have checkFalse : first.intent.erase.sameCheck second.intent.erase = false := by
    apply Bool.eq_false_iff.mpr
    intro checkTrue
    have payload := (DataIntent.erase_sameCheck_eq_true_iff
      first.intent second.intent).mp checkTrue
    exact writesNe payload.1
  simp [DurableDataIntent.execute, DataSnapshot.install,
    Snapshot.install, Snapshot.lookupRecorded,
    checkFalse]

/-- No pair of distinct terminal kinds can both be accepted sequentially from
one open promise snapshot.  The second contender is a transaction conflict,
not a second terminal record. -/
theorem distinct_terminals_mutually_exclusive
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (first second : Plan rootBytes openCell)
    (different : first.kind ≠ second.kind)
    (before : DataSnapshot rootBytes) :
    DurableDataIntent.execute .complete
        (DataSnapshot.install before first.intent) second.intent ≠
      .accepted (DataSnapshot.install
        (DataSnapshot.install before first.intent) second.intent) := by
  rw [competing_decision_conflicts first second different]
  simp

/-! ## Physical and liveness ceilings -/

/-- Physical safety is inherited only through an actual data-intent simulation.
The refinement must cover the same terminal/outbox bytes and both read guards. -/
theorem physical_step_terminal_atomic
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell)
    {PhysicalState : Type u}
    {PhysicalStep : PhysicalState → DataIntent rootBytes → PhysicalState → Type v}
    {Represents : PhysicalState → DataSnapshot rootBytes → Prop}
    (refinement : DurableDataIntent.ImplementationRefinement
      rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore plan.intent physicalAfter) :
    ∃ modelAfter,
      Represents physicalAfter modelAfter ∧
      (modelAfter = modelBefore ∨
        modelAfter = DataSnapshot.install modelBefore plan.intent) ∧
      (∀ cellId, rootBytes (modelAfter.canonicalBytes cellId) =
        modelAfter.model.roots cellId) :=
  DurableDataIntent.physical_step_no_partial_data_commit
    refinement represented stepped

/-- Safety does not imply that a runnable contender is ever scheduled or that
its physical step terminates.  A deployment claiming eventual terminality must
provide this additional progress relation; this module constructs none. -/
structure LivenessRefinement
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (Enabled : Plan rootBytes openCell → Prop)
    (EventuallyInstalled : Plan rootBytes openCell → Prop) : Prop where
  progresses : ∀ plan, Enabled plan → EventuallyInstalled plan

/-! ## Concrete non-vacuity and race witness -/

namespace Witness

def lengthRoot (bytes : List UInt8) : Digest := ⟨bytes.length⟩

def zeroCharge : Charge := fun _ => 0

def openCell : OpenCell where
  codecVersion := 1
  domain := ⟨10⟩
  promiseId := ⟨11⟩
  deadline := 7
  transactionId := ⟨12⟩
  nullifierId := ⟨13⟩
  eventId := ⟨14⟩
  terminalCell := ⟨20⟩
  outboxCell := ⟨21⟩
  clockCell := ⟨22⟩
  triggerCell := ⟨23⟩
  openTerminalBytes := [0]
  openOutboxBytes := [0, 0]
  exactCharge := zeroCharge
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalTriggerDistinct := by decide
  outboxTriggerDistinct := by decide

def finalizePlan : Plan lengthRoot openCell where
  settledAt := 7
  decision := .finalize (by decide)
  evidenceRoot := ⟨31⟩
  triggerRoot := ⟨32⟩

def cancelPlan : Plan lengthRoot openCell where
  settledAt := 7
  decision := .cancel (by decide)
  evidenceRoot := ⟨33⟩
  triggerRoot := ⟨32⟩

def expirePlan : Plan lengthRoot openCell where
  settledAt := 8
  decision := .expire (by decide)
  evidenceRoot := ⟨34⟩
  triggerRoot := ⟨35⟩

def breakPlan : Plan lengthRoot openCell where
  settledAt := 6
  decision := .broken (by decide)
  evidenceRoot := ⟨36⟩
  triggerRoot := ⟨37⟩

def beforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = openCell.terminalCell then openCell.openTerminalBytes
  else if cellId = openCell.outboxCell then openCell.openOutboxBytes
  else if cellId = openCell.clockCell then finalizePlan.clockBytes
  else if cellId = openCell.triggerCell then
    List.replicate finalizePlan.triggerRoot.value 0
  else []

def beforeModel : Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => lengthRoot (beforeBytes cellId)
  consumed := fun _ => false
  available := fun _ => 100
  history := []
  journal := []

def before : DataSnapshot lengthRoot where
  model := beforeModel
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

@[simp] theorem finalize_ready : finalizePlan.intent.preflight before = .ok () := by
  decide

@[simp] theorem finalize_commits :
    DurableDataIntent.execute .complete before finalizePlan.intent =
      .accepted (DataSnapshot.install before finalizePlan.intent) := by
  exact Plan.complete_ready finalizePlan before (by decide) finalize_ready

@[simp] theorem exact_retry_replays :
    DurableDataIntent.execute .complete
        (DataSnapshot.install before finalizePlan.intent) finalizePlan.intent =
      .replayed finalizePlan.intent.erase :=
  Plan.retry_after_install finalizePlan .complete before

@[simp] theorem cancel_loses_finalize_race :
    DurableDataIntent.execute .complete
        (DataSnapshot.install before finalizePlan.intent) cancelPlan.intent =
      .rejected (.durable .transactionConflict) := by
  apply competing_decision_conflicts finalizePlan cancelPlan
  decide

@[simp] theorem expire_loses_finalize_race :
    DurableDataIntent.execute .complete
        (DataSnapshot.install before finalizePlan.intent) expirePlan.intent =
      .rejected (.durable .transactionConflict) := by
  apply competing_decision_conflicts finalizePlan expirePlan
  decide

@[simp] theorem break_loses_finalize_race :
    DurableDataIntent.execute .complete
        (DataSnapshot.install before finalizePlan.intent) breakPlan.intent =
      .rejected (.durable .transactionConflict) := by
  apply competing_decision_conflicts finalizePlan breakPlan
  decide

end Witness

/-! Kernel-facing theorem audit. -/

/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.Plan.terminal_and_outbox_atomic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Plan.terminal_and_outbox_atomic
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.Plan.retry_after_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Plan.retry_after_install
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.competing_decision_conflicts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms competing_decision_conflicts
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.distinct_terminals_mutually_exclusive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinct_terminals_mutually_exclusive
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.physical_step_terminal_atomic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms physical_step_terminal_atomic
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.Witness.finalize_commits' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.finalize_commits
/-- info: 'Minidregg.Kernel.ReactiveTerminalCell.Witness.cancel_loses_finalize_race' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cancel_loses_finalize_race

end Minidregg.Kernel.ReactiveTerminalCell
