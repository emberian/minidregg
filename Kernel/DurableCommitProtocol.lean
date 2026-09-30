/-
# Kernel.DurableCommitProtocol -- fail-closed durable settlement model

`CanonicalTransition.PreparedTurn` and `MultiCellHyperedge` determine
logical meaning.  This module does not interpret
state, effects, authority, or receipts again.  It models the smaller handler
protocol which must install an already accepted meaning durably:

* compare every participating cell against its exact canonical pre-root;
* install all exact canonical post-roots as one atomic model transition;
* consume every eager nullifier in that same transition;
* debit the exact Lean-derived resource charge;
* append the exact receipt/history event and idempotency record.

Crash and retry behavior is explicit.  A crash can occur before the atomic
install or after the complete install; there is deliberately no model state for
"some roots changed, but the receipt/nullifier/debit did not".  This is a
verified protocol model, not a proof about a particular database, filesystem,
or network.  The final section exposes the required implementation-refinement
premise as a proof-relevant simulation relation.  No `Bool = true` receipt is
treated as evidence of physical atomicity.
-/
import Kernel.MultiCellHyperedge
import Theory.ResourceCost

namespace Minidregg.Kernel.DurableCommitProtocol

open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.ResourceCost

set_option autoImplicit false

universe u v w x y z b h p q

/-! ## Exact handler intent -- no second semantic interpreter -/

/-- One canonical compare-and-swap lane.  Both roots are data projected from
an already accepted semantic transition by the adapters below. -/
structure RootWrite (CellId : Type u) where
  cellId : CellId
  expectedPre : TypedAuthorization.Digest
  exactPost : TypedAuthorization.Digest
  deriving DecidableEq, Repr

/-- The complete data installed by one durable transaction.  `exactCharge` is
unbounded Lean `Nat` arithmetic lane-by-lane; machine-width encoding remains a
separate checked boundary in `Theory.ResourceCost`.

`Event` is intentionally parametric.  For one cell the adapter below uses the
existing private-constructor `AcceptedCellEffect.ReceiptEvent`; for a joint
turn it can use the exact joint receipt binding or a richer existing history
event.  The durable layer only appends the value it was given. -/
structure Intent
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  transactionId : TxId
  rootWrites : List (RootWrite CellId)
  nullifiers : List Nullifier
  exactCharge : Charge
  event : Event

namespace Intent

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}

/-- Replay equality is finite and executable even though a charge is a
function: `Lane.allCheck` compares every closed resource lane. -/
def sameCheck [DecidableEq (RootWrite CellId)] [DecidableEq Nullifier]
    [DecidableEq Event]
    (left right : Intent TxId CellId Nullifier Event) : Bool :=
  decide (left.rootWrites = right.rootWrites) &&
    decide (left.nullifiers = right.nullifiers) &&
    Lane.allCheck (fun lane => decide (left.exactCharge lane = right.exactCharge lane)) &&
    decide (left.event = right.event)

/-- Exact payload equality for idempotent retry.  Transaction identifiers are
looked up separately; changing any root, nullifier, charge lane, or event under
the same identifier is a conflict. -/
def SamePayload (left right : Intent TxId CellId Nullifier Event) : Prop :=
  left.rootWrites = right.rootWrites /\
    left.nullifiers = right.nullifiers /\
    left.exactCharge = right.exactCharge /\
    left.event = right.event

@[simp] theorem sameCheck_eq_true_iff
    [DecidableEq (RootWrite CellId)] [DecidableEq Nullifier] [DecidableEq Event]
    (left right : Intent TxId CellId Nullifier Event) :
    left.sameCheck right = true <-> left.SamePayload right := by
  simp only [sameCheck, Bool.and_eq_true, decide_eq_true_eq,
    Lane.allCheck_eq_true_iff, SamePayload]
  constructor
  · rintro ⟨⟨⟨roots, nullifiers⟩, charge⟩, event⟩
    refine ⟨roots, nullifiers, ?_, event⟩
    funext lane
    exact charge lane
  · rintro ⟨roots, nullifiers, charge, event⟩
    refine ⟨⟨⟨roots, nullifiers⟩, ?_⟩, event⟩
    intro lane
    exact congrFun charge lane

@[simp] theorem sameCheck_self
    [DecidableEq (RootWrite CellId)] [DecidableEq Nullifier] [DecidableEq Event]
    (intent : Intent TxId CellId Nullifier Event) :
    intent.sameCheck intent = true := by
  rw [sameCheck_eq_true_iff]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Intent

/-! ## One atomic model snapshot -/

/-- The durable model state is one record because roots, nullifiers, budget,
history, and retry journal form one semantic commit.  A real implementation may
store these in many tables or services only after discharging the refinement
premise at the end of this module. -/
structure Snapshot
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  roots : CellId -> TypedAuthorization.Digest
  consumed : Nullifier -> Bool
  available : Charge
  history : List Event
  journal : List (TxId × Intent TxId CellId Nullifier Event)

namespace Snapshot

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}

/-- Recursive lookup keeps retry behavior transparently executable. -/
def lookupRecorded [DecidableEq TxId]
    (transactionId : TxId) :
    List (TxId × Intent TxId CellId Nullifier Event) ->
      Option (Intent TxId CellId Nullifier Event)
  | [] => none
  | (recordedId, recorded) :: rest =>
      if recordedId = transactionId then some recorded
      else lookupRecorded transactionId rest

/-- Find the exact post-root assigned to a cell, if this transaction writes
that cell.  Duplicate cell ids are rejected by preflight before installation. -/
def lookupPost [DecidableEq CellId]
    (cellId : CellId) : List (RootWrite CellId) ->
      Option TypedAuthorization.Digest
  | [] => none
  | write :: rest =>
      if write.cellId = cellId then some write.exactPost
      else lookupPost cellId rest

/-- The only state-changing operation in the model.  Every component of the
semantic commit is installed by this one constructor-valued function. -/
def install [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    Snapshot TxId CellId Nullifier Event where
  roots := fun cellId =>
    (lookupPost cellId intent.rootWrites).getD (before.roots cellId)
  consumed := fun nullifier =>
    if nullifier ∈ intent.nullifiers then true else before.consumed nullifier
  available := fun lane => before.available lane - intent.exactCharge lane
  history := before.history ++ [intent.event]
  journal := (intent.transactionId, intent) :: before.journal

@[simp] theorem lookupRecorded_install
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    lookupRecorded intent.transactionId (install before intent).journal =
      some intent := by
  simp [install, lookupRecorded]

@[simp] theorem install_roots
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    (install before intent).roots = fun cellId =>
      (lookupPost cellId intent.rootWrites).getD (before.roots cellId) :=
  rfl

@[simp] theorem install_consumes
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (nullifier : Nullifier) (present : nullifier ∈ intent.nullifiers) :
    (install before intent).consumed nullifier = true := by
  simp [install, present]

@[simp] theorem install_preserves_other_nullifier
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (nullifier : Nullifier) (absent : nullifier ∉ intent.nullifiers) :
    (install before intent).consumed nullifier = before.consumed nullifier := by
  simp [install, absent]

@[simp] theorem install_history
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    (install before intent).history = before.history ++ [intent.event] :=
  rfl

@[simp] theorem install_journal
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    (install before intent).journal =
      (intent.transactionId, intent) :: before.journal :=
  rfl

/-- Successful preflight funding makes the model debit exact in every lane. -/
theorem install_exact_debit
    [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (funded : intent.exactCharge <= before.available) :
    intent.exactCharge + (install before intent).available = before.available := by
  funext lane
  change intent.exactCharge lane +
    (before.available lane - intent.exactCharge lane) = before.available lane
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (funded lane)

end Snapshot

/-! ## Executable preflight, crash schedules, and retry -/

inductive RejectReason
  | transactionConflict
  | noCells
  | duplicateCell
  | duplicateNullifier
  | stalePreRoot
  | alreadyConsumed
  | insufficientBudget
  deriving DecidableEq, Repr

inductive CrashPoint
  | beforeAtomicInstall
  | afterAtomicInstall
  deriving DecidableEq, Repr

/-- A schedule is explicit protocol input used to study crash behavior. -/
inductive Schedule
  | complete
  | crash (point : CrashPoint)
  deriving DecidableEq, Repr

namespace Intent

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}

def rootsMatchCheck [DecidableEq CellId]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) : Bool :=
  intent.rootWrites.all fun write =>
    decide (before.roots write.cellId = write.expectedPre)

@[simp] theorem rootsMatchCheck_eq_true_iff [DecidableEq CellId]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    intent.rootsMatchCheck before = true <->
      forall write, write ∈ intent.rootWrites ->
        before.roots write.cellId = write.expectedPre := by
  simp [rootsMatchCheck]

def nullifiersFreshCheck [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) : Bool :=
  intent.nullifiers.all fun nullifier =>
    decide (before.consumed nullifier = false)

@[simp] theorem nullifiersFreshCheck_eq_true_iff [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    intent.nullifiersFreshCheck before = true <->
      forall nullifier, nullifier ∈ intent.nullifiers ->
        before.consumed nullifier = false := by
  simp [nullifiersFreshCheck]

/-- Ordered fail-closed preflight. A claim-only intent is a real atomic
mutation of the consumed-nullifier set, charge, history, and retry journal;
an intent with neither a cell write nor a claim remains a no-op refusal.
The checks read only the atomic snapshot, and no candidate post is exposed on
any error branch. -/
def preflight [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) : Except RejectReason Unit :=
  if intent.rootWrites = [] ∧ intent.nullifiers = [] then
    .error .noCells
  else if !(decide (intent.rootWrites.map RootWrite.cellId).Nodup) then
    .error .duplicateCell
  else if !(decide intent.nullifiers.Nodup) then
    .error .duplicateNullifier
  else if !intent.rootsMatchCheck before then
    .error .stalePreRoot
  else if !intent.nullifiersFreshCheck before then
    .error .alreadyConsumed
  else if !Charge.fundedCheck intent.exactCharge before.available then
    .error .insufficientBudget
  else
    .ok ()

theorem preflight_empty_effect_rejected [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (noWrites : intent.rootWrites = []) (noClaims : intent.nullifiers = []) :
    intent.preflight before = .error .noCells := by
  simp [Intent.preflight, noWrites, noClaims]

theorem preflight_claim_only_ready [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (noWrites : intent.rootWrites = []) (hasClaim : intent.nullifiers ≠ [])
    (distinctClaims : intent.nullifiers.Nodup)
    (fresh : intent.nullifiersFreshCheck before = true)
    (funded : Charge.fundedCheck intent.exactCharge before.available = true) :
    intent.preflight before = .ok () := by
  simp [Intent.preflight, noWrites, hasClaim, distinctClaims, fresh, funded,
    Intent.rootsMatchCheck]

theorem install_claim_only_preserves_roots [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (noWrites : intent.rootWrites = []) :
    (Snapshot.install before intent).roots = before.roots := by
  funext cellId
  simp [Snapshot.install, noWrites, Snapshot.lookupPost]

theorem preflight_spent_single_claim_rejected [DecidableEq CellId]
    [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) (claim : Nullifier)
    (noWrites : intent.rootWrites = [])
    (oneClaim : intent.nullifiers = [claim])
    (spent : before.consumed claim = true) :
    intent.preflight before = .error .alreadyConsumed := by
  simp [Intent.preflight, noWrites, oneClaim, Intent.rootsMatchCheck,
    Intent.nullifiersFreshCheck, spent]

/-- The compare-and-swap guard, refuting pole: a well-formed intent naming a
cell whose durable root is not the root it was prepared against is refused as
stale, before any nullifier, charge, or history is touched. -/
theorem preflight_stale_root_rejected [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (write : RootWrite CellId) (mem : write ∈ intent.rootWrites)
    (stale : before.roots write.cellId ≠ write.expectedPre)
    (distinctCells : (intent.rootWrites.map RootWrite.cellId).Nodup)
    (distinctClaims : intent.nullifiers.Nodup) :
    intent.preflight before = .error .stalePreRoot := by
  have nonempty : intent.rootWrites ≠ [] := List.ne_nil_of_mem mem
  have mismatch : intent.rootsMatchCheck before = false := by
    cases matched : intent.rootsMatchCheck before
    · rfl
    · exact absurd ((rootsMatchCheck_eq_true_iff before intent).1 matched write mem) stale
  simp [Intent.preflight, nonempty, distinctCells, distinctClaims, mismatch]

end Intent


/-- Protocol results carry a replacement snapshot only for a complete atomic
install or an explicitly modeled crash after that install. -/
inductive Outcome
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x)
  | accepted (next : Snapshot TxId CellId Nullifier Event)
  | replayed (recorded : Intent TxId CellId Nullifier Event)
  | rejected (reason : RejectReason)
  | crashed (point : CrashPoint) (next : Snapshot TxId CellId Nullifier Event)

namespace Outcome

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}

/-- Observed durable state.  Replays and rejections are identities; crash state
is explicit because a lost response may happen on either side of the atomic
install. -/
def storeAfter (before : Snapshot TxId CellId Nullifier Event) :
    Outcome TxId CellId Nullifier Event -> Snapshot TxId CellId Nullifier Event
  | .accepted next => next
  | .replayed _ => before
  | .rejected _ => before
  | .crashed _ next => next

end Outcome

/-- Execute one retry-safe transaction.  Journal lookup precedes pre-root and
nullifier checks, so a lost successful response is recognized as replay even
though the first installation changed roots and consumed nullifiers. -/
def execute
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
  (schedule : Schedule) (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    Outcome TxId CellId Nullifier Event :=
  match Snapshot.lookupRecorded intent.transactionId before.journal with
  | some recorded =>
      if recorded.sameCheck intent then .replayed recorded
      else .rejected .transactionConflict
  | none =>
      match intent.preflight before with
      | .error reason => .rejected reason
      | .ok () =>
          match schedule with
          | .complete => .accepted (Snapshot.install before intent)
          | .crash .beforeAtomicInstall => .crashed .beforeAtomicInstall before
          | .crash .afterAtomicInstall =>
              .crashed .afterAtomicInstall (Snapshot.install before intent)

/-- The central atomicity statement.  Every accepted, replayed, rejected, or
crashed execution exposes either the entire old snapshot or the entire
installed snapshot.  There is no third, partially committed semantic state. -/
theorem execute_no_partial_commit
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (schedule : Schedule) (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    (execute schedule before intent).storeAfter before = before \/
      (execute schedule before intent).storeAfter before =
        Snapshot.install before intent := by
  simp only [execute]
  split
  · split <;> simp [Outcome.storeAfter]
  · split
    · simp [Outcome.storeAfter]
    · split <;> simp [Outcome.storeAfter]

/-- Positive non-vacuity tooth: an unrecorded intent that passes the complete
fail-closed preflight reaches exactly the one atomic installation. -/
theorem execute_complete_ready
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId before.journal = none)
    (ready : intent.preflight before = .ok ()) :
    execute .complete before intent =
      .accepted (Snapshot.install before intent) := by
  simp [execute, unrecorded, ready]

/-- Execution-level stale refusal: an unrecorded intent whose guard fails
leaves the durable snapshot untouched under every schedule. -/
theorem execute_stale_root_rejected
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (schedule : Schedule) (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId before.journal = none)
    (write : RootWrite CellId) (mem : write ∈ intent.rootWrites)
    (stale : before.roots write.cellId ≠ write.expectedPre)
    (distinctCells : (intent.rootWrites.map RootWrite.cellId).Nodup)
    (distinctClaims : intent.nullifiers.Nodup) :
    execute schedule before intent = .rejected .stalePreRoot := by
  simp [execute, unrecorded,
    Intent.preflight_stale_root_rejected before intent write mem stale
      distinctCells distinctClaims]

/-- A retry after any complete installation is idempotent and returns the
original recorded payload without touching roots, nullifiers, budget, or
history a second time. -/
@[simp] theorem execute_retry_after_install
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (schedule : Schedule) (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    execute schedule (Snapshot.install before intent) intent =
      .replayed intent := by
  unfold execute
  simp [Snapshot.install, Snapshot.lookupRecorded]

/-- Crash-before is an identity whenever the transaction reaches the install
barrier. -/
theorem execute_crash_before
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId before.journal = none)
    (ready : intent.preflight before = .ok ()) :
    execute (.crash .beforeAtomicInstall) before intent =
      .crashed .beforeAtomicInstall before := by
  simp [execute, unrecorded, ready]

/-- Crash-after exposes the complete atomic installation; its retry is the
same idempotent replay as an ordinary lost response. -/
theorem execute_crash_after_then_retry
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId before.journal = none)
    (ready : intent.preflight before = .ok ()) :
    execute (.crash .afterAtomicInstall) before intent =
        .crashed .afterAtomicInstall (Snapshot.install before intent) /\
      execute .complete (Snapshot.install before intent) intent =
        .replayed intent := by
  constructor
  · simp [execute, unrecorded, ready]
  · simp

/-- A claim-only event has the same exact lost-reply recovery as a cell write:
the crash-after image has unchanged roots, but its claim, charge and original
journal record are installed atomically, so retry cannot charge it twice. -/
theorem execute_claim_only_crash_after_then_retry
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (noWrites : intent.rootWrites = [])
    (unrecorded : Snapshot.lookupRecorded intent.transactionId before.journal = none)
    (ready : intent.preflight before = .ok ()) :
    execute (.crash .afterAtomicInstall) before intent =
        .crashed .afterAtomicInstall (Snapshot.install before intent) ∧
      execute .complete (Snapshot.install before intent) intent = .replayed intent ∧
      (Snapshot.install before intent).roots = before.roots := by
  rcases execute_crash_after_then_retry before intent unrecorded ready with
    ⟨crashed, replayed⟩
  exact ⟨crashed, replayed, Intent.install_claim_only_preserves_roots before intent noWrites⟩

/-! ## Commit-indexed multi-cell metering -/

/-- Explicit byte-accounting policy for a durable multi-cell installation.
`base` prices protocol work not determined by the handler shape (for example
proof work or network intent).  Root, nullifier, and event storage are then
added by Lean from the exact accepted commit and exact event.

The sizes are protocol codec facts supplied when defining a deployment policy;
they are not executor-reported counters. -/
structure MultiCellCostPolicy (Nullifier : Type w) (Event : Type x) where
  base : Charge
  rootWriteBytes : Nat
  nullifierBytes : Nullifier -> Nat
  eventBytes : Event -> Nat

namespace MultiCellCostPolicy

variable {Nullifier : Type w} {Event : Type x}

/-- Shape-derived exact handler charge.  Incidences and memory touches replace
the corresponding base coordinates.  Durable storage and side-effect counts
add every exact root write, eager nullifier, and the one appended event. -/
def exact
    (policy : MultiCellCostPolicy Nullifier Event)
    (rootCount memoryTouches : Nat) (nullifiers : List Nullifier)
    (event : Event) : Charge :=
  fun lane =>
    match lane with
    | .incidences => rootCount
    | .memoryTouches => memoryTouches
    | .storageBytes =>
        policy.base .storageBytes +
          rootCount * policy.rootWriteBytes +
          (nullifiers.map policy.nullifierBytes).sum +
          policy.eventBytes event
    | .sideEffectCount =>
        policy.base .sideEffectCount + rootCount + nullifiers.length + 1
    | other => policy.base other

@[simp] theorem exact_incidences
    (policy : MultiCellCostPolicy Nullifier Event)
    (rootCount memoryTouches : Nat) (nullifiers : List Nullifier)
    (event : Event) :
    policy.exact rootCount memoryTouches nullifiers event .incidences =
      rootCount :=
  rfl

@[simp] theorem exact_memoryTouches
    (policy : MultiCellCostPolicy Nullifier Event)
    (rootCount memoryTouches : Nat) (nullifiers : List Nullifier)
    (event : Event) :
    policy.exact rootCount memoryTouches nullifiers event .memoryTouches =
      memoryTouches :=
  rfl

@[simp] theorem exact_storageBytes
    (policy : MultiCellCostPolicy Nullifier Event)
    (rootCount memoryTouches : Nat) (nullifiers : List Nullifier)
    (event : Event) :
    policy.exact rootCount memoryTouches nullifiers event .storageBytes =
      policy.base .storageBytes +
        rootCount * policy.rootWriteBytes +
        (nullifiers.map policy.nullifierBytes).sum + policy.eventBytes event :=
  rfl

@[simp] theorem exact_sideEffectCount
    (policy : MultiCellCostPolicy Nullifier Event)
    (rootCount memoryTouches : Nat) (nullifiers : List Nullifier)
    (event : Event) :
    policy.exact rootCount memoryTouches nullifiers event .sideEffectCount =
      policy.base .sideEffectCount + rootCount + nullifiers.length + 1 :=
  rfl

end MultiCellCostPolicy

/-- Exact typed patch touches across a complete heterogeneous accepted family:
the sum of every leg's write footprint (one address per guarded write or
allocation).  This is derived from the same family patches already validated by
`MultiCellHyperedge.Commit`; no executor touch counter is accepted. -/
def multiCellMemoryTouches
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    (_commit : MultiCellHyperedge.Commit law accepted boundary) : Nat :=
  Finset.univ.sum fun incidence =>
    (Store.Patch.writeFootprint ((declaration.legs incidence).family.patch
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome)).card

/-- The metered touches are exactly the footprints of the accepted legs'
canonical deltas, so the charge is indexed by what each validated patch
changed, not by a second syntactic reading. -/
theorem multiCellMemoryTouches_eq_accepted_footprints
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    (commit : MultiCellHyperedge.Commit law accepted boundary) :
    multiCellMemoryTouches commit =
      Finset.univ.sum fun incidence =>
        (accepted incidence).prepared.delta.footprint.card :=
  rfl

/-- A bounded quote indexed by one exact accepted multi-cell commit and one
exact appended event.  Unlike an arbitrary `Quote`, its exact coordinate is
definitionally derived from the accepted commit and explicit deployment cost
policy. -/
structure BoundedMultiCellCommit
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    (commit : MultiCellHyperedge.Commit law accepted boundary)
    (Event : Type p) (event : Event) where
  policy : MultiCellCostPolicy (MultiCellHyperedge.JointNullifier accepted) Event
  upper : Charge
  exact_le_upper :
    policy.exact (Fintype.card Incidence) (multiCellMemoryTouches commit)
      commit.nullifiers event <= upper

namespace BoundedMultiCellCommit

variable
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {commit : MultiCellHyperedge.Commit law accepted boundary}
    {Event : Type p} {event : Event}

noncomputable def quote
    (bounded : BoundedMultiCellCommit commit Event event) : Quote where
  upper := bounded.upper
  exact := bounded.policy.exact (Fintype.card Incidence)
    (multiCellMemoryTouches commit) commit.nullifiers event
  exact_le_upper := bounded.exact_le_upper

@[simp] theorem quote_exact
    (bounded : BoundedMultiCellCommit commit Event event) :
    bounded.quote.exact =
      bounded.policy.exact (Fintype.card Incidence)
        (multiCellMemoryTouches commit) commit.nullifiers event :=
  rfl

end BoundedMultiCellCommit

/-! ## Adapters from the existing semantic and receipt types -/

namespace Intent

/- The single-cell adapters (`ofPreparedTurn`, `ofAcceptedEffect` and its
root/preflight poles, `ofTypedCellHyperedge`) are gone: an accepted effect is a
`Kernel.World.Leg` (`Kernel.TurnRecord.Leg.ofAccepted`), its post root is derived
by `World.step` (`TurnRecord.step_ofAccepted_root`), and a stale pre-store is
refused by the leg guard (`World.step_leg`, `Example.reject_guardFailed`).  A
same-cell typed hyperedge is one leg carrying the concatenated patch (C3). -/

/-- A heterogeneous multi-cell commit yields one write per incidence, with
the exact pre/post roots owned by its complete accepted family.

This is deliberately named `WithOpaqueEvent`: `event` is appended exactly but
this generic adapter does not claim the value is a semantic receipt.  Exact
receipt specializations must supply an existing indexed receipt type, as
`ofMultiCellJointReceipt` does below. -/
noncomputable def ofMultiCellWithOpaqueEvent
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (_funding : ChargeReceipt available bounded.quote) :
    Intent TypedAuthorization.Digest TypedAuthorization.Digest
      (MultiCellHyperedge.JointNullifier accepted) Event where
  transactionId := declaration.header.turnId
  rootWrites := Finset.univ.toList.map fun incidence =>
    { cellId := cells.cellId incidence
      expectedPre := (declaration.pre incidence).root
      exactPost := (commit.post incidence).root }
  nullifiers := commit.nullifiers
  exactCharge := bounded.quote.exact
  event := event

/-- The smallest joint receipt specialization appends the exact handler-bound
`JointCommitInput`, including its receipt root.  Richer indexed history events
can use `ofMultiCellWithOpaqueEvent` while retaining their own relation proof. -/
noncomputable def ofMultiCellJointReceipt
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    (commit : MultiCellHyperedge.Commit law accepted boundary)
    (bounded : BoundedMultiCellCommit commit
      MultiCellHyperedge.JointCommitInput commit.jointInput)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    Intent TypedAuthorization.Digest TypedAuthorization.Digest
      (MultiCellHyperedge.JointNullifier accepted)
      MultiCellHyperedge.JointCommitInput :=
  ofMultiCellWithOpaqueEvent commit commit.jointInput bounded available funding

@[simp] theorem ofMultiCell_exactCharge
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    (ofMultiCellWithOpaqueEvent commit event bounded available funding).exactCharge =
      bounded.quote.exact :=
  rfl

@[simp] theorem ofMultiCell_rootWrites_length
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    (ofMultiCellWithOpaqueEvent commit event bounded available funding).rootWrites.length =
      Fintype.card Incidence := by
  simp [ofMultiCellWithOpaqueEvent]

/-- Every durable write of a multi-cell commit is guarded at the root its leg's
request quoted and installs the root of that leg's family patch run on its
canonical pre-store. -/
theorem ofMultiCell_rootWrites_exact
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    (ofMultiCellWithOpaqueEvent commit event bounded available funding).rootWrites =
      Finset.univ.toList.map fun incidence =>
        { cellId := cells.cellId incidence
          expectedPre := (declaration.legs incidence).request.preStateRoot
          exactPost := (cells.materializer incidence).rootOf
            (Store.Patch.run (declaration.pre incidence).logical
              ((declaration.legs incidence).family.patch
                (declaration.legs incidence).declaration
                (declaration.legs incidence).outcome)) } := by
  simp only [ofMultiCellWithOpaqueEvent,
    MultiCellHyperedge.Declaration.accepted_request_preRoot declaration accepted]
  rfl

/-- Multi-cell semantic admission already proves cell identities injective, so
the derived durable write set cannot fail the duplicate-cell preflight check. -/
theorem ofMultiCell_cellIds_nodup
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    ((ofMultiCellWithOpaqueEvent commit event bounded available funding).rootWrites.map
      RootWrite.cellId).Nodup := by
  have incidenceNodup : (Finset.univ.toList : List Incidence).Nodup :=
    (Finset.univ : Finset Incidence).nodup_toList
  have cellNodup := List.Nodup.map commit.cellIdsDistinct incidenceNodup
  simpa [ofMultiCellWithOpaqueEvent, Function.comp_def] using cellNodup

end Intent

/-! ## Explicit physical implementation refinement premise -/

/-- A real DB/network/filesystem handler refines this protocol only by
supplying a simulation indexed by its actual physical states and steps.

`PhysicalStep` is proof-relevant implementation evidence, not an `atomic`
Boolean.  This module deliberately provides no constructor for a particular
implementation: transaction configuration, write-ahead logging, replication,
and failure recovery must establish `simulates` externally. -/
structure ImplementationRefinement
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x)
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    (PhysicalState : Type p)
    (PhysicalStep : PhysicalState -> Intent TxId CellId Nullifier Event ->
      PhysicalState -> Type q)
    (Represents : PhysicalState -> Snapshot TxId CellId Nullifier Event -> Prop) : Prop where
  simulates : forall {physicalBefore physicalAfter modelBefore intent},
    Represents physicalBefore modelBefore ->
    PhysicalStep physicalBefore intent physicalAfter ->
    exists schedule,
      Represents physicalAfter
        ((execute schedule modelBefore intent).storeAfter modelBefore)

/-- Conditional physical atomicity: an implementation step that discharges the
explicit refinement premise represents either the complete old snapshot or the
complete installed snapshot.  The theorem does not assert that any concrete
database has discharged that premise. -/
theorem physical_step_no_partial_commit
    {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event]
    {PhysicalState : Type p}
    {PhysicalStep : PhysicalState -> Intent TxId CellId Nullifier Event ->
      PhysicalState -> Type q}
    {Represents : PhysicalState -> Snapshot TxId CellId Nullifier Event -> Prop}
    (refinement : ImplementationRefinement TxId CellId Nullifier Event
      PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : Snapshot TxId CellId Nullifier Event}
    {intent : Intent TxId CellId Nullifier Event}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore intent physicalAfter) :
    exists modelAfter,
      Represents physicalAfter modelAfter /\
        (modelAfter = modelBefore \/
          modelAfter = Snapshot.install modelBefore intent) := by
  rcases refinement.simulates represented stepped with ⟨schedule, simulated⟩
  refine ⟨(execute schedule modelBefore intent).storeAfter modelBefore,
    simulated, ?_⟩
  exact execute_no_partial_commit schedule modelBefore intent

end Minidregg.Kernel.DurableCommitProtocol

/-- info: 'Minidregg.Kernel.DurableCommitProtocol.execute_no_partial_commit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.execute_no_partial_commit
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.execute_complete_ready' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.execute_complete_ready
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.execute_retry_after_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.execute_retry_after_install
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.execute_crash_after_then_retry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.execute_crash_after_then_retry
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.Intent.ofMultiCellJointReceipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.Intent.ofMultiCellJointReceipt
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.physical_step_no_partial_commit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.physical_step_no_partial_commit
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.execute_stale_root_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.execute_stale_root_rejected
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.multiCellMemoryTouches_eq_accepted_footprints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.multiCellMemoryTouches_eq_accepted_footprints
/-- info: 'Minidregg.Kernel.DurableCommitProtocol.Intent.ofMultiCell_rootWrites_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCommitProtocol.Intent.ofMultiCell_rootWrites_exact
