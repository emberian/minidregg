/-
# Kernel.DurableCommitProtocol -- fail-closed durable settlement model

`CanonicalTransition.PreparedTurn`, `TypedCellHyperedge`, and
`MultiCellHyperedge` determine logical meaning.  This module does not interpret
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
import Kernel.TypedCellHyperedge
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

/-- Ordered fail-closed preflight.  The checks read only the atomic snapshot;
no candidate post is exposed on any error branch. -/
def preflight [DecidableEq CellId] [DecidableEq Nullifier]
    (before : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) : Except RejectReason Unit :=
  if intent.rootWrites = [] then
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

/-- Exact typed patch touches across a complete heterogeneous accepted family.
This is derived from the same family patches already validated by
`MultiCellHyperedge.Commit`; no executor touch counter is accepted. -/
noncomputable def multiCellMemoryTouches
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
      declaration}
    (_commit : MultiCellHyperedge.Commit law accepted boundary) : Nat :=
  Finset.univ.sum fun incidence =>
    ((declaration.legs incidence).family.patch
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome).fieldFootprint.card +
    ((declaration.legs incidence).family.patch
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome).resourceFootprint.card

/-- A bounded quote indexed by one exact accepted multi-cell commit and one
exact appended event.  Unlike an arbitrary `Quote`, its exact coordinate is
definitionally derived from the accepted commit and explicit deployment cost
policy. -/
structure BoundedMultiCellCommit
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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

/-- One canonical prepared turn becomes one exact durable root write.  The
funding witness is the existing `ChargeReceipt`; the runtime still rechecks the
currently observed snapshot because the budget may have changed since quote
construction. -/
def ofPreparedTurn
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {pre : CellState.Materialized M} {Nullifier : Type y}
    (transactionId : TxId) (cellId : CellId)
    (turn : PreparedTurn M pre Nullifier)
    (bounded : BoundedPreparedTurn turn)
    (available : Charge) (_funding : ChargeReceipt available bounded.quote)
    (event : Event) : Intent TxId CellId Nullifier Event where
  transactionId := transactionId
  rootWrites := [{ cellId := cellId
                   expectedPre := turn.preRoot
                   exactPost := turn.postRoot }]
  nullifiers := turn.nullifier.toList
  exactCharge := bounded.quote.exact
  event := event

@[simp] theorem ofPreparedTurn_roots
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {pre : CellState.Materialized M} {Nullifier : Type y}
    (transactionId : TxId) (cellId : CellId)
    (turn : PreparedTurn M pre Nullifier)
    (bounded : BoundedPreparedTurn turn)
    (available : Charge) (funding : ChargeReceipt available bounded.quote)
    (event : Event) :
    (ofPreparedTurn transactionId cellId turn bounded available funding event).rootWrites =
      [{ cellId := cellId
         expectedPre := turn.preRoot
         exactPost := turn.postRoot }] :=
  rfl

@[simp] theorem ofPreparedTurn_nullifiers
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {pre : CellState.Materialized M} {Nullifier : Type y}
    (transactionId : TxId) (cellId : CellId)
    (turn : PreparedTurn M pre Nullifier)
    (bounded : BoundedPreparedTurn turn)
    (available : Charge) (funding : ChargeReceipt available bounded.quote)
    (event : Event) :
    (ofPreparedTurn transactionId cellId turn bounded available funding event).nullifiers =
      turn.nullifier.toList :=
  rfl

@[simp] theorem ofPreparedTurn_exactCharge
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {pre : CellState.Materialized M} {Nullifier : Type y}
    (transactionId : TxId) (cellId : CellId)
    (turn : PreparedTurn M pre Nullifier)
    (bounded : BoundedPreparedTurn turn)
    (available : Charge) (funding : ChargeReceipt available bounded.quote)
    (event : Event) :
    (ofPreparedTurn transactionId cellId turn bounded available funding event).exactCharge =
      bounded.quote.exact :=
  rfl

/-- The ordinary one-cell receipt adapter uses the existing receipt projection,
whose constructor is private and therefore already indexed by the exact
accepted semantic effect. -/
def ofAcceptedEffect
    {TxId : Type u} {CellId : Type v}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {portal : TypedAuthorization.Portal}
    {authState : TypedAuthorization.AuthState}
    {kind : TypedAuthorization.ResourceKind}
    {request : TypedAuthorization.Request kind}
    {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (transactionId : TxId) (cellId : CellId)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (bounded : BoundedPreparedTurn accepted.prepared)
    (available : Charge) (funding : ChargeReceipt available bounded.quote) :
    Intent TxId CellId Nullifier (ReceiptEvent family) :=
  ofPreparedTurn transactionId cellId accepted.prepared bounded available funding
    accepted.toReceiptEvent

/-- A same-cell typed hyperedge has one canonical root transition but many
heterogeneous incidence nullifiers.  Its `PreparedTurn` stores that complete
list in one optional slot; this dedicated adapter deliberately flattens the
list so every eager nullifier is consumed individually by `Snapshot.install`. -/
def ofTypedCellHyperedge
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {portal : TypedAuthorization.Portal}
    {projection : TypedCellHyperedge.AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : TypedCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      S M portal Coordinate Balance}
    {declaration : TypedCellHyperedge.Declaration.{u, v, w, x, y, z}
      S M portal projection Incidence}
    (transactionId : TxId) (cellId : CellId)
    (commit : TypedCellHyperedge.Commit law declaration)
    (bounded : BoundedPreparedTurn commit.prepared)
    (available : Charge) (_funding : ChargeReceipt available bounded.quote)
    (event : Event) :
    Intent TxId CellId declaration.JointNullifier Event where
  transactionId := transactionId
  rootWrites := [{ cellId := cellId
                   expectedPre := commit.prepared.preRoot
                   exactPost := commit.prepared.postRoot }]
  nullifiers := declaration.jointNullifiers
  exactCharge := bounded.quote.exact
  event := event

@[simp] theorem ofTypedCellHyperedge_nullifiers
    {TxId : Type u} {CellId : Type v} {Event : Type p}
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S TypedAuthorization.Digest}
    {portal : TypedAuthorization.Portal}
    {projection : TypedCellHyperedge.AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : TypedCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      S M portal Coordinate Balance}
    {declaration : TypedCellHyperedge.Declaration.{u, v, w, x, y, z}
      S M portal projection Incidence}
    (transactionId : TxId) (cellId : CellId)
    (commit : TypedCellHyperedge.Commit law declaration)
    (bounded : BoundedPreparedTurn commit.prepared)
    (available : Charge) (funding : ChargeReceipt available bounded.quote)
    (event : Event) :
    (ofTypedCellHyperedge transactionId cellId commit bounded available funding event).nullifiers =
      declaration.jointNullifiers :=
  rfl

/-- A heterogeneous multi-cell commit yields one write per incidence, with
the exact pre/post roots owned by its complete accepted family.

This is deliberately named `WithOpaqueEvent`: `event` is appended exactly but
this generic adapter does not claim the value is a semantic receipt.  Exact
receipt specializations must supply an existing indexed receipt type, as
`ofMultiCellJointReceipt` does below. -/
noncomputable def ofMultiCellWithOpaqueEvent
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
      declaration}
    {Event : Type p}
    (commit : MultiCellHyperedge.Commit law accepted boundary) (event : Event)
    (bounded : BoundedMultiCellCommit commit Event event)
    (available : Charge)
    (funding : ChargeReceipt available bounded.quote) :
    (ofMultiCellWithOpaqueEvent commit event bounded available funding).rootWrites.length =
      Fintype.card Incidence := by
  simp [ofMultiCellWithOpaqueEvent]

/-- Multi-cell semantic admission already proves cell identities injective, so
the derived durable write set cannot fail the duplicate-cell preflight check. -/
theorem ofMultiCell_cellIds_nodup
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {cells : MultiCellHyperedge.CellFamily.{u, v, w, x, z} Incidence}
    {declaration : MultiCellHyperedge.Declaration.{u, v, w, x, y, z} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : MultiCellHyperedge.ResourceLaw.{u, v, w, x, y, z, b}
      declaration Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : MultiCellHyperedge.HandlerBoundary.{u, v, w, x, y, z, h}
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

#print axioms Minidregg.Kernel.DurableCommitProtocol.execute_no_partial_commit
#print axioms Minidregg.Kernel.DurableCommitProtocol.execute_complete_ready
#print axioms Minidregg.Kernel.DurableCommitProtocol.execute_retry_after_install
#print axioms Minidregg.Kernel.DurableCommitProtocol.execute_crash_after_then_retry
#print axioms Minidregg.Kernel.DurableCommitProtocol.Intent.ofAcceptedEffect
#print axioms Minidregg.Kernel.DurableCommitProtocol.Intent.ofMultiCellJointReceipt
#print axioms Minidregg.Kernel.DurableCommitProtocol.physical_step_no_partial_commit
