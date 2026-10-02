/-!
# Explicit activation after an audited legacy execution cut

This is a pure after-core carry helper. The caller must bind the clock and
history digest to its actual authenticated source cut/origin index, and must
keep legacy execution quiescent. A nonzero digest is only a non-placeholder
check; it proves neither provenance nor physical quiescence.

The neutral v4 lift alone does not activate accounting. This helper requires
its empty compute namespace, an absent append-only activation, and a current
clock day strictly AFTER the closed legacy day. There is no fresh-genesis
fallback and no inference that missing historical records mean zero usage.
-/
import Kernel.PayCell
import Kernel.ClockCell

namespace Minidregg.Kernel.RunComputeActivation

open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- An executable scan of the actual typed store's finite support. -/
def UsageEmpty (store : PayCell.PayStore) : Prop :=
  ∀ address ∈ store.support, address.1 ≠ .computeUsage

instance (store : PayCell.PayStore) : Decidable (UsageEmpty store) := by
  unfold UsageEmpty
  infer_instance

theorem UsageEmpty.absent {store : PayCell.PayStore} (empty : UsageEmpty store)
    (subject : Nat) : PayCell.computeUsageAt store subject = none := by
  by_contra present
  have member : PayCell.computeUsageAddress subject ∈ store.support :=
    DFinsupp.mem_support_iff.mpr present
  exact empty _ member rfl

/-- This constructor always records a closed legacy history, never genesis. -/
def activation (clock : ClockCell.Clock) (legacyThroughDay : Nat) (history : Digest) :
    PayCell.ComputeActivation :=
  ⟨clock.now / ClockCell.secondsPerDay, some legacyThroughDay, history⟩

def patch (clock : ClockCell.Clock) (legacyThroughDay : Nat) (history : Digest) :
    Patch PayCell.layout :=
  [.allocate .computeActivation () (activation clock legacyThroughDay history)]

theorem patch_frame (store : PayCell.PayStore) (clock : ClockCell.Clock)
    (legacyThroughDay : Nat) (history : Digest) (address : Address PayCell.layout)
    (outside : address ≠ PayCell.computeActivationAddress) :
    Patch.run store (patch clock legacyThroughDay history) address = store address := by
  apply Patch.run_frame
  simpa [patch, Patch.writeFootprint, Op.writeAddress?, PayCell.computeActivationAddress]
    using outside

inductive Reject where
  | legacyDayNotClosed
  | historyMissing
  | alreadyActive
  | usagePresent
  | patchRejected (reason : RejectReason)
  deriving DecidableEq, Repr

/-- Exact source values and checked conditions, not authenticated carry authority.
Only prepare constructs this token. Inputs remain indices so consumers cannot
accidentally attribute a result to a different clock, cutoff or history. -/
structure Prepared (pre : PayCell.Cell) (expectedRoot : Digest)
    (clock : ClockCell.Clock) (legacyThroughDay : Nat) (history : Digest) where
  private mk ::
  dayAfter : legacyThroughDay < clock.now / ClockCell.secondsPerDay
  historyNonzero : history.value ≠ 0
  activationAbsent : PayCell.computeActivationOf pre.logical = none
  usageEmpty : UsageEmpty pre.logical
  validated : ValidatedPatch PayCell.materializer pre expectedRoot
    (patch clock legacyThroughDay history)

/-- Supply the actual authenticated clock and audited history at the carry
boundary. Materializer validation binds expectedRoot to this exact pre-cell. -/
def prepare (pre : PayCell.Cell) (expectedRoot : Digest) (clock : ClockCell.Clock)
    (legacyThroughDay : Nat) (history : Digest) :
    Except Reject (Prepared pre expectedRoot clock legacyThroughDay history) :=
  if closed : legacyThroughDay < clock.now / ClockCell.secondsPerDay then
    if nonzero : history.value ≠ 0 then
      if absent : PayCell.computeActivationOf pre.logical = none then
        if empty : UsageEmpty pre.logical then
          match validate PayCell.materializer pre expectedRoot (patch clock legacyThroughDay history) with
          | .rejected reason => .error (.patchRejected reason)
          | .accepted validated => .ok ⟨closed, nonzero, absent, empty, validated⟩
        else .error .usagePresent
      else .error .alreadyActive
    else .error .historyMissing
  else .error .legacyDayNotClosed

def Prepared.post {pre : PayCell.Cell} {expectedRoot : Digest}
    {clock : ClockCell.Clock} {legacyThroughDay : Nat} {history : Digest}
    (prepared : Prepared pre expectedRoot clock legacyThroughDay history) : PayCell.Cell :=
  prepared.validated.apply

theorem Prepared.root_exact {pre : PayCell.Cell} {expectedRoot : Digest}
    {clock : ClockCell.Clock} {legacyThroughDay : Nat} {history : Digest}
    (prepared : Prepared pre expectedRoot clock legacyThroughDay history) :
    expectedRoot = pre.root :=
  prepared.validated.preRoot_bound

theorem Prepared.activation_valid {pre : PayCell.Cell} {expectedRoot : Digest}
    {clock : ClockCell.Clock} {legacyThroughDay : Nat} {history : Digest}
    (prepared : Prepared pre expectedRoot clock legacyThroughDay history) :
    (activation clock legacyThroughDay history).valid :=
  prepared.dayAfter

/-- The post contains exactly the supplied closed-history activation. -/
theorem Prepared.activation_exact {pre : PayCell.Cell} {expectedRoot : Digest}
    {clock : ClockCell.Clock} {legacyThroughDay : Nat} {history : Digest}
    (prepared : Prepared pre expectedRoot clock legacyThroughDay history) :
    PayCell.computeActivationOf prepared.post.logical =
      some (activation clock legacyThroughDay history) := by
  simp [PayCell.computeActivationOf, Prepared.post, ValidatedPatch.apply_logical,
    patch, Patch.run, Op.apply, PayCell.computeActivationAddress]

/-- Payment, custody, tariff, and every subject usage row survive exactly. -/
theorem Prepared.preserves {pre : PayCell.Cell} {expectedRoot : Digest}
    {clock : ClockCell.Clock} {legacyThroughDay : Nat} {history : Digest}
    (prepared : Prepared pre expectedRoot clock legacyThroughDay history)
    (address : Address PayCell.layout) (outside : address ≠ PayCell.computeActivationAddress) :
    prepared.post.logical address = pre.logical address := by
  exact patch_frame pre.logical clock legacyThroughDay history address outside

/-- Same-day activation cannot erase the remainder of a legacy execution day. -/
theorem prepare_refuses_unclosed (pre : PayCell.Cell) (root : Digest)
    (clock : ClockCell.Clock) (legacyThroughDay : Nat) (history : Digest)
    (unclosed : clock.now / ClockCell.secondsPerDay ≤ legacyThroughDay) :
    prepare pre root clock legacyThroughDay history = .error .legacyDayNotClosed := by
  simp [prepare, Nat.not_lt.mpr unclosed]

theorem prepare_refuses_placeholder (pre : PayCell.Cell) (root : Digest)
    (clock : ClockCell.Clock) (legacyThroughDay : Nat)
    (closed : legacyThroughDay < clock.now / ClockCell.secondsPerDay) :
    prepare pre root clock legacyThroughDay ⟨0⟩ = .error .historyMissing := by
  simp [prepare, closed]

end Minidregg.Kernel.RunComputeActivation
