/-
Authenticated finalized-chain evidence for paid-entry decisions.

Only the checked payment-observer ingress writes this row. The deployment
Clock supplies the current time for a bounded freshness policy; it never
manufactures missing chain evidence. Finality and the chain RPC verification
remain the observer capability's responsibility. This module preserves the
exact asserted slot and block time, separately from the mixed deployment clock.
-/
import Kernel.PayReceivingContract
import Kernel.PayCell
import Kernel.ClockCell

namespace Minidregg.Kernel.PayChainTip

open Minidregg.Kernel.PayCell
open Minidregg.Theory.Store (Patch)

set_option autoImplicit false

def valid (tip : ChainTip) : Prop :=
  0 < tip.slot ∧ tip.slot < 2 ^ 64 ∧ 0 < tip.blockTime ∧ tip.blockTime < 2 ^ 64

instance (tip : ChainTip) : Decidable (valid tip) := by unfold valid; infer_instance

/-- Equal evidence is permitted here; durable ingress/tick nullifiers decide
retries. Neither finalized coordinate may move backward. -/
def advances (previous : Option ChainTip) (next : ChainTip) : Prop :=
  valid next ∧ match previous with
    | none => True
    | some before => before.slot ≤ next.slot ∧ before.blockTime ≤ next.blockTime ∧
        (before.slot = next.slot → before.blockTime = next.blockTime)

instance (previous : Option ChainTip) (next : ChainTip) : Decidable (advances previous next) := by
  unfold advances
  cases previous <;> infer_instance

/-- An exact-preimage RAM update; first evidence allocates only when absent. -/
def patch (previous : Option ChainTip) (next : ChainTip) : Patch PayCell.layout :=
  match previous with
  | none => [.allocate .chainTip () next]
  | some before => [.write .chainTip () before next]

theorem patch_tip (store : PayStore) (previous : Option ChainTip) (next : ChainTip) :
    chainTipOf (Patch.run store (patch previous next)) = some next := by
  cases previous <;> exact Minidregg.Theory.Store.Store.set_eq _ _ _

theorem advances_monotone (before next : ChainTip) (accepted : advances (some before) next) :
    before.slot ≤ next.slot ∧ before.blockTime ≤ next.blockTime := ⟨accepted.2.1, accepted.2.2.1⟩

inductive FreshnessReject where
  | missing | malformed | future | stale
  deriving DecidableEq, Repr

def defaultMaxLagSeconds : Nat := PayReceivingContract.defaultMaxLagSeconds

/-- The caller supplies the authenticated deployment clock. Check future time
before age: truncated natural subtraction must never make future evidence fresh.
The returned evidence exposes exact as-of slot, seconds and ChainTip.hour.
A maximum lag is policy data, with the initial 180-second default. -/
def fresh (clock : ClockCell.Clock) (evidence : Option ChainTip)
    (maxLagSeconds : Nat := defaultMaxLagSeconds) : Except FreshnessReject ChainTip :=
  match evidence with
  | none => .error .missing
  | some tip =>
    if ¬valid tip then .error .malformed
    else if clock.now < tip.blockTime then .error .future
    else if tip.blockTime + maxLagSeconds < clock.now then .error .stale
    else .ok tip

theorem missing_is_not_clock (clock : ClockCell.Clock) (maxLagSeconds : Nat) :
    fresh clock none maxLagSeconds = .error .missing := rfl

theorem future_refuses (clock : ClockCell.Clock) (tip : ChainTip) (maxLagSeconds : Nat)
    (shaped : valid tip) (future : clock.now < tip.blockTime) :
    fresh clock (some tip) maxLagSeconds = .error .future := by
  simp [fresh, shaped, future]

theorem fresh_exact (clock : ClockCell.Clock) (evidence : Option ChainTip)
    (maxLagSeconds : Nat) (tip : ChainTip)
    (accepted : fresh clock evidence maxLagSeconds = .ok tip) :
    evidence = some tip ∧ valid tip ∧
    tip.blockTime ≤ clock.now ∧ clock.now ≤ tip.blockTime + maxLagSeconds := by
  cases evidence with
  | none => cases accepted
  | some seen =>
    unfold fresh at accepted
    split at accepted
    · cases accepted
    rename_i shaped
    split at accepted
    · cases accepted
    rename_i notFuture
    split at accepted
    · cases accepted
    rename_i notStale
    injection accepted with same
    subst tip
    exact ⟨rfl, by simpa using shaped, by omega, by omega⟩

theorem missing_fixture :
    fresh ⟨1000, 99⟩ none = .error .missing := by decide

theorem lag_boundary_fixture :
    fresh ⟨1180, 99⟩ (some ⟨99, 1000⟩) = .ok ⟨99, 1000⟩ := by decide

theorem stale_fixture :
    fresh ⟨1181, 99⟩ (some ⟨99, 1000⟩) = .error .stale := by decide

theorem future_fixture :
    fresh ⟨999, 99⟩ (some ⟨99, 1000⟩) = .error .future := by decide

theorem malformed_fixture :
    fresh ⟨1000, 99⟩ (some ⟨0, 1000⟩) = .error .malformed := by decide

theorem earlier_block_time_refused :
    ¬advances (some ⟨99, 1000⟩) ⟨100, 999⟩ := by decide

theorem earlier_slot_refused :
    ¬advances (some ⟨99, 1000⟩) ⟨98, 1001⟩ := by decide

theorem same_slot_cannot_change_time :
    ¬advances (some ⟨99, 1000⟩) ⟨99, 1001⟩ := by decide

theorem identical_evidence_permitted :
    advances (some ⟨99, 1000⟩) ⟨99, 1000⟩ := by decide

#assert_axioms patch_tip
#assert_axioms advances_monotone
#assert_axioms missing_is_not_clock
#assert_axioms future_refuses
#assert_axioms fresh_exact
#assert_axioms missing_fixture
#assert_axioms lag_boundary_fixture
#assert_axioms stale_fixture
#assert_axioms future_fixture
#assert_axioms malformed_fixture
#assert_axioms earlier_block_time_refused
#assert_axioms earlier_slot_refused
#assert_axioms same_slot_cannot_change_time
#assert_axioms identical_evidence_permitted

end Minidregg.Kernel.PayChainTip
