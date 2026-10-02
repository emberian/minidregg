/-
A read-only enrollment quote. The Host supplies the receiver's exact account
birth fee at its loaded authority state; this module chooses no price and
changes neither enrollment decisions nor conservation.

Every whole membership week is consumed by the existing enrollment receiver.
Atomic rounding or the journal floor must therefore never silently buy an
extra week or consume the requested spendable starter remainder.
-/
import Kernel.PayTariff

namespace Minidregg.Kernel.PayEnrolQuote

open PayTariff

set_option autoImplicit false

inductive Reject where
  | tariffInvalid
  | weeksZero
  | starterTooLarge
  | observationCapExceeded
  | entryCreditUncovered
  | exactWeeksUnrepresentable
  | starterUnrepresentable
  deriving DecidableEq, Repr

structure Quote where
  amountAtomic : Nat
  credit : Nat
  birthFee : Nat
  requestedWeeks : Nat
  actualWeeks : Nat
  leaseCredit : Nat
  creditedRemainder : Nat
  minimumStarterCredit : Nat
  /-- The existing entry threshold: birth plus one week, excluding starter. -/
  minimumEntryCredit : Nat
  deriving DecidableEq, Repr

/-- Ceiling in atomic units. Its denominator is positive for every valid tariff. -/
def atomicCeil (credit rate : Nat) : Nat := (credit + rate - 1) / rate

/-- The smallest transfer covering the requested credit and journal floor.
The result is checked against the receiver's actual week/remainder arithmetic,
not an assumption that the requested split survives atomic rounding.

A requested starter of a whole week or more cannot remain spendable in this
single enrollment transfer; such funding needs an ordinary-account top-up.
A quote is descriptive, not a reservation of the tariff or current authority. -/
def quote (tariff : Tariff) (birthFee requestedWeeks minimumStarterCredit : Nat) :
    Except Reject Quote :=
  if !decide tariff.valid then .error .tariffInvalid
  else if requestedWeeks = 0 then .error .weeksZero
  else if tariff.weekCredit ≤ minimumStarterCredit then .error .starterTooLarge
  else
    let target := birthFee + requestedWeeks * tariff.weekCredit + minimumStarterCredit
    let amount := max (atomicCeil target tariff.creditPerAtomic) tariff.journalFloor
    if tariff.maxPerObservation < amount then .error .observationCapExceeded
    else
      let credit := tariff.creditFor amount
      let minimumEntryCredit := birthFee + tariff.weekCredit
      if credit < minimumEntryCredit then .error .entryCreditUncovered
      else
        let actualWeeks := (credit - birthFee) / tariff.weekCredit
        let leaseCredit := actualWeeks * tariff.weekCredit
        let remainder := credit - birthFee - leaseCredit
        if actualWeeks ≠ requestedWeeks then .error .exactWeeksUnrepresentable
        else if remainder < minimumStarterCredit then .error .starterUnrepresentable
        else .ok {
          amountAtomic := amount
          credit := credit
          birthFee := birthFee
          requestedWeeks := requestedWeeks
          actualWeeks := actualWeeks
          leaseCredit := leaseCredit
          creditedRemainder := remainder
          minimumStarterCredit := minimumStarterCredit
          minimumEntryCredit := minimumEntryCredit }

/-- Whenever the fee and membership are covered, these three terms partition
the credit exactly. In particular the starter is not a second mint. -/
theorem credit_decomposition (credit birthFee leaseCredit : Nat)
    (feeCovered : birthFee ≤ credit)
    (leaseCovered : leaseCredit ≤ credit - birthFee) :
    birthFee + leaseCredit + (credit - birthFee - leaseCredit) = credit := by
  omega


/-- A successful quote retains the chosen duration and starter, and its exact
credited amount is partitioned into the birth fee, membership and remainder.
This is a property of the returned quote, not merely of caller-supplied bounds. -/
theorem quote_success_split (tariff : Tariff) (birthFee requestedWeeks starter : Nat)
    (q : Quote) (accepted : quote tariff birthFee requestedWeeks starter = .ok q) :
    q.birthFee + q.leaseCredit + q.creditedRemainder = q.credit ∧
      q.actualWeeks = requestedWeeks ∧ starter ≤ q.creditedRemainder := by
  let amount := max
    (atomicCeil (birthFee + requestedWeeks * tariff.weekCredit + starter)
      tariff.creditPerAtomic) tariff.journalFloor
  let credit := tariff.creditFor amount
  let actualWeeks := (credit - birthFee) / tariff.weekCredit
  unfold quote at accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  rename_i entryCovered
  split at accepted
  · cases accepted
  rename_i exactWeeks
  split at accepted
  · cases accepted
  rename_i starterCovered
  have feeCovered : birthFee ≤ credit := by
    change ¬credit < birthFee + tariff.weekCredit at entryCovered
    omega
  have leaseCovered := Nat.div_mul_le_self (credit - birthFee) tariff.weekCredit
  change actualWeeks * tariff.weekCredit ≤ credit - birthFee at leaseCovered
  have sameWeeks : actualWeeks = requestedWeeks := by
    change ¬actualWeeks ≠ requestedWeeks at exactWeeks
    omega
  have enoughStarter : starter ≤ credit - birthFee - actualWeeks * tariff.weekCredit := by
    change ¬credit - birthFee - actualWeeks * tariff.weekCredit < starter at starterCovered
    omega
  injection accepted with same
  subst q
  change birthFee + actualWeeks * tariff.weekCredit +
      (credit - birthFee - actualWeeks * tariff.weekCredit) = credit ∧
    actualWeeks = requestedWeeks ∧
      starter ≤ credit - birthFee - actualWeeks * tariff.weekCredit
  exact ⟨credit_decomposition credit birthFee (actualWeeks * tariff.weekCredit)
    feeCovered leaseCovered, sameWeeks, enoughStarter⟩

/-- No transfer selected above the cap can be described as a successful quote. -/
theorem quote_with_floor_above_cap (tariff : Tariff)
    (birthFee requestedWeeks minimumStarterCredit : Nat)
    (valid : tariff.valid) (weeks : requestedWeeks ≠ 0)
    (starter : minimumStarterCredit < tariff.weekCredit)
    (floor : tariff.maxPerObservation < tariff.journalFloor) :
    quote tariff birthFee requestedWeeks minimumStarterCredit =
      .error .observationCapExceeded := by
  have above : tariff.maxPerObservation <
      max (atomicCeil
        (birthFee + requestedWeeks * tariff.weekCredit + minimumStarterCredit)
        tariff.creditPerAtomic) tariff.journalFloor :=
    lt_of_lt_of_le floor (Nat.le_max_right _ _)
  simp [quote, valid, weeks, Nat.not_le.mpr starter, above]

/-! Concrete poles use a week of 168 credits, a real nonzero birth fee,
non-unit atomic rates, observation caps and journal floors. -/

private def fixture : Tariff :=
  { exampleTariff with
      version := 3, creditPerAtomic := 1, maxPerObservation := 100000,
      nodeHourRate := 1, enrolIndex := some 0, journalFloor := 1 }

/-- The entry threshold itself leaves no spendable funds. -/
theorem exact_entry_has_zero_remainder :
    quote fixture 7 1 0 =
      .ok ⟨175, 175, 7, 1, 1, 168, 0, 0, 175⟩ := by decide

/-- A starter remains in the account after two explicitly chosen weeks. -/
theorem two_weeks_and_starter :
    quote fixture 7 2 47 =
      .ok ⟨390, 390, 7, 2, 2, 336, 47, 47, 175⟩ := by decide

/-- Atomic rounding may add spendable credit without changing the duration. -/
theorem coarse_atomic_rounding_preserves_split :
    quote { fixture with creditPerAtomic := 10 } 7 1 20 =
      .ok ⟨20, 200, 7, 1, 1, 168, 25, 20, 175⟩ := by decide

/-- Here rounding buys two weeks and leaves only 7 credits, below the
requested 167. The old "entry plus starter" client formula would misquote it. -/
theorem coarse_atomic_rounding_cannot_buy_extra_week :
    quote { fixture with creditPerAtomic := 10 } 7 1 167 =
      .error .exactWeeksUnrepresentable := by decide

/-- Even an extra week with ample remainder is not the chosen duration. -/
theorem coarse_atomic_rounding_cannot_silently_extend :
    quote { fixture with creditPerAtomic := 400 } 7 1 20 =
      .error .exactWeeksUnrepresentable := by decide

theorem insufficient_observation_cap :
    quote { fixture with maxPerObservation := 190 } 7 1 20 =
      .error .observationCapExceeded := by decide

/-- The floor is in atomic units; it can increase the spendable remainder. -/
theorem journal_floor_is_honored :
    quote { fixture with journalFloor := 200 } 7 1 20 =
      .ok ⟨200, 200, 7, 1, 1, 168, 25, 20, 175⟩ := by decide

theorem journal_floor_cannot_buy_extra_week :
    quote { fixture with journalFloor := 400 } 7 1 20 =
      .error .exactWeeksUnrepresentable := by decide

theorem starter_cannot_be_a_whole_week :
    quote fixture 7 1 168 = .error .starterTooLarge := by decide

theorem zero_weeks_refused :
    quote fixture 7 0 20 = .error .weeksZero := by decide

theorem invalid_tariff_refused :
    quote { fixture with creditPerAtomic := 0 } 7 1 20 =
      .error .tariffInvalid := by decide

#assert_axioms credit_decomposition
#assert_axioms quote_success_split
#assert_axioms quote_with_floor_above_cap
#assert_axioms exact_entry_has_zero_remainder
#assert_axioms two_weeks_and_starter
#assert_axioms coarse_atomic_rounding_preserves_split
#assert_axioms coarse_atomic_rounding_cannot_buy_extra_week
#assert_axioms coarse_atomic_rounding_cannot_silently_extend
#assert_axioms insufficient_observation_cap
#assert_axioms journal_floor_is_honored
#assert_axioms journal_floor_cannot_buy_extra_week
#assert_axioms starter_cannot_be_a_whole_week
#assert_axioms zero_weeks_refused
#assert_axioms invalid_tariff_refused

end Minidregg.Kernel.PayEnrolQuote
