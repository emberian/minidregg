import Theory.ObjectiveBendDemandForcingDemand
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-- Every state after the first `n` transitions fits the limits. -/
def FitsFrom (L : Limits) (s : State) (n : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ n → (exec j s).heap.size ≤ L.heap ∧ (exec j s).stack.length ≤ L.stack

theorem fitsFrom_tail {L : Limits} {s : State} {n : Nat} (h : FitsFrom L s (n + 1)) : FitsFrom L (stepRaw s) n :=
  fun j lo hi => h (j + 1) (by omega) (by omega)

/-- **A bounded run that does not suspend is a halting raw run that fits.** -/
theorem runBounded_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State), (∀ r st, runBounded L ticks s ≠ .suspended r st) →
      ∃ n, n ≤ ticks ∧ Halts s n ∧ FitsFrom L s n ∧ runBounded L ticks s = runBounded L 0 (exec n s) := by
  intro ticks
  induction ticks with
  | zero =>
    intro s ns
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, ?_⟩, fun _ h1 h2 => by omega, rfl⟩
    show active s.control = false
    cases ctl : s.control with
    | evaluate term environment => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | enter address => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | returned value => exact (ns .ticks s (by simp [runBounded, ctl])).elim
    | _ => rfl
  | succ ticks ih =>
    intro s ns
    cases c : active s.control with
    | false =>
      refine ⟨0, Nat.zero_le _, ⟨fun _ h => by omega, c⟩, fun _ h1 h2 => by omega, ?_⟩
      rw [runBounded_succ_inactive c]; rfl
    | true =>
      rw [runBounded_succ_active c] at ns ⊢
      by_cases fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack
      · rw [if_pos fits] at ns ⊢
        obtain ⟨n, le, halts, fit, eq⟩ := ih (stepRaw s) ns
        refine ⟨n + 1, by omega, halts_succ c halts, ?_, eq⟩
        intro j lo hi
        cases j with
        | zero => omega
        | succ j =>
          by_cases j0 : j = 0
          · subst j0; exact fits
          · exact fit j (by omega) (by omega)
      · rw [if_neg fits] at ns; exact absurd rfl (ns .capacity s)

/-- **A halting raw run that fits is the bounded run.** -/
theorem runBounded_of_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State) (n : Nat), Halts s n → n ≤ ticks → FitsFrom L s n →
      runBounded L ticks s = runBounded L 0 (exec n s) := by
  intro ticks
  induction ticks with
  | zero => intro s n halts le _; rw [show n = 0 by omega]; rfl
  | succ ticks ih =>
    intro s n halts le fit
    cases n with
    | zero =>
      have inactive : active s.control = false := halts.2
      rw [runBounded_succ_inactive inactive]; rfl
    | succ n =>
      have act : active s.control = true := halts.1 0 (by omega)
      have fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack :=
        fit 1 (Nat.le_refl _) (by omega)
      rw [runBounded_succ_active act, if_pos fits]
      exact ih (stepRaw s) n (halts_tail halts) (by omega) (fitsFrom_tail fit)

/-- Forcing with the open policy finishes exactly when the raw run halts complete, fitting. -/
theorem forceWith_finished (L : Limits) :
    ∀ (ticks : Nat) (s : State) (v : RuntimeValue) (st : State) (r : Nat),
      forceWith (fun _ => true) L ticks s = (.finished v st, r) →
      ∃ n, n ≤ ticks ∧ Halts s n ∧ FitsFrom L s n ∧ exec n s = st ∧ st.control = .complete v ∧ r = ticks - n := by
  intro ticks
  induction ticks with
  | zero =>
    intro s v st r h
    simp only [forceWith] at h
    cases ctl : s.control <;> simp [runBounded, ctl] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, by simp [exec, ctl, active]⟩, fun _ h1 h2 => by omega, rfl, ctl, rfl⟩
  | succ ticks ih =>
    intro s v st r h
    cases c : active s.control with
    | false =>
      rw [forceWith_succ_inactive c] at h
      cases ctl : s.control <;> simp [active, ctl] at c <;> simp [runBounded, ctl] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨0, Nat.zero_le _, ⟨fun _ h => by omega, by simp [exec, ctl, active]⟩, fun _ h1 h2 => by omega, rfl, ctl, by omega⟩
    | true =>
      rw [forceWith_succ_active c] at h
      simp only [Bool.true_eq_false, if_false] at h
      rw [runBounded_succ_active c] at h
      by_cases fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack
      · rw [if_pos fits] at h
        have h0 : runBounded L 0 (stepRaw s) = runBounded L 0 (stepRaw s) := rfl
        cases ctl1 : active (stepRaw s).control with
        | true =>
          have run1 : runBounded L 0 (stepRaw s) = .suspended .ticks (stepRaw s) := by
            cases ctl : (stepRaw s).control <;> simp [active, ctl] at ctl1 <;> simp [runBounded, ctl]
          rw [run1] at h; simp only [continueForce] at h
          obtain ⟨n, le, halts, fit, eq, ctlV, rEq⟩ := ih (stepRaw s) v st r h
          refine ⟨n + 1, by omega, halts_succ c halts, ?_, eq, ctlV, by omega⟩
          intro j lo hi
          cases j with
          | zero => omega
          | succ j =>
            by_cases j0 : j = 0
            · subst j0; exact fits
            · exact fit j (by omega) (by omega)
        | false =>
          cases ctl : (stepRaw s).control <;> simp [active, ctl] at ctl1 <;>
            simp [runBounded, ctl, continueForce] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          refine ⟨1, by omega, ⟨fun j lt => by rw [show j = 0 by omega]; exact c, by simp [exec_one, ctl, active]⟩,
            fun j lo hi => by rw [show j = 1 by omega]; exact fits, rfl, ctl, by omega⟩
      · rw [if_neg fits] at h; simp [continueForce] at h

theorem forceWith_of_halts (L : Limits) :
    ∀ (ticks : Nat) (s : State) (n : Nat) (v : RuntimeValue), Halts s n → n ≤ ticks → FitsFrom L s n →
      (exec n s).control = .complete v →
      forceWith (fun _ => true) L ticks s = (.finished v (exec n s), ticks - n) := by
  intro ticks
  induction ticks with
  | zero =>
    intro s n v halts le _ ctl
    have : n = 0 := by omega
    subst this
    simp [forceWith, runBounded, exec] at ctl ⊢; simp [ctl]
  | succ ticks ih =>
    intro s n v halts le fit ctl
    cases n with
    | zero =>
      have inactive : active s.control = false := halts.2
      have ctl' : s.control = .complete v := ctl
      rw [forceWith_succ_inactive inactive]
      simp [runBounded, ctl', exec]
    | succ n =>
      have act : active s.control = true := halts.1 0 (by omega)
      have fits : (stepRaw s).heap.size ≤ L.heap ∧ (stepRaw s).stack.length ≤ L.stack :=
        fit 1 (Nat.le_refl _) (by omega)
      rw [forceWith_succ_active act]
      simp only [Bool.true_eq_false, if_false]
      rw [show runBounded L 1 s = runBounded L (0 + 1) s from rfl, runBounded_succ_active act, if_pos fits]
      have tail := halts_tail halts
      cases n with
      | zero =>
        have inact : active (stepRaw s).control = false := tail.2
        have ctl' : (stepRaw s).control = .complete v := ctl
        simp [runBounded, ctl', continueForce, exec]
      | succ n =>
        have act1 : active (stepRaw s).control = true := tail.1 0 (by omega)
        have run1 : runBounded L 0 (stepRaw s) = .suspended .ticks (stepRaw s) := by
          cases c : (stepRaw s).control <;> simp [active, c] at act1 <;> simp [runBounded, c]
        rw [run1]; simp only [continueForce]
        rw [ih (stepRaw s) (n + 1) v tail (by omega) (fitsFrom_tail fit) ctl]
        congr 1
        omega

#assert_axioms fitsFrom_tail runBounded_halts runBounded_of_halts forceWith_finished forceWith_of_halts

end Minidregg.Theory.ObjectiveBendDemandForcing
