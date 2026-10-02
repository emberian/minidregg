/-
# The order range a scalar width covers, stated on source values

`inputsInRange` bounds the DIFFERENCE of the two integers an order atom
compares. A friend does not write differences, it writes slot values and
literals. This module turns a bound on every value an instance touches into the
range premise, and a bound on the values into the equality premise
(`castInjOn`) over a prime field, so the compiled law's verdict equals `eval`
for every law whose values lie in the stated band.

The band `[-B, B)` must satisfy `3 * B ≤ 2^width`: `leSlotsOff a b c`
compares `a` with `b + c`, a difference of three values. Nothing here
short-circuits: the range premise is still checked on every order atom,
including children of `not` and `any`, whatever their Boolean outcome.
-/
import Compiler.PredCompile
import Mathlib.Data.ZMod.Basic
import Theory.AssertAxioms

namespace Minidregg.Compiler

open Minidregg.Pred (Pred PredList State Slot)

set_option autoImplicit false

/-- The band `[-B, B)`. -/
def InBand (B x : Int) : Prop := -B ≤ x ∧ x < B

instance (B x : Int) : Decidable (InBand B x) :=
  inferInstanceAs (Decidable (-B ≤ x ∧ x < B))

theorem intOf_inBand {B : Int} (hB : 0 < B) {st : State} (s : Slot)
    (h : ∀ x ∈ stateVals st, InBand B x) : InBand B (intOf st s) := by
  unfold intOf
  cases hs : st.get s with
  | none => simp only [Option.getD_none]; exact ⟨by omega, hB⟩
  | some x => simpa only [Option.getD_some] using h x (get_mem_stateVals hs)

private theorem diff_in_range {w : Nat} {B a b : Int} (hB : 3 * B ≤ (2 : Int) ^ w)
    (ha : InBand B a) (hb : InBand B b) (present : Bool) :
    PredOrder.InputsInRange w present a b := by
  intro _
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  generalize (2 : Int) ^ w = P at *
  constructor <;> omega

private theorem offset_diff_in_range {w : Nat} {B a b c : Int} (hB : 3 * B ≤ (2 : Int) ^ w)
    (ha : InBand B a) (hb : InBand B b) (hc : InBand B c) (present : Bool) :
    PredOrder.InputsInRange w present a (b + c) := by
  intro _
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hc0, hc1⟩ := hc
  generalize (2 : Int) ^ w = P at *
  constructor <;> omega

mutual
/-- Every order atom of `p` is in range when every literal of `p` and every value of
both states lies in the band. -/
theorem inputsInRange_of_inBand {w : Nat} {B : Int} (hB : 3 * B ≤ (2 : Int) ^ w) (hB0 : 0 < B)
    {old new : State} (hold : ∀ x ∈ stateVals old, InBand B x)
    (hnew : ∀ x ∈ stateVals new, InBand B x) :
    (p : Pred) → (∀ x ∈ lits p, InBand B x) →
      inputsInRange (.scalar w) p old new = true
  | .le s v, hl => by
      simp only [inputsInRange, CompilerProfile.scalar, decide_eq_true_eq]
      exact diff_in_range hB (intOf_inBand hB0 s hnew) (hl v (by simp [lits])) _
  | .monotone s, _ => by
      simp only [inputsInRange, CompilerProfile.scalar, decide_eq_true_eq]
      exact diff_in_range hB (intOf_inBand hB0 s hold) (intOf_inBand hB0 s hnew) _
  | .leSlots a b, _ => by
      simp only [inputsInRange, CompilerProfile.scalar, decide_eq_true_eq]
      exact diff_in_range hB (intOf_inBand hB0 a hnew) (intOf_inBand hB0 b hnew) _
  | .leSlotsOff a b c, hl => by
      simp only [inputsInRange, CompilerProfile.scalar, decide_eq_true_eq]
      exact offset_diff_in_range hB (intOf_inBand hB0 a hnew) (intOf_inBand hB0 b hnew)
        (hl c (by simp [lits])) _
  | .not p, hl => by
      simp only [inputsInRange]
      exact inputsInRange_of_inBand hB hB0 hold hnew p (by simpa [lits] using hl)
  | .allL ps, hl => by
      simp only [inputsInRange]
      exact inputsInRangeL_of_inBand hB hB0 hold hnew ps (by simpa [lits] using hl)
  | .anyL ps, hl => by
      simp only [inputsInRange]
      exact inputsInRangeL_of_inBand hB hB0 hold hnew ps (by simpa [lits] using hl)
  | .eq _ _, _ | .memberOf _ _, _ | .writeOnce _, _ | .eqSlots _ _, _
  | .witnessed _, _ | .hashEq _ _ _, _ | .ran _, _ => by simp [inputsInRange]
theorem inputsInRangeL_of_inBand {w : Nat} {B : Int} (hB : 3 * B ≤ (2 : Int) ^ w) (hB0 : 0 < B)
    {old new : State} (hold : ∀ x ∈ stateVals old, InBand B x)
    (hnew : ∀ x ∈ stateVals new, InBand B x) :
    (ps : PredList) → (∀ x ∈ litsL ps, InBand B x) →
      inputsInRangeL (.scalar w) ps old new = true
  | .nil, _ => by simp [inputsInRangeL]
  | .cons p ps, hl => by
      simp only [inputsInRangeL, Bool.and_eq_true]
      exact ⟨inputsInRange_of_inBand hB hB0 hold hnew p
          (fun x hx => hl x (by simp [litsL, hx])),
        inputsInRangeL_of_inBand hB hB0 hold hnew ps
          (fun x hx => hl x (by simp [litsL, hx]))⟩
end

/-- The range premise, from one bound on every integer the instance touches. -/
theorem inputsInRange_of_intsOf_inBand {w : Nat} {B : Int} (hB : 3 * B ≤ (2 : Int) ^ w)
    (hB0 : 0 < B) {p : Pred} {old new : State} (h : ∀ x ∈ intsOf p old new, InBand B x) :
    inputsInRange (.scalar w) p old new = true :=
  inputsInRange_of_inBand hB hB0
    (fun x hx => h x (by simp [intsOf, hx])) (fun x hx => h x (by simp [intsOf, hx])) p
    (fun x hx => h x (by simp [intsOf, hx]))

/-- Over a prime field of characteristic at least `2B`, no two integers of the band
share a field image: the equality premise holds for every list of band values. -/
theorem castInjOn_zmod_of_inBand {q : Nat} [Fact q.Prime] {B : Int} (hB : 2 * B ≤ (q : Int))
    (I : List Int) (h : ∀ x ∈ I, InBand B x) : castInjOn (ZMod q) I := by
  intro a ha b hb same
  have hdvd : (q : Int) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp same
  obtain ⟨ha0, ha1⟩ := h a ha
  obtain ⟨hb0, hb1⟩ := h b hb
  have habs : |b - a| < (q : Int) := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

#assert_axioms inputsInRange_of_intsOf_inBand
#assert_axioms castInjOn_zmod_of_inBand

end Minidregg.Compiler
