/-
# Theory.FiniteTapeGap — distinguishing gaps over finite equally likely tapes

A bounded randomized experiment is a function of one random tape drawn
uniformly from `Fin tapes` (pad unused coins so both worlds use the same tape
space). `GapAtMost tapes num den left right` says the two experiments' success
counts differ by at most `num/den` as a probability, stated by cross
multiplication so no measure theory is needed to read it. An empty experiment
or a zero denominator never satisfies it.

The two lemmas every hybrid argument uses are here: the triangle inequality
(`GapAtMost.trans`) and invariance under a permutation of the tapes
(`count_ofFn_perm`, `GapAtMost.zero_of_perm`), which is how an ideal
one-time-pad hybrid is shown to be identical across worlds.
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Minidregg.Theory.FiniteTapeGap

set_option autoImplicit false

/-- Absolute probability gap at most `num/den` between two experiments on
`tapes` equally likely tapes. -/
def GapAtMost (tapes num den : Nat) (left right : Fin tapes → Bool) : Prop :=
  0 < tapes ∧ 0 < den ∧
    (List.ofFn left).count true * den ≤
      (List.ofFn right).count true * den + num * tapes ∧
    (List.ofFn right).count true * den ≤
      (List.ofFn left).count true * den + num * tapes

theorem GapAtMost.symm {tapes num den : Nat} {left right : Fin tapes → Bool}
    (gap : GapAtMost tapes num den left right) : GapAtMost tapes num den right left :=
  ⟨gap.1, gap.2.1, gap.2.2.2, gap.2.2.1⟩

/-- The triangle inequality: hybrids compose by adding their gaps. -/
theorem GapAtMost.trans {tapes first second den : Nat} {left middle right : Fin tapes → Bool}
    (one : GapAtMost tapes first den left middle)
    (two : GapAtMost tapes second den middle right) :
    GapAtMost tapes (first + second) den left right := by
  obtain ⟨positive, denominator, a, b⟩ := one
  obtain ⟨_, _, c, d⟩ := two
  refine ⟨positive, denominator, ?_, ?_⟩ <;> rw [Nat.add_mul] <;> omega

/-- Rewrite the numerator and denominator by equations. -/
theorem GapAtMost.cast {tapes num num' den den' : Nat} {left right : Fin tapes → Bool}
    (gap : GapAtMost tapes num den left right) (sameNum : num = num') (sameDen : den = den') :
    GapAtMost tapes num' den' left right := by
  subst sameNum
  subst sameDen
  exact gap

/-- A larger budget is still a bound. -/
theorem GapAtMost.mono {tapes small large den : Nat} {left right : Fin tapes → Bool}
    (gap : GapAtMost tapes small den left right) (le : small ≤ large) :
    GapAtMost tapes large den left right := by
  obtain ⟨positive, denominator, a, b⟩ := gap
  have : small * tapes ≤ large * tapes := Nat.mul_le_mul_right _ le
  exact ⟨positive, denominator, by omega, by omega⟩

/-- Rescaling numerator and denominator by the same positive factor keeps the
bound: hybrids with different denominators are put over a common one. -/
theorem GapAtMost.scale {tapes num den : Nat} {left right : Fin tapes → Bool}
    (gap : GapAtMost tapes num den left right) {factor : Nat} (positive : 0 < factor) :
    GapAtMost tapes (num * factor) (den * factor) left right := by
  obtain ⟨tapesPositive, denominator, a, b⟩ := gap
  refine ⟨tapesPositive, Nat.mul_pos denominator positive, ?_, ?_⟩
  · have := Nat.mul_le_mul_right factor a
    rw [Nat.add_mul] at this
    calc _ = (List.ofFn left).count true * den * factor := by rw [Nat.mul_assoc]
      _ ≤ _ := this
      _ = _ := by rw [Nat.mul_assoc, Nat.mul_right_comm num tapes factor]
  · have := Nat.mul_le_mul_right factor b
    rw [Nat.add_mul] at this
    calc _ = (List.ofFn right).count true * den * factor := by rw [Nat.mul_assoc]
      _ ≤ _ := this
      _ = _ := by rw [Nat.mul_assoc, Nat.mul_right_comm num tapes factor]

/-- Equal success counts give a zero gap. -/
theorem GapAtMost.zero_of_count_eq {tapes den : Nat} {left right : Fin tapes → Bool}
    (positive : 0 < tapes) (denominator : 0 < den)
    (same : (List.ofFn left).count true = (List.ofFn right).count true) :
    GapAtMost tapes 0 den left right := by
  refine ⟨positive, denominator, ?_, ?_⟩ <;> rw [same] <;> omega

/-- Relabelling the tapes by a permutation does not change a success count. -/
theorem count_ofFn_perm {tapes : Nat} (experiment : Fin tapes → Bool)
    (relabel : Equiv.Perm (Fin tapes)) :
    (List.ofFn (experiment ∘ relabel)).count true = (List.ofFn experiment).count true :=
  (Equiv.Perm.ofFn_comp_perm relabel experiment).count_eq true

/-- Two worlds that are the same experiment up to a relabelling of the tapes
are identical: gap zero against every test. -/
theorem GapAtMost.zero_of_perm {tapes den : Nat} (positive : 0 < tapes) (denominator : 0 < den)
    (experiment : Fin tapes → Bool) (relabel : Equiv.Perm (Fin tapes)) :
    GapAtMost tapes 0 den (experiment ∘ relabel) experiment :=
  GapAtMost.zero_of_count_eq positive denominator (count_ofFn_perm experiment relabel)

/-- A gap budget below one is refuted by a test that succeeds on every tape in
one world and on no tape in the other. -/
theorem not_gapAtMost_of_separating {tapes num den : Nat} {left right : Fin tapes → Bool}
    (small : num < den) (always : ∀ tape, left tape = true) (never : ∀ tape, right tape = false) :
    ¬ GapAtMost tapes num den left right := by
  rintro ⟨positive, _, bound, _⟩
  have full : (List.ofFn left).count true = tapes := by
    rw [List.count_eq_length.mpr (by simpa [List.mem_ofFn] using fun tape => (always tape).symm)]
    simp
  have empty : (List.ofFn right).count true = 0 := by
    rw [List.count_eq_zero]
    simp [List.mem_ofFn, never]
  rw [full, empty] at bound
  have : num * tapes < den * tapes := Nat.mul_lt_mul_of_pos_right small positive
  rw [Nat.mul_comm tapes den] at bound
  omega

end Minidregg.Theory.FiniteTapeGap
