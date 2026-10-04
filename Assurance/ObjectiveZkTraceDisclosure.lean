import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum
import Theory.AssertAxioms

/- The one-row raw trace leak and the status of height-256 padding, as statements.

* `one_row_opening_reveals`: a committed column of degree < 2 over the base field K
  (one real row + one hiding row) opened at an extension point ζ with 1, ζ
  K-linearly independent determines BOTH coefficients, hence the real row value
  (`one_row_value_revealed`). In IR2 the single local row is the whole unrolled
  execution (every wire, private state, salt), so every main-trace column leaks.
  `independence_needed`: the hypothesis is refutable (ζ in the base field collides),
  so the theorem is not a tautology; `independence_satisfiable`: and satisfiable.
* `repeated_row_column_constant` / `repeated_row_opening_is_row`: padding by
  REPETITION to a public height H, without masking, makes every column the constant
  polynomial of the row value; every opening is the row value itself. Padding fixes
  the SHAPE as a function of the public envelope; it does not hide content
  (`padded_rows_determine_row`: the padded matrix is injective in the private row).
  Privacy at height 256 rests entirely on the hiding PCS randomness (one random row
  per real row) and the finite-query masking budget; that composition is not proved
  here and is not proved anywhere in the tree for the deployed transcript. -/
namespace Minidregg.Assurance.ObjectiveZkTraceDisclosure
open Polynomial
set_option autoImplicit false

theorem one_row_opening_reveals {K L : Type} [Field K] [Field L] [Algebra K L] {ζ : L}
    (independent : LinearIndependent K ![1, ζ]) {a b a' b' : K}
    (same : algebraMap K L a + algebraMap K L b * ζ = algebraMap K L a' + algebraMap K L b' * ζ) :
    a = a' ∧ b = b' := by
  exact LinearIndependent.pair_iffₛ.mp independent a b a' b' (by simpa [Algebra.smul_def] using same)

/-- The real row value at any domain point `x` is determined by the public opening. -/
theorem one_row_value_revealed {K L : Type} [Field K] [Field L] [Algebra K L] {ζ : L}
    (independent : LinearIndependent K ![1, ζ]) (x : K) {a b a' b' : K}
    (same : algebraMap K L a + algebraMap K L b * ζ = algebraMap K L a' + algebraMap K L b' * ζ) :
    a + b * x = a' + b' * x := by
  obtain ⟨first, second⟩ := one_row_opening_reveals independent same
  rw [first, second]

/-- The premise is satisfiable: ℂ over ℝ at `I`. -/
theorem independence_satisfiable : LinearIndependent ℝ ![(1 : ℂ), Complex.I] := by
  rw [← Complex.coe_basisOneI]
  exact Complex.basisOneI.linearIndependent

/-- The premise is refutable and needed: at a base-field point two different rows
open identically, so nothing is revealed without it. -/
theorem independence_needed :
    ¬ ∀ a b a' b' : ℝ, algebraMap ℝ ℝ a + algebraMap ℝ ℝ b * 1 =
        algebraMap ℝ ℝ a' + algebraMap ℝ ℝ b' * 1 → a = a' ∧ b = b' := by
  intro reveals
  have wrong := reveals 1 0 0 1 (by norm_num)
  norm_num at wrong

/-- Repetition padding without masking: a column of degree < H agreeing with the row
value `c` on H ≥ 1 trace points IS the constant `c`. -/
theorem repeated_row_column_constant {K : Type} [Field K] (domain : Finset K) (column : K[X])
    (c : K) (nonempty : 0 < domain.card) (degree : column.degree < domain.card)
    (repeated : ∀ x ∈ domain, column.eval x = c) : column = C c := by
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq domain
  · calc (column - C c).degree ≤ max column.degree (C c).degree := Polynomial.degree_sub_le _ _
      _ < domain.card := max_lt degree
          (lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast nonempty))
  · intro x member
    rw [repeated x member, Polynomial.eval_C]

theorem repeated_row_opening_is_row {K L : Type} [Field K] [Field L] [Algebra K L]
    (domain : Finset K) (column : K[X]) (c : K) (nonempty : 0 < domain.card)
    (degree : column.degree < domain.card) (repeated : ∀ x ∈ domain, column.eval x = c)
    (ζ : L) : aeval ζ column = algebraMap K L c := by
  rw [repeated_row_column_constant domain column c nonempty degree repeated, aeval_C]

/-- The padded matrix (the row repeated to the public height) determines the row. -/
theorem padded_rows_determine_row {α : Type} (height : Nat) (row row' : α)
    (same : List.replicate (height+1) row = List.replicate (height+1) row') : row = row' := by
  rw [List.replicate_succ, List.replicate_succ] at same
  exact (List.cons.inj same).1

#assert_axioms one_row_opening_reveals
#assert_axioms one_row_value_revealed
#assert_axioms independence_satisfiable
#assert_axioms independence_needed
#assert_axioms repeated_row_column_constant
#assert_axioms repeated_row_opening_is_row
#assert_axioms padded_rows_determine_row
end Minidregg.Assurance.ObjectiveZkTraceDisclosure
