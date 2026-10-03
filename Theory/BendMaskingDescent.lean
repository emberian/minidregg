import Theory.BendMaskingInterpolation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Lifts

/- Prime-field descent for masking offsets. Unlike same-extension-field
interpolation, this constructs actual base-field polynomial coefficients.
The native BabyBear/quartic representation, closed query enumeration and
adaptive full-transcript distribution remain separate correspondence work. -/
namespace Minidregg.Theory.BendMaskingDescent
set_option autoImplicit false
open Polynomial
variable {E : Type*} [Field E] (p : Nat) [Fact p.Prime] [CharP E p]

/-- Frobenius-fixed coefficients really lift from the prime field, with no
increase in degree. This holds even when E is not a finite field. -/
theorem prime_descent (polynomial : E[X])
    (fixed : ∀ n, polynomial.coeff n ^ p = polynomial.coeff n) :
    ∃ base : (ZMod p)[X], base.map (ZMod.castHom (m := p) dvd_rfl E) = polynomial ∧
      base.degree = polynomial.degree := by
  apply Polynomial.exists_degree_eq_of_mem_lifts
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have member := (Subfield.mem_bot_iff_pow_eq_self E p).mpr (fixed n)
  rw [← ZMod.fieldRange_castHom_eq_bot p] at member
  exact member

/-- The interpolation coupling can use an actual prime-field offset when the
query/data symmetry is the p-power automorphism. No extension-valued randomness
is substituted for the backend's base-field random polynomial. -/
theorem observation_shift_base [DecidableEq E] (queries : Finset E)
    (automorphism : E ≃+* E) (power : ∀ x, automorphism x = x ^ p)
    (vanishing left right : E[X])
    (outside : ∀ point ∈ queries, vanishing.eval point ≠ 0)
    (closed : ∀ point ∈ queries, automorphism point ∈ queries)
    (closedInverse : ∀ point ∈ queries, automorphism.symm point ∈ queries)
    (fixedVanishing : vanishing.map automorphism.toRingHom = vanishing)
    (fixedLeft : left.map automorphism.toRingHom = left)
    (fixedRight : right.map automorphism.toRingHom = right) :
    ∃ offset : (ZMod p)[X], offset.degree < queries.card ∧
      ∀ randomness : (ZMod p)[X], ∀ point ∈ queries,
        left.eval point + vanishing.eval point *
          (randomness.map (ZMod.castHom (m := p) dvd_rfl E)).eval point =
        right.eval point + vanishing.eval point *
          ((randomness + offset).map (ZMod.castHom (m := p) dvd_rfl E)).eval point := by
  obtain ⟨offset, small, fixed, coupling⟩ :=
    BendMaskingInterpolation.observation_shift_fixed queries automorphism vanishing left right
      outside closed closedInverse fixedVanishing fixedLeft fixedRight
  obtain ⟨base, mapped, degree⟩ := prime_descent p offset (by simpa only [power] using fixed)
  refine ⟨base, degree.trans_lt small, ?_⟩
  intro randomness point member
  simpa only [Polynomial.map_add, mapped] using
    coupling (randomness.map (ZMod.castHom (m := p) dvd_rfl E)) point member

/-- Translation acts on the real bounded coefficient space itself. The inverse
uses subtraction and stays within the same public degree bound. This is the
finite uniform-mask coupling boundary, not an adaptive transcript theorem. -/
noncomputable def boundedTranslation (bound : Nat) (offset : (ZMod p)[X])
    (small : offset.degree < bound) :
    {mask : (ZMod p)[X] // mask.degree < bound} ≃
      {mask : (ZMod p)[X] // mask.degree < bound} where
  toFun mask := ⟨mask.val + offset,
    (Polynomial.degree_add_le _ _).trans_lt (max_lt mask.property small)⟩
  invFun mask := ⟨mask.val - offset,
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt mask.property small)⟩
  left_inv := by intro mask; apply Subtype.ext; simp
  right_inv := by intro mask; apply Subtype.ext; simp

#assert_axioms prime_descent
#assert_axioms observation_shift_base
end Minidregg.Theory.BendMaskingDescent
