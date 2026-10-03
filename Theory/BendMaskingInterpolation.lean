import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theory.AssertAxioms

/- Constructive polynomial masking at arbitrary finite same-field queries.
For the actual BabyBear trace with extension-field OOD queries, a separate
Frobenius-descent argument must show the interpolant has base-field coefficients.
This lemma must not be silently applied across that missing field boundary. -/
namespace Minidregg.Theory.BendMaskingInterpolation
open Polynomial
set_option autoImplicit false

variable {F : Type*} [Field F] [DecidableEq F]

/-- If queries avoid zeros of the trace-domain vanishing polynomial, a mask
with degree below the number of query points can realize
any observation shift. The construction is actual Lagrange interpolation. -/
theorem observation_shift (queries : Finset F) (vanishing left right : F[X])
    (outside : ∀ point ∈ queries, vanishing.eval point ≠ 0) :
    ∃ offset : F[X], offset.degree < queries.card ∧
      ∀ randomness : F[X], ∀ point ∈ queries,
        left.eval point + vanishing.eval point * randomness.eval point =
        right.eval point + vanishing.eval point * (randomness + offset).eval point := by
  let values : F → F := fun point =>
    (left.eval point - right.eval point) / vanishing.eval point
  let offset := Lagrange.interpolate queries id values
  refine ⟨offset, Lagrange.degree_interpolate_lt values Function.injective_id.injOn, ?_⟩
  intro randomness point member
  have atPoint : offset.eval point = values point :=
    Lagrange.eval_interpolate_at_node values Function.injective_id.injOn member
  rw [Polynomial.eval_add, atPoint]
  dsimp [values]
  field_simp [outside point member]
  <;> ring

/-- Uniqueness of a bounded interpolant forces its coefficients to be fixed by
an automorphism whenever its evaluation data is equivariant on a closed query
set. This is the algebraic descent step, before identifying a concrete fixed
field with the backend's coefficient field. -/
theorem map_eq_of_equivariant_evaluations (queries : Finset F)
    (automorphism : F ≃+* F) (polynomial : F[X])
    (small : polynomial.degree < queries.card)
    (closed : ∀ point ∈ queries, automorphism.symm point ∈ queries)
    (equivariant : ∀ point ∈ queries,
      polynomial.eval (automorphism point) = automorphism (polynomial.eval point)) :
    polynomial.map automorphism.toRingHom = polynomial := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq queries
    Function.injective_id.injOn
  · rw [Polynomial.degree_map_eq_of_injective (f := automorphism.toRingHom) automorphism.injective]
    exact small
  · exact small
  · intro point member
    have mapped := Polynomial.eval_map_apply (p := polynomial) automorphism.toRingHom
      (automorphism.symm point)
    have value := equivariant (automorphism.symm point) (closed point member)
    simpa using mapped.trans value.symm

/-- Interpolation of automorphism-equivariant values produces fixed coefficients.
For Frobenius this supplies descent only after a separate concrete theorem
identifies its fixed coefficients with the base field. -/
theorem interpolate_coeff_fixed (queries : Finset F) (automorphism : F ≃+* F)
    (values : F → F)
    (closed : ∀ point ∈ queries, automorphism point ∈ queries)
    (closedInverse : ∀ point ∈ queries, automorphism.symm point ∈ queries)
    (equivariant : ∀ point ∈ queries, values (automorphism point) = automorphism (values point))
    (index : Nat) :
    automorphism ((Lagrange.interpolate queries id values).coeff index) =
      (Lagrange.interpolate queries id values).coeff index := by
  have fixed := map_eq_of_equivariant_evaluations queries automorphism
    (Lagrange.interpolate queries id values)
    (Lagrange.degree_interpolate_lt values Function.injective_id.injOn) closedInverse
    (by
      intro point member
      have atPoint : (Lagrange.interpolate queries id values).eval point = values point := by
        simpa using Lagrange.eval_interpolate_at_node values Function.injective_id.injOn member
      have atImage : (Lagrange.interpolate queries id values).eval (automorphism point) =
          values (automorphism point) := by
        simpa using Lagrange.eval_interpolate_at_node values Function.injective_id.injOn (closed point member)
      rw [atPoint, atImage]
      exact equivariant point member)
  simpa only [Polynomial.coeff_map] using congrArg (fun p : F[X] => p.coeff index) fixed

/-- A coefficient-fixed polynomial has equivariant evaluations. -/
theorem eval_equivariant_of_map_eq (automorphism : F ≃+* F)
    (polynomial : F[X]) (fixed : polynomial.map automorphism.toRingHom = polynomial)
    (point : F) :
    polynomial.eval (automorphism point) = automorphism (polynomial.eval point) := by
  simpa only [fixed] using
    (Polynomial.eval_map_apply (p := polynomial) automorphism.toRingHom point)

/-- Constructive observation coupling with an offset whose coefficients lie in
an automorphism's fixed field. This is the needed descent shape for a Frobenius-
closed set of extension queries; the concrete BabyBear/Frobenius identification
and the query set/cardinality bound remain separate backend obligations. -/
theorem observation_shift_fixed (queries : Finset F) (automorphism : F ≃+* F)
    (vanishing left right : F[X])
    (outside : ∀ point ∈ queries, vanishing.eval point ≠ 0)
    (closed : ∀ point ∈ queries, automorphism point ∈ queries)
    (closedInverse : ∀ point ∈ queries, automorphism.symm point ∈ queries)
    (fixedVanishing : vanishing.map automorphism.toRingHom = vanishing)
    (fixedLeft : left.map automorphism.toRingHom = left)
    (fixedRight : right.map automorphism.toRingHom = right) :
    ∃ offset : F[X], offset.degree < queries.card ∧
      (∀ index, automorphism (offset.coeff index) = offset.coeff index) ∧
      ∀ randomness : F[X], ∀ point ∈ queries,
        left.eval point + vanishing.eval point * randomness.eval point =
        right.eval point + vanishing.eval point * (randomness + offset).eval point := by
  let values : F → F := fun point =>
    (left.eval point - right.eval point) / vanishing.eval point
  let offset := Lagrange.interpolate queries id values
  have equivariant : ∀ point ∈ queries,
      values (automorphism point) = automorphism (values point) := by
    intro point _
    dsimp [values]
    rw [eval_equivariant_of_map_eq automorphism left fixedLeft,
      eval_equivariant_of_map_eq automorphism right fixedRight,
      eval_equivariant_of_map_eq automorphism vanishing fixedVanishing,
      _root_.map_div₀ automorphism, _root_.map_sub automorphism]
  refine ⟨offset, Lagrange.degree_interpolate_lt values Function.injective_id.injOn,
    fun index => interpolate_coeff_fixed queries automorphism values closed closedInverse
      equivariant index, ?_⟩
  intro randomness point member
  have atPoint : offset.eval point = values point :=
    Lagrange.eval_interpolate_at_node values Function.injective_id.injOn member
  rw [Polynomial.eval_add, atPoint]
  dsimp [values]
  field_simp [outside point member]
  <;> ring

#assert_axioms observation_shift
#assert_axioms map_eq_of_equivariant_evaluations
#assert_axioms interpolate_coeff_fixed
#assert_axioms eval_equivariant_of_map_eq
#assert_axioms observation_shift_fixed
end Minidregg.Theory.BendMaskingInterpolation
