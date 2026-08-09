/-
# Compiler.GateTraceRelationExt6 -- the complete padded-trace eta relation

The runtime opens one padded trace table against an eta aggregation ordered as

1. seven factored-gate terminal affine claims;
2. every public-prefix coordinate equality;
3. every advertised padding-zero equality.

This file instantiates `GateFactoredExt6`'s generic aggregation algebra for
that exact order and proves the resulting bad-eta count.  It also proves the
base-subfield sampling fact used below the executable trace check.  No theorem
here turns sampled oracle answers into a codeword: `SamplesRepresentPolynomial`
is the explicit premise that the separate proximity layer must provide.
-/

import Compiler.GateFactoredExt6

namespace Minidregg.Compiler

open scoped BigOperators
open Minidregg.Loom Polynomial

namespace GateTraceRelationExt6

open GateFactoredExt6

/-! ## 1. Exact runtime ordering of the padded-trace relation -/

variable {nPublic nPadding : Nat}

/-- Claimed affine values in runtime eta order.  Padding claims have value
zero; public-prefix claims carry the public statement value. -/
noncomputable def extendedValues (terminal : Fin 7 -> Ext6Q)
    (publicValues : Fin nPublic -> Ext6Q) : Fin (7 + nPublic + nPadding) -> Ext6Q :=
  Fin.append (Fin.append terminal publicValues) (fun _ => 0)

/-- Public constants in the same order.  Only the seven selector forms can
have nonzero constants. -/
noncomputable def extendedConstants (terminal : Fin 7 -> TraceAffineFunctional) :
    Fin (7 + nPublic + nPadding) -> Ext6Q :=
  Fin.append (Fin.append (fun j => (terminal j).constant) (fun _ => 0)) (fun _ => 0)

/-- Public finite-support weights in runtime eta order.  Public cells select
trace coordinate `j`; padding cells select coordinate `traceLength+j`. -/
noncomputable def extendedWeights (terminal : Fin 7 -> TraceAffineFunctional)
    (traceLength : Nat) : Fin (7 + nPublic + nPadding) -> Nat →₀ Ext6Q :=
  Fin.append
    (Fin.append (fun j => (terminal j).weights)
      (fun j => Finsupp.single j.val 1))
    (fun j => Finsupp.single (traceLength + j.val) 1)

/-- **Complete padded-trace aggregation identity.**  The seven terminal
equalities, all public-prefix equalities, and all padding-zero equalities fold
to one dot product against the same padded trace. -/
theorem extended_eta_identity (eta : Ext6Q) (trace : Nat -> Ext6Q)
    (traceLength : Nat) (terminalValues : Fin 7 -> Ext6Q)
    (terminal : Fin 7 -> TraceAffineFunctional) (publicValues : Fin nPublic -> Ext6Q)
    (hterminal : ∀ j, terminalValues j = (terminal j).eval trace)
    (hpublic : ∀ j : Fin nPublic, trace j.val = publicValues j)
    (hpadding : ∀ j : Fin nPadding, trace (traceLength + j.val) = 0) :
    (∑ j : Fin (7 + nPublic + nPadding), eta ^ j.val *
      (extendedValues (nPadding := nPadding) terminalValues publicValues j -
        extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j)) =
      Finsupp.linearCombination Ext6Q trace
        (etaBatchedWeights (t := 7 + nPublic + nPadding) eta
          (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength)) := by
  apply etaBatched_opening_identity
  intro j
  refine Fin.addCases (m := 7 + nPublic) (n := nPadding) ?_ ?_ j
  · intro q
    refine Fin.addCases (m := 7) (n := nPublic) ?_ ?_ q
    · intro k
      simpa [extendedValues, extendedConstants, extendedWeights,
        TraceAffineFunctional.eval] using hterminal k
    · intro k
      have hk := (hpublic k).symm
      simpa [extendedValues, extendedConstants, extendedWeights,
        Finsupp.linearCombination_single, smul_eq_mul] using hk
  · intro k
    have hk := (hpadding k).symm
    simpa [extendedValues, extendedConstants, extendedWeights,
      Finsupp.linearCombination_single, smul_eq_mul] using hk

/-- One of the complete ordered affine equalities is false exactly when its
`openingDefect` is nonzero. -/
theorem exists_extended_defect_of_false (trace : Nat -> Ext6Q) (traceLength : Nat)
    (terminalValues : Fin 7 -> Ext6Q) (terminal : Fin 7 -> TraceAffineFunctional)
    (publicValues : Fin nPublic -> Ext6Q)
    (hfalse : ∃ j : Fin (7 + nPublic + nPadding),
      extendedValues (nPadding := nPadding) terminalValues publicValues j ≠
        extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j +
          Finsupp.linearCombination Ext6Q trace
            (extendedWeights (nPublic := nPublic) (nPadding := nPadding)
              terminal traceLength j)) :
    ∃ j : Fin (7 + nPublic + nPadding), openingDefect trace
      (extendedValues (nPadding := nPadding) terminalValues publicValues)
      (extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal)
      (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength) j ≠ 0 := by
  obtain ⟨j, hj⟩ := hfalse
  refine ⟨j, ?_⟩
  intro hzero
  apply hj
  unfold openingDefect at hzero
  have heq : extendedValues (nPadding := nPadding) terminalValues publicValues j -
      extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j =
      Finsupp.linearCombination Ext6Q trace
        (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength j) :=
    sub_eq_zero.mp hzero
  calc
    extendedValues (nPadding := nPadding) terminalValues publicValues j =
        (extendedValues (nPadding := nPadding) terminalValues publicValues j -
          extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j) +
          extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j := by ring
    _ = Finsupp.linearCombination Ext6Q trace
          (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength j) +
          extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j := by rw [heq]
    _ = _ := by ring

/-- **Complete relation bad-eta count.**  A false relation among the seven
terminal claims, `nPublic` prefix claims, and `nPadding` zero claims survives
at no more than `6+nPublic+nPadding` challenges. -/
theorem card_bad_extended_eta_le (challenges : Finset Ext6Q)
    (trace : Nat -> Ext6Q) (traceLength : Nat)
    (terminalValues : Fin 7 -> Ext6Q) (terminal : Fin 7 -> TraceAffineFunctional)
    (publicValues : Fin nPublic -> Ext6Q)
    (hfalse : ∃ j : Fin (7 + nPublic + nPadding),
      extendedValues (nPadding := nPadding) terminalValues publicValues j ≠
        extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal j +
          Finsupp.linearCombination Ext6Q trace
            (extendedWeights (nPublic := nPublic) (nPadding := nPadding)
              terminal traceLength j)) :
    (challenges.filter fun eta : Ext6Q =>
      (∑ j : Fin (7 + nPublic + nPadding), eta ^ j.val *
        openingDefect trace (extendedValues (nPadding := nPadding) terminalValues publicValues)
          (extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal)
          (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength) j) = 0).card ≤
      6 + nPublic + nPadding := by
  have h := card_bad_eta_le challenges trace
    (extendedValues (nPadding := nPadding) terminalValues publicValues)
    (extendedConstants (nPublic := nPublic) (nPadding := nPadding) terminal)
    (extendedWeights (nPublic := nPublic) (nPadding := nPadding) terminal traceLength)
    (exists_extended_defect_of_false trace traceLength terminalValues terminal publicValues hfalse)
  omega

/-! ## 2. Base-subfield sampling through a non-base coefficient projection -/

/-- Coefficientwise application of one BabyBear-linear Ext6 coordinate.  For a
non-base basis coordinate, `project (algebraMap a) = 0`. -/
noncomputable def coordinatePolynomial
    (project : Ext6Q →ₗ[BabyBear] BabyBear) (p : Polynomial Ext6Q) :
    Polynomial BabyBear :=
  p.sum fun n c => C (project c) * X ^ n

@[simp] theorem coordinatePolynomial_coeff
    (project : Ext6Q →ₗ[BabyBear] BabyBear) (p : Polynomial Ext6Q) (n : Nat) :
    (coordinatePolynomial project p).coeff n = project (p.coeff n) := by
  classical
  rw [coordinatePolynomial, coeff_sum]
  by_cases hn : n ∈ p.support
  · rw [sum_def, Finset.sum_eq_single n]
    · simp
    · intro a ha hane
      simp [Ne.symm hane]
    · intro hnot
      exact (hnot hn).elim
  · have hc : p.coeff n = 0 := notMem_support_iff.mp hn
    rw [hc, map_zero]
    rw [sum_def]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : n ≠ a := fun h => hn (h ▸ ha)
    simp [hne]

/-- Coordinate projection cannot increase polynomial degree. -/
theorem coordinatePolynomial_degree_le
    (project : Ext6Q →ₗ[BabyBear] BabyBear) (p : Polynomial Ext6Q) :
    (coordinatePolynomial project p).degree ≤ p.degree := by
  apply degree_mono
  intro n hn
  rw [mem_support_iff, coordinatePolynomial_coeff] at hn
  rw [mem_support_iff]
  intro hp
  rw [hp, map_zero] at hn
  exact hn rfl

/-- **Missing-coefficient projection linearity, closed.**  Evaluating an Ext6
polynomial at an embedded BabyBear point and then taking a base-linear
coordinate equals evaluating the coefficientwise coordinate polynomial. -/
theorem coordinatePolynomial_eval
    (project : Ext6Q →ₗ[BabyBear] BabyBear) (p : Polynomial Ext6Q) (x : BabyBear) :
    (coordinatePolynomial project p).eval x =
      project (p.eval (algebraMap BabyBear Ext6Q x)) := by
  rw [coordinatePolynomial, sum_def, eval_finsetSum, eval_eq_sum, sum_def]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  symm
  calc
    project (p.coeff n * (algebraMap BabyBear Ext6Q x) ^ n) =
        project (algebraMap BabyBear Ext6Q (x ^ n) * p.coeff n) := by
          rw [map_pow, mul_comm]
    _ = project ((x ^ n) • p.coeff n) := by rw [Algebra.smul_def]
    _ = (x ^ n) • project (p.coeff n) := project.map_smul _ _
    _ = project (p.coeff n) * x ^ n := by simp [smul_eq_mul, mul_comm]

/-- The exact relation the separate sampled proximity argument must establish.
It is intentionally only a relation on the sampled points, not a claim that an
arbitrary committed oracle is a low-degree codeword. -/
def SamplesRepresentPolynomial (oracle : BabyBear -> Ext6Q)
    (p : Polynomial Ext6Q) (samples : Finset BabyBear) : Prop :=
  ∀ x ∈ samples, oracle x = p.eval (algebraMap BabyBear Ext6Q x)

/-- **Base-subfield sampling bound.**  Let `project` be any non-base Ext6
coordinate (it kills the BabyBear image).  If that coordinate polynomial is
nonzero and the original degree is `< d`, at most `d-1` points of any base
evaluation domain can evaluate back into the BabyBear image. -/
theorem card_eval_in_baseImage_le (domain : Finset BabyBear) (d : Nat)
    (project : Ext6Q →ₗ[BabyBear] BabyBear) (p : Polynomial Ext6Q)
    (hkillsBase : ∀ a : BabyBear, project (algebraMap BabyBear Ext6Q a) = 0)
    (hcoord : coordinatePolynomial project p ≠ 0) (hdegree : p.degree < d) :
    (domain.filter fun x => ∃ a : BabyBear,
      p.eval (algebraMap BabyBear Ext6Q x) = algebraMap BabyBear Ext6Q a).card ≤ d - 1 := by
  classical
  let q := coordinatePolynomial project p
  have hqdegree : q.degree < d :=
    lt_of_le_of_lt (coordinatePolynomial_degree_le project p) hdegree
  have hqnat : q.natDegree < d :=
    (Polynomial.natDegree_lt_iff_degree_lt hcoord).mpr hqdegree
  have hsub : (domain.filter fun x => ∃ a : BabyBear,
      p.eval (algebraMap BabyBear Ext6Q x) = algebraMap BabyBear Ext6Q a).val ⊆ q.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    obtain ⟨a, ha⟩ := hx.2
    rw [Polynomial.mem_roots hcoord]
    unfold Polynomial.IsRoot
    change (coordinatePolynomial project p).eval x = 0
    rw [coordinatePolynomial_eval, ha, hkillsBase]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simp at hqnat
  omega

/-- The executable sampled check may consume the count only after its separate
proximity argument supplies `SamplesRepresentPolynomial`.  This theorem does
the exact transfer from polynomial evaluations to the observed oracle and no
more. -/
theorem card_sampledOracle_in_baseImage_le (samples : Finset BabyBear) (d : Nat)
    (oracle : BabyBear -> Ext6Q) (p : Polynomial Ext6Q)
    (project : Ext6Q →ₗ[BabyBear] BabyBear)
    (hsamples : SamplesRepresentPolynomial oracle p samples)
    (hkillsBase : ∀ a : BabyBear, project (algebraMap BabyBear Ext6Q a) = 0)
    (hcoord : coordinatePolynomial project p ≠ 0) (hdegree : p.degree < d) :
    (samples.filter fun x => ∃ a : BabyBear,
      oracle x = algebraMap BabyBear Ext6Q a).card ≤ d - 1 := by
  classical
  have hsub : (samples.filter fun x => ∃ a : BabyBear,
      oracle x = algebraMap BabyBear Ext6Q a) ⊆
      samples.filter fun x => ∃ a : BabyBear,
        p.eval (algebraMap BabyBear Ext6Q x) = algebraMap BabyBear Ext6Q a := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨a, ha⟩ := hx.2
    exact ⟨hx.1, a, by rw [← hsamples x hx.1, ha]⟩
  exact (Finset.card_le_card hsub).trans
    (card_eval_in_baseImage_le samples d project p hkillsBase hcoord hdegree)

#check @extended_eta_identity
#check @card_bad_extended_eta_le
#check @coordinatePolynomial_eval
#check @card_eval_in_baseImage_le
#check @card_sampledOracle_in_baseImage_le

#print axioms card_bad_extended_eta_le
#print axioms card_eval_in_baseImage_le

end GateTraceRelationExt6
end Minidregg.Compiler
