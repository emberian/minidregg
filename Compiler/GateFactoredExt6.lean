/-
# Compiler.GateFactoredExt6 -- succinct factored provenance for emitted gates

The materialized residual table is useful as a reference, but it is not the
oracle the succinct prover should commit.  This module derives the gate claim
from seven sparse operand tables over one disjoint padded cube:

* multiplication: `A_gamma`, `B`, `C_gamma`;
* addition: `A_gamma`, `B_gamma`, `C_gamma`;
* root pins: `Z_gamma`.

At Boolean corners their factored expression has exactly the gamma-batched
serialized descriptor residual as its cube sum.  Off the cube it is a
degree-at-most-two polynomial handled by `AirSumcheckQuadratic`.  Its terminal
is reduced to seven public finite-support affine functionals of the trace; a
generic commitment layer need authenticate only their linear parts.
-/

import Compiler.GateMleExt6
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace Minidregg.Compiler

open scoped BigOperators
open Minidregg.Assurance Minidregg.Loom Polynomial

namespace GateFactoredExt6

variable {m : Nat}

/-! ## 1. One disjoint padded domain and generic sparse tables -/

/-- Gate positions are the first `|gates|` positions of the canonical residual
ordering from `GateMleExt6`. -/
def gatePosition (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (k : Fin d.gates.length) :
    Fin (GateMleExt6.descriptorResiduals d wv).length :=
  ⟨k, by simpa using Nat.lt_add_right d.zeros.length k.isLt⟩

/-- Root-pin positions follow every gate, exactly as in the canonical residual
ordering. -/
def zeroPosition (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (j : Fin d.zeros.length) :
    Fin (GateMleExt6.descriptorResiduals d wv).length :=
  ⟨d.gates.length + j, by simp⟩

@[simp] theorem gatePosition_val (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear) (k : Fin d.gates.length) :
    (gatePosition d wv k).val = k.val := rfl

@[simp] theorem zeroPosition_val (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear) (j : Fin d.zeros.length) :
    (zeroPosition d wv j).val = d.gates.length + j.val := rfl

/-- Restriction of the shared residual encoding to gate positions. -/
def gateEncoding (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    Fin d.gates.length ↪ (Fin m -> Bool) :=
  ({ toFun := gatePosition d wv
     inj' := fun _ _ h => Fin.ext (by
       simpa using congrArg
         (fun q : Fin (GateMleExt6.descriptorResiduals d wv).length => q.val) h) } :
    Fin d.gates.length ↪ Fin (GateMleExt6.descriptorResiduals d wv).length).trans enc

/-- Restriction of the shared residual encoding to root-pin positions. -/
def zeroEncoding (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    Fin d.zeros.length ↪ (Fin m -> Bool) :=
  ({ toFun := zeroPosition d wv
     inj' := fun _ _ h => Fin.ext (by
       have hv := congrArg
         (fun q : Fin (GateMleExt6.descriptorResiduals d wv).length => q.val) h
       exact Nat.add_left_cancel hv) } :
    Fin d.zeros.length ↪ Fin (GateMleExt6.descriptorResiduals d wv).length).trans enc

/-- A value list injected into a cube, with zero padding. -/
noncomputable def sparseTable {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (val : Fin t -> Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  fun b => ∑ k, if enc k = b then val k else 0

theorem sparseTable_read {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (val : Fin t -> Ext6Q) (k : Fin t) :
    sparseTable enc val (enc k) = val k :=
  sum_ite_enc enc val k

/-- Summing a sparse padded table recovers the sum of its payloads. -/
theorem sum_sparseTable {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (val : Fin t -> Ext6Q) :
    ∑ b, sparseTable enc val b = ∑ k, val k := by
  classical
  unfold sparseTable
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_eq_single (enc k)]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- Products of two tables with the same injective support have no cross
terms.  This is the algebraic use of disjoint padding. -/
theorem sparseTable_mul {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (a b : Fin t -> Ext6Q) (x : Fin m -> Bool) :
    sparseTable enc a x * sparseTable enc b x =
      sparseTable enc (fun k => a k * b k) x := by
  classical
  unfold sparseTable
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : enc i = x
  · simp only [hi, if_pos]
    rw [Fintype.sum_eq_single i]
    · simp [hi]
    · intro j hji
      have hne : enc j ≠ x := by
        intro hj
        exact hji (enc.injective (hj.trans hi.symm))
      simp [hne]
  · simp [hi]

theorem sum_sparseTable_mul {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (a b : Fin t -> Ext6Q) :
    ∑ x, sparseTable enc a x * sparseTable enc b x = ∑ k, a k * b k := by
  simp_rw [sparseTable_mul enc a b]
  exact sum_sparseTable enc _

/-! ## 2. Seven descriptor-derived tables -/

/-- Sparse operand tables are built over Ext6 directly, but every payload is
the exact algebraic embedding of a serialized `DWire.read`. -/
noncomputable def operandTable {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (scale : Fin t -> Ext6Q) (operand : Fin t -> DWire BabyBear)
    (wv : Nat -> BabyBear) : (Fin m -> Bool) -> Ext6Q :=
  sparseTable enc fun k =>
    scale k * algebraMap BabyBear Ext6Q ((operand k).read wv)

noncomputable def gateOpScale (d : ConstraintDescriptor BabyBear) (wanted : GateOp)
    (weight : Fin d.gates.length -> Ext6Q) (k : Fin d.gates.length) : Ext6Q :=
  if (d.gates.get k).op = wanted then weight k else 0

noncomputable def mulAGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .mul fun k => gamma ^ k.val) (fun k => (d.gates.get k).a) wv

noncomputable def mulB (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .mul fun _ => 1) (fun k => (d.gates.get k).b) wv

noncomputable def mulCGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .mul fun k => gamma ^ k.val)
    (fun k => DWire.wire (d.gates.get k).out) wv

noncomputable def addAGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .add fun k => gamma ^ k.val) (fun k => (d.gates.get k).a) wv

noncomputable def addBGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .add fun k => gamma ^ k.val) (fun k => (d.gates.get k).b) wv

noncomputable def addCGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (gateEncoding d wv enc)
    (gateOpScale d .add fun k => gamma ^ k.val)
    (fun k => DWire.wire (d.gates.get k).out) wv

noncomputable def zeroGamma (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  operandTable (zeroEncoding d wv enc)
    (fun j => gamma ^ (d.gates.length + j.val)) (fun j => d.zeros.get j) wv

/-- The linear channels are absorbed into one `C` table, so the existing
quadratic engine applies without modification. -/
noncomputable def combinedC (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  mulCGamma d wv enc gamma - addAGamma d wv enc gamma - addBGamma d wv enc gamma +
    addCGamma d wv enc gamma - zeroGamma d wv enc gamma

/-- The succinct gate polynomial. -/
noncomputable def factoredGatePolynomial (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Ext6Q) -> Ext6Q :=
  prodDiff (mulAGamma d wv enc gamma) (mulB d wv enc) (combinedC d wv enc gamma)

/-! ## 3. Exact gamma-batched descriptor provenance -/

/-- The descriptor claim, without a materialized defect oracle: gate residuals
retain their gate-list exponents and root pins follow them. -/
noncomputable def gammaBatchedDescriptorResidual (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear) (gamma : Ext6Q) : Ext6Q :=
  (∑ k : Fin d.gates.length,
      gamma ^ k.val * algebraMap BabyBear Ext6Q
        (GateMleExt6.gateResidual wv (d.gates.get k))) +
    ∑ j : Fin d.zeros.length,
      gamma ^ (d.gates.length + j.val) *
        algebraMap BabyBear Ext6Q ((d.zeros.get j).read wv)

/-- The factored polynomial is exactly the requested seven-opening expression. -/
theorem factoredGatePolynomial_expanded (d : ConstraintDescriptor BabyBear)
    (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (x : Fin m -> Ext6Q) :
    factoredGatePolynomial d wv enc gamma x =
      mle (mulAGamma d wv enc gamma) x * mle (mulB d wv enc) x -
        mle (mulCGamma d wv enc gamma) x +
      mle (addAGamma d wv enc gamma) x + mle (addBGamma d wv enc gamma) x -
        mle (addCGamma d wv enc gamma) x + mle (zeroGamma d wv enc gamma) x := by
  simp only [factoredGatePolynomial, prodDiff, combinedC, mle]
  simp only [Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Summing the factored expression on Boolean corners is exactly the
gamma-batched residual of the serialized descriptor. -/
theorem factored_cube_sum_eq_gammaBatchedDescriptorResidual
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) :
    (∑ b, factoredGatePolynomial d wv enc gamma (cubePt b)) =
      gammaBatchedDescriptorResidual d wv gamma := by
  classical
  rw [show (∑ b, factoredGatePolynomial d wv enc gamma (cubePt b)) =
      (∑ b, mulAGamma d wv enc gamma b * mulB d wv enc b) -
        (∑ b, mulCGamma d wv enc gamma b) +
        (∑ b, addAGamma d wv enc gamma b) +
        (∑ b, addBGamma d wv enc gamma b) -
        (∑ b, addCGamma d wv enc gamma b) +
        (∑ b, zeroGamma d wv enc gamma b) by
    simp_rw [factoredGatePolynomial_expanded, mle_agrees]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  rw [show (∑ b, mulAGamma d wv enc gamma b * mulB d wv enc b) =
      ∑ k : Fin d.gates.length,
        (gateOpScale d .mul fun k => gamma ^ k.val) k *
            algebraMap BabyBear Ext6Q ((d.gates.get k).a.read wv) *
          ((gateOpScale d .mul fun _ => 1) k *
            algebraMap BabyBear Ext6Q ((d.gates.get k).b.read wv)) by
    exact sum_sparseTable_mul (gateEncoding d wv enc) _ _]
  rw [show (∑ b, mulCGamma d wv enc gamma b) =
      ∑ k : Fin d.gates.length,
        (gateOpScale d .mul fun k => gamma ^ k.val) k *
          algebraMap BabyBear Ext6Q (wv (d.gates.get k).out) by
    exact sum_sparseTable (gateEncoding d wv enc) _]
  rw [show (∑ b, addAGamma d wv enc gamma b) =
      ∑ k : Fin d.gates.length,
        (gateOpScale d .add fun k => gamma ^ k.val) k *
          algebraMap BabyBear Ext6Q ((d.gates.get k).a.read wv) by
    exact sum_sparseTable (gateEncoding d wv enc) _]
  rw [show (∑ b, addBGamma d wv enc gamma b) =
      ∑ k : Fin d.gates.length,
        (gateOpScale d .add fun k => gamma ^ k.val) k *
          algebraMap BabyBear Ext6Q ((d.gates.get k).b.read wv) by
    exact sum_sparseTable (gateEncoding d wv enc) _]
  rw [show (∑ b, addCGamma d wv enc gamma b) =
      ∑ k : Fin d.gates.length,
        (gateOpScale d .add fun k => gamma ^ k.val) k *
          algebraMap BabyBear Ext6Q (wv (d.gates.get k).out) by
    exact sum_sparseTable (gateEncoding d wv enc) _]
  rw [show (∑ b, zeroGamma d wv enc gamma b) =
      ∑ j : Fin d.zeros.length,
        gamma ^ (d.gates.length + j.val) *
          algebraMap BabyBear Ext6Q ((d.zeros.get j).read wv) by
    exact sum_sparseTable (zeroEncoding d wv enc) _]
  unfold gammaBatchedDescriptorResidual
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases hop : (d.gates.get k).op <;>
    unfold gateOpScale GateMleExt6.gateResidual <;>
    rw [hop] <;>
    simp [GateOp.denote, map_add, map_mul, map_sub] <;>
    ring

/-- Satisfaction makes the factored cube claim zero, without committing a
materialized residual table. -/
theorem gammaBatchedDescriptorResidual_zero_of_holds
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear) (gamma : Ext6Q)
    (hd : descriptorHolds d wv) :
    gammaBatchedDescriptorResidual d wv gamma = 0 := by
  rcases hd with ⟨hg, hz⟩
  unfold gammaBatchedDescriptorResidual
  have hgate : ∀ k : Fin d.gates.length,
      GateMleExt6.gateResidual wv (d.gates.get k) = 0 := by
    intro k
    exact (GateMleExt6.gate_holds_iff_residual_zero wv _).mp
      (hg _ (List.get_mem _ k))
  have hzero : ∀ j : Fin d.zeros.length, (d.zeros.get j).read wv = 0 := by
    intro j
    exact hz _ (List.get_mem _ j)
  have hgatesum : (∑ k : Fin d.gates.length,
      gamma ^ k.val * algebraMap BabyBear Ext6Q
        (GateMleExt6.gateResidual wv (d.gates.get k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hgate k, map_zero, mul_zero]
  have hzerosum : (∑ j : Fin d.zeros.length,
      gamma ^ (d.gates.length + j.val) *
        algebraMap BabyBear Ext6Q ((d.zeros.get j).read wv)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hzero j, map_zero, mul_zero]
  rw [hgatesum, hzerosum, add_zero]

/-! ## 4. Degree two and the existing quadratic sumcheck chain -/

/-- An explicit restriction polynomial for one coordinate line. -/
noncomputable def factoredLinePolynomial
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (i : Fin m) (x : Fin m -> Ext6Q) : Polynomial Ext6Q :=
  let P := factoredGatePolynomial d wv enc gamma
  let cross :=
    (mle (mulAGamma d wv enc gamma) (Function.update x i 1) -
      mle (mulAGamma d wv enc gamma) (Function.update x i 0)) *
    (mle (mulB d wv enc) (Function.update x i 1) -
      mle (mulB d wv enc) (Function.update x i 0))
  C cross * X ^ 2 + C (P (Function.update x i 1) - P (Function.update x i 0) - cross) * X +
    C (P (Function.update x i 0))

theorem factoredLinePolynomial_eval
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (i : Fin m) (x : Fin m -> Ext6Q) (t : Ext6Q) :
    (factoredLinePolynomial d wv enc gamma i x).eval t =
      factoredGatePolynomial d wv enc gamma (Function.update x i t) := by
  have h := prodDiff_line (mulAGamma d wv enc gamma) (mulB d wv enc)
    (combinedC d wv enc gamma) i x t
  rw [factoredGatePolynomial, h]
  simp only [factoredLinePolynomial, factoredGatePolynomial, eval_add, eval_mul,
    eval_pow, eval_C, eval_X]
  ring

/-- The factored emitted-gate polynomial has individual degree at most two in
every variable. -/
theorem factored_individualDegree_le_two
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (i : Fin m) (x : Fin m -> Ext6Q) :
    ∃ q : Polynomial Ext6Q,
      q.degree < ((2 + 1 : Nat) : WithBot Nat) ∧
        ∀ t, q.eval t = factoredGatePolynomial d wv enc gamma (Function.update x i t) := by
  refine ⟨factoredLinePolynomial d wv enc gamma i x,
    lt_of_le_of_lt Polynomial.degree_quadratic_le (by decide), ?_⟩
  exact factoredLinePolynomial_eval d wv enc gamma i x

/-- The honest degree-two messages are precisely the existing quadratic
engine, with all linear channels absorbed into `combinedC`. -/
noncomputable def factoredRounds
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (chi : Nat -> Ext6Q) : Nat -> Polynomial Ext6Q :=
  quadHonest (mulAGamma d wv enc gamma) (mulB d wv enc)
    (combinedC d wv enc gamma) chi

theorem quadraticTable_sum_eq_gammaBatchedDescriptorResidual
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) :
    (∑ b, (mulAGamma d wv enc gamma b * mulB d wv enc b -
      combinedC d wv enc gamma b)) = gammaBatchedDescriptorResidual d wv gamma := by
  rw [← prodDiff_cube_sum]
  exact factored_cube_sum_eq_gammaBatchedDescriptorResidual d wv enc gamma

theorem factoredRounds_boolean_sum
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) :
    ∀ i, i < m ->
      (factoredRounds d wv enc gamma (chalOf r) i).eval 0 +
          (factoredRounds d wv enc gamma (chalOf r) i).eval 1 =
        scChain (gammaBatchedDescriptorResidual d wv gamma)
          (factoredRounds d wv enc gamma (chalOf r)) (chalOf r) i := by
  have h := quadHonest_boolean_sum (mulAGamma d wv enc gamma) (mulB d wv enc)
    (combinedC d wv enc gamma) r
  rw [quadraticTable_sum_eq_gammaBatchedDescriptorResidual d wv enc gamma] at h
  exact h

/-- On a satisfying trace the verifier's asserted sumcheck claim is literally
zero. -/
theorem factoredRounds_zero_boolean_sum
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) (r : Fin m -> Ext6Q) :
    ∀ i, i < m ->
      (factoredRounds d wv enc gamma (chalOf r) i).eval 0 +
          (factoredRounds d wv enc gamma (chalOf r) i).eval 1 =
        scChain 0 (factoredRounds d wv enc gamma (chalOf r)) (chalOf r) i := by
  have h := factoredRounds_boolean_sum d wv enc gamma r
  rw [gammaBatchedDescriptorResidual_zero_of_holds d wv gamma hd] at h
  exact h

/-- The factored terminal is the fixed seven-MLE expression. -/
theorem factoredRounds_terminal
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) :
    scChain (gammaBatchedDescriptorResidual d wv gamma)
        (factoredRounds d wv enc gamma (chalOf r)) (chalOf r) m =
      mle (mulAGamma d wv enc gamma) r * mle (mulB d wv enc) r -
        mle (mulCGamma d wv enc gamma) r +
      mle (addAGamma d wv enc gamma) r + mle (addBGamma d wv enc gamma) r -
        mle (addCGamma d wv enc gamma) r + mle (zeroGamma d wv enc gamma) r := by
  have h := scChain_quadHonest_final (mulAGamma d wv enc gamma) (mulB d wv enc)
    (combinedC d wv enc gamma) r
  rw [quadraticTable_sum_eq_gammaBatchedDescriptorResidual d wv enc gamma] at h
  calc
    _ = factoredGatePolynomial d wv enc gamma r := by
      simpa only [factoredRounds, factoredGatePolynomial] using h
    _ = _ := factoredGatePolynomial_expanded d wv enc gamma r

/-- The same terminal identity on the zero-anchored valid-trace chain. -/
theorem factoredRounds_zero_terminal
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) (r : Fin m -> Ext6Q) :
    scChain 0 (factoredRounds d wv enc gamma (chalOf r)) (chalOf r) m =
      mle (mulAGamma d wv enc gamma) r * mle (mulB d wv enc) r -
        mle (mulCGamma d wv enc gamma) r +
      mle (addAGamma d wv enc gamma) r + mle (addBGamma d wv enc gamma) r -
        mle (addCGamma d wv enc gamma) r + mle (zeroGamma d wv enc gamma) r := by
  have h := factoredRounds_terminal d wv enc gamma r
  rw [gammaBatchedDescriptorResidual_zero_of_holds d wv gamma hd] at h
  exact h

/-! ## 5. Seven public affine trace functionals and a generic opening seam -/

/-- A public finite-support linear functional plus a public constant. -/
structure TraceAffineFunctional where
  constant : Ext6Q
  weights : Nat →₀ Ext6Q

/-- Evaluation against the extension-lifted total trace. -/
noncomputable def TraceAffineFunctional.eval (f : TraceAffineFunctional)
    (trace : Nat -> Ext6Q) : Ext6Q :=
  f.constant + Finsupp.linearCombination Ext6Q trace f.weights

noncomputable def wireFunctional (z : DWire BabyBear) : TraceAffineFunctional :=
  match z with
  | .cnst c => ⟨algebraMap BabyBear Ext6Q c, 0⟩
  | .wire n => ⟨0, Finsupp.single n 1⟩

theorem wireFunctional_eval (z : DWire BabyBear) (wv : Nat -> BabyBear) :
    (wireFunctional z).eval (liftWord (K := Ext6Q) wv) =
      algebraMap BabyBear Ext6Q (z.read wv) := by
  cases z <;> simp [wireFunctional, TraceAffineFunctional.eval,
    Finsupp.linearCombination_single, liftWord]

/-- Public selector weights for an operand table at challenge `r`. -/
noncomputable def selectorFunctional {t : Nat} (enc : Fin t ↪ (Fin m -> Bool))
    (scale : Fin t -> Ext6Q) (operand : Fin t -> DWire BabyBear)
    (r : Fin m -> Ext6Q) : TraceAffineFunctional where
  constant := ∑ k,
    (scale k * chiEval (enc k) r) * (wireFunctional (operand k)).constant
  weights := ∑ k,
    (scale k * chiEval (enc k) r) • (wireFunctional (operand k)).weights

/-- Sparse-table MLE evaluation is the associated public affine functional of
the trace. -/
theorem mle_operandTable_eq_selectorFunctional_eval {t : Nat}
    (enc : Fin t ↪ (Fin m -> Bool)) (scale : Fin t -> Ext6Q)
    (operand : Fin t -> DWire BabyBear) (wv : Nat -> BabyBear)
    (r : Fin m -> Ext6Q) :
    mle (operandTable enc scale operand wv) r =
      (selectorFunctional enc scale operand r).eval (liftWord (K := Ext6Q) wv) := by
  classical
  rw [mle]
  unfold operandTable sparseTable selectorFunctional TraceAffineFunctional.eval
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hsparse :
      (∑ k, ∑ b, (if enc k = b then
          scale k * algebraMap BabyBear Ext6Q ((operand k).read wv) else 0) * chiEval b r) =
        ∑ k, scale k * algebraMap BabyBear Ext6Q ((operand k).read wv) *
          chiEval (enc k) r := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Fintype.sum_eq_single (enc k)]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  rw [hsparse]
  simp only [map_sum, LinearMap.map_smul, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hw := wireFunctional_eval (operand k) wv
  unfold TraceAffineFunctional.eval at hw
  rw [← hw]
  ring

/-- The fixed seven terminal functionals. -/
inductive TerminalKind
  | mulA | mulB | mulC | addA | addB | addC | zero
deriving DecidableEq, Fintype

noncomputable def terminalFunctional (kind : TerminalKind)
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) : TraceAffineFunctional :=
  match kind with
  | .mulA => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .mul fun k => gamma ^ k.val) (fun k => (d.gates.get k).a) r
  | .mulB => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .mul fun _ => 1) (fun k => (d.gates.get k).b) r
  | .mulC => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .mul fun k => gamma ^ k.val)
      (fun k => DWire.wire (d.gates.get k).out) r
  | .addA => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .add fun k => gamma ^ k.val) (fun k => (d.gates.get k).a) r
  | .addB => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .add fun k => gamma ^ k.val) (fun k => (d.gates.get k).b) r
  | .addC => selectorFunctional (gateEncoding d wv enc)
      (gateOpScale d .add fun k => gamma ^ k.val)
      (fun k => DWire.wire (d.gates.get k).out) r
  | .zero => selectorFunctional (zeroEncoding d wv enc)
      (fun j => gamma ^ (d.gates.length + j.val)) (fun j => d.zeros.get j) r

/-- The commitment layer's sole generic obligation: authenticate one public
finite-support linear functional of the trace.  Constants are not opened. -/
structure LinearFunctionalOpening (trace : Nat -> Ext6Q) (weights : Nat →₀ Ext6Q) where
  value : Ext6Q
  authenticates : value = Finsupp.linearCombination Ext6Q trace weights

/-- One generic opening for each of the fixed seven selector functionals. -/
structure TerminalOpenings
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) where
  openLinear : (kind : TerminalKind) ->
    LinearFunctionalOpening (liftWord (K := Ext6Q) wv)
      (terminalFunctional kind d wv enc gamma r).weights

noncomputable def TerminalOpenings.affineValue
    {d : ConstraintDescriptor BabyBear} {wv : Nat -> BabyBear}
    {enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool)}
    {gamma : Ext6Q} {r : Fin m -> Ext6Q}
    (opened : TerminalOpenings d wv enc gamma r) (kind : TerminalKind) : Ext6Q :=
  (terminalFunctional kind d wv enc gamma r).constant + (opened.openLinear kind).value

theorem TerminalOpenings.affineValue_eq_eval
    {d : ConstraintDescriptor BabyBear} {wv : Nat -> BabyBear}
    {enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool)}
    {gamma : Ext6Q} {r : Fin m -> Ext6Q}
    (opened : TerminalOpenings d wv enc gamma r) (kind : TerminalKind) :
    opened.affineValue kind =
      (terminalFunctional kind d wv enc gamma r).eval (liftWord (K := Ext6Q) wv) := by
  rw [TerminalOpenings.affineValue, TraceAffineFunctional.eval,
    (opened.openLinear kind).authenticates]

/-- The seven generic linear openings reconstruct the exact factored terminal. -/
theorem factoredRounds_terminal_of_openings
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q)
    (opened : TerminalOpenings d wv enc gamma r) :
    scChain (gammaBatchedDescriptorResidual d wv gamma)
        (factoredRounds d wv enc gamma (chalOf r)) (chalOf r) m =
      opened.affineValue .mulA * opened.affineValue .mulB -
        opened.affineValue .mulC + opened.affineValue .addA +
        opened.affineValue .addB - opened.affineValue .addC +
        opened.affineValue .zero := by
  rw [factoredRounds_terminal]
  simp only [TerminalOpenings.affineValue_eq_eval, terminalFunctional]
  rw [← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval,
    ← mle_operandTable_eq_selectorFunctional_eval]
  rfl

/-! ## 6. Fresh-eta aggregation of the seven linear openings -/

/-- Public eta-power aggregation of finite-support trace weights. -/
noncomputable def etaBatchedWeights {t : Nat} (eta : Ext6Q)
    (weights : Fin t -> Nat →₀ Ext6Q) : Nat →₀ Ext6Q :=
  ∑ j : Fin t, eta ^ j.val • weights j

/-- **Runtime aggregation identity.**  Once the `v_j` are transcript-bound and
each is the claimed public constant plus its trace functional, subtracting the
constants and batching by fresh eta is one linear functional against one
trace.  Instantiate `t = 7` in terminal order for the outer gate algebra. -/
theorem etaBatched_opening_identity {t : Nat} (eta : Ext6Q)
    (trace : Nat -> Ext6Q) (values constants : Fin t -> Ext6Q)
    (weights : Fin t -> Nat →₀ Ext6Q)
    (h : ∀ j, values j = constants j +
      Finsupp.linearCombination Ext6Q trace (weights j)) :
    (∑ j : Fin t, eta ^ j.val * (values j - constants j)) =
      Finsupp.linearCombination Ext6Q trace (etaBatchedWeights eta weights) := by
  calc
    _ = ∑ j : Fin t, eta ^ j.val *
        Finsupp.linearCombination Ext6Q trace (weights j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h j]
      ring
    _ = _ := by
      simp [etaBatchedWeights, smul_eq_mul]

/-- Runtime order of the seven terminal claims. -/
def terminalOrder : Fin 7 -> TerminalKind :=
  ![.mulA, .mulB, .mulC, .addA, .addB, .addC, .zero]

/-- Exact seven-operand instantiation of `etaBatched_opening_identity`, in the
same field order as Rust's `OperandEvaluations` and `TerminalOperandSelectors`. -/
theorem etaBatched_terminal_identity (eta : Ext6Q)
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (GateMleExt6.descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) (values : Fin 7 -> Ext6Q)
    (h : ∀ j, values j =
      (terminalFunctional (terminalOrder j) d wv enc gamma r).eval
        (liftWord (K := Ext6Q) wv)) :
    (∑ j : Fin 7, eta ^ j.val *
      (values j - (terminalFunctional (terminalOrder j) d wv enc gamma r).constant)) =
      Finsupp.linearCombination Ext6Q (liftWord (K := Ext6Q) wv)
        (etaBatchedWeights eta fun j =>
          (terminalFunctional (terminalOrder j) d wv enc gamma r).weights) := by
  apply etaBatched_opening_identity
  intro j
  simpa only [TraceAffineFunctional.eval] using h j

/-- Fixed post-transcript defect of one claimed affine opening. -/
noncomputable def openingDefect {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q)
    (j : Fin t) : Ext6Q :=
  (values j - constants j) - Finsupp.linearCombination Ext6Q trace (weights j)

/-- The fresh-eta aggregation defect polynomial. -/
noncomputable def etaDefectPolynomial {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q) :
    Polynomial Ext6Q :=
  ∑ j : Fin t, C (openingDefect trace values constants weights j) * X ^ j.val

theorem etaDefectPolynomial_eval {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q)
    (eta : Ext6Q) :
    (etaDefectPolynomial trace values constants weights).eval eta =
      ∑ j : Fin t, eta ^ j.val * openingDefect trace values constants weights j := by
  unfold etaDefectPolynomial
  change (evalRingHom eta) (∑ j : Fin t,
      C (openingDefect trace values constants weights j) * X ^ j.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, map_pow, coe_evalRingHom, eval_C, eval_X]
  ring

theorem etaDefectPolynomial_coeff {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q)
    (k : Fin t) :
    (etaDefectPolynomial trace values constants weights).coeff k.val =
      openingDefect trace values constants weights k := by
  classical
  unfold etaDefectPolynomial
  change (lcoeff Ext6Q k.val) (∑ j : Fin t,
      C (openingDefect trace values constants weights j) * X ^ j.val) = _
  rw [map_sum]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj
    have hv : k.val ≠ j.val := fun h => hj (Fin.ext h.symm)
    simp [hv]

theorem etaDefectPolynomial_ne_zero {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q)
    (h : ∃ j, openingDefect trace values constants weights j ≠ 0) :
    etaDefectPolynomial trace values constants weights ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  intro hp
  have hc : (etaDefectPolynomial trace values constants weights).coeff k.val = 0 := by
    rw [hp, coeff_zero]
  rw [etaDefectPolynomial_coeff] at hc
  exact hk hc

/-- The eta defect polynomial has degree strictly below the number of claims. -/
theorem etaDefectPolynomial_degree_lt {t : Nat} (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q) :
    (etaDefectPolynomial trace values constants weights).degree < t :=
  degree_sum_fin_lt _

/-- **Fresh-eta bad-challenge bound.**  If at least one transcript-bound affine
claim is false, at most `t-1` extension-field challenges aggregate the fixed
defects to zero.  For the landed seven-operand gate terminal this is at most
six bad eta values. -/
theorem card_bad_eta_le {t : Nat} (challenges : Finset Ext6Q)
    (trace : Nat -> Ext6Q)
    (values constants : Fin t -> Ext6Q) (weights : Fin t -> Nat →₀ Ext6Q)
    (h : ∃ j, openingDefect trace values constants weights j ≠ 0) :
    (challenges.filter fun eta : Ext6Q =>
      (∑ j : Fin t, eta ^ j.val *
        openingDefect trace values constants weights j) = 0).card ≤ t - 1 := by
  classical
  let p := etaDefectPolynomial trace values constants weights
  have hp : p ≠ 0 := etaDefectPolynomial_ne_zero trace values constants weights h
  have hdeg : p.natDegree < t :=
    (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
      (etaDefectPolynomial_degree_lt trace values constants weights)
  have hsub : (challenges.filter fun eta : Ext6Q =>
      (∑ j : Fin t, eta ^ j.val *
        openingDefect trace values constants weights j) = 0).val ⊆ p.roots := by
    intro eta heta
    rw [Finset.mem_val, Finset.mem_filter] at heta
    rw [Polynomial.mem_roots hp]
    exact (etaDefectPolynomial_eval trace values constants weights eta).trans heta.2
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  have ht : 0 < t := by
    obtain ⟨j, -⟩ := h
    exact Nat.zero_lt_of_lt j.isLt
  omega

#check @factored_cube_sum_eq_gammaBatchedDescriptorResidual
#check @factored_individualDegree_le_two
#check @factoredRounds_terminal_of_openings
#check @etaBatched_opening_identity
#check @card_bad_eta_le

#print axioms factoredRounds_terminal_of_openings

end GateFactoredExt6
end Minidregg.Compiler
