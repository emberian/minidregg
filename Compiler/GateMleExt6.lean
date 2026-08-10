/-
# Compiler.GateMleExt6 -- emitted gates through an Ext6 MLE terminal

This module is the clear-table side of the joined gate protocol.  It starts at
the serialized `ConstraintDescriptor`, materializes its gate and root-pin
residuals in their exact list order, embeds that table into the proved field
`Ext6Q`, weights entry `k` by `gamma^k`, and instantiates the existing honest
MLE sumcheck chain.  Thus descriptor provenance, base-to-extension transport,
the zero claim, every round identity, and the terminal MLE identity are
theorems here.

The sole succinct-oracle seam is `CommittedTerminal`: a future Mobius/FRI
assembly supplies an authenticated opening equal to this module's exact MLE.
No commitment or FRI claim is postulated or re-proved here.
-/

import Assurance.AirSumcheckQuadratic
import Compiler.Ext6Conformance
import Loom.ExtensionChallengeBridge

namespace Minidregg.Compiler

open scoped BigOperators
open Minidregg.Assurance Minidregg.Loom Polynomial

namespace GateMleExt6

/-! ## 1. Exact residual provenance from the emitted descriptor -/

/-- The scalar residual of one emitted gate. -/
def gateResidual {F : Type*} [Field F] (wv : Nat -> F) (g : DGate F) : F :=
  g.op.denote (g.a.read wv) (g.b.read wv) - wv g.out

theorem gate_holds_iff_residual_zero {F : Type*} [Field F]
    (wv : Nat -> F) (g : DGate F) :
    g.holds wv ↔ gateResidual wv g = 0 := by
  unfold DGate.holds gateResidual
  rw [sub_eq_zero]

/-- The canonical clear residual list: gates in descriptor order, followed by
root-pin reads in descriptor order. -/
def descriptorResiduals {F : Type*} [Field F]
    (d : ConstraintDescriptor F) (wv : Nat -> F) : List F :=
  d.gates.map (gateResidual wv) ++ d.zeros.map (fun z => z.read wv)

@[simp] theorem descriptorResiduals_length {F : Type*} [Field F]
    (d : ConstraintDescriptor F) (wv : Nat -> F) :
    (descriptorResiduals d wv).length = d.gates.length + d.zeros.length := by
  simp [descriptorResiduals]

/-- Materializing the residual list loses no descriptor condition. -/
theorem descriptorHolds_iff_residuals_zero {F : Type*} [Field F]
    (d : ConstraintDescriptor F) (wv : Nat -> F) :
    descriptorHolds d wv ↔ ∀ x ∈ descriptorResiduals d wv, x = 0 := by
  constructor
  · rintro ⟨hg, hz⟩ x hx
    simp only [descriptorResiduals, List.mem_append, List.mem_map] at hx
    rcases hx with hx | hx
    · obtain ⟨g, hgmem, rfl⟩ := hx
      exact (gate_holds_iff_residual_zero wv g).mp (hg g hgmem)
    · obtain ⟨z, hzmem, rfl⟩ := hx
      exact hz z hzmem
  · intro h
    constructor
    · intro g hg
      apply (gate_holds_iff_residual_zero wv g).mpr
      exact h _ (by
        simp only [descriptorResiduals, List.mem_append, List.mem_map]
        exact Or.inl ⟨g, hg, rfl⟩)
    · intro z hz
      exact h _ (by
        simp only [descriptorResiduals, List.mem_append, List.mem_map]
        exact Or.inr ⟨z, hz, rfl⟩)

/-! ## 2. Padded base table, exact Ext6 lift, and gamma powers -/

variable {m : Nat}

/-- Put residual `k` at corner `enc k`; unused cube corners are zero. -/
def residualTable (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    (Fin m -> Bool) -> BabyBear :=
  fun b => ∑ k, if enc k = b then (descriptorResiduals d wv).get k else 0

/-- The padded table reads the exact ordered descriptor residual at each used
corner.  This is `AirSumcheckQuadratic.sum_ite_enc`, not a new encoding lemma. -/
theorem residualTable_read (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (k : Fin (descriptorResiduals d wv).length) :
    residualTable d wv enc (enc k) = (descriptorResiduals d wv).get k :=
  sum_ite_enc enc _ k

/-- Descriptor satisfaction is exactly pointwise zero of the padded table. -/
theorem descriptorHolds_iff_residualTable_zero
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    descriptorHolds d wv ↔ ∀ b, residualTable d wv enc b = 0 := by
  constructor
  · intro hd b
    have hmem := (descriptorHolds_iff_residuals_zero d wv).mp hd
    have hget : ∀ k : Fin (descriptorResiduals d wv).length,
        (descriptorResiduals d wv).get k = 0 := by
      intro k
      exact hmem _ (List.get_mem _ k)
    unfold residualTable
    apply Finset.sum_eq_zero
    intro k _
    rw [hget k]
    split <;> simp
  · intro hzero
    apply (descriptorHolds_iff_residuals_zero d wv).mpr
    rw [List.forall_mem_iff_get]
    intro k
    rw [← residualTable_read d wv enc k]
    exact hzero (enc k)

/-- The table embedded coefficientwise from BabyBear into the proved degree-six
extension. -/
noncomputable def liftedResidualTable
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool)) :
    (Fin m -> Bool) -> Ext6Q :=
  liftWord (K := Ext6Q) (residualTable d wv enc)

@[simp] theorem liftedResidualTable_apply
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (b : Fin m -> Bool) :
    liftedResidualTable d wv enc b =
      algebraMap BabyBear Ext6Q (residualTable d wv enc b) := rfl

/-- The runtime's positional gamma mask: used entry `k` has coefficient
`gamma^k`; padding has coefficient zero. -/
noncomputable def gammaMask
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  fun b => ∑ k, if enc k = b then gamma ^ (k : Nat) else 0

/-- The one Ext6 table consumed by gate sumcheck. -/
noncomputable def gammaResidualTable
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) : (Fin m -> Bool) -> Ext6Q :=
  fun b => gammaMask d wv enc gamma b * liftedResidualTable d wv enc b

/-- At used corner `k`, the joined table is exactly `gamma^k` times the
algebraic embedding of emitted residual `k`. -/
theorem gammaResidualTable_read
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (k : Fin (descriptorResiduals d wv).length) :
    gammaResidualTable d wv enc gamma (enc k) =
      gamma ^ (k : Nat) *
        algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k) := by
  rw [gammaResidualTable, gammaMask, sum_ite_enc enc _ k,
    liftedResidualTable_apply, residualTable_read]

/-- A valid descriptor makes the complete Ext6 gamma-weighted table zero. -/
theorem gammaResidualTable_zero_of_descriptorHolds
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) :
    ∀ b, gammaResidualTable d wv enc gamma b = 0 := by
  intro b
  rw [gammaResidualTable, liftedResidualTable_apply,
    (descriptorHolds_iff_residualTable_zero d wv enc).mp hd b, map_zero, mul_zero]

/-- Hence the claimed hypercube total is literally zero. -/
theorem gammaResidual_zeroClaim
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) :
    ∑ b, gammaResidualTable d wv enc gamma b = 0 := by
  simp [gammaResidualTable_zero_of_descriptorHolds d wv enc gamma hd]

/-! ## 3. Compatibility with the existing factored quadratic gate table -/

/-- The already-proved multiplication defect table commutes pointwise with the
BabyBear-to-Ext6 embedding.  Thus the clear residual and the factored
`A-hat * B-hat - C-hat` terminal agree at every Boolean corner; authenticating
that factorization off the cube is deliberately the commitment-opening seam
below. -/
theorem lift_defectWord_apply {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (gs : List (Gate BabyBear Idx))
    (enc : Fin gs.length ↪ (Fin m -> Bool))
    (asg : Idx -> BabyBear) (auxv : Nat -> BabyBear) (b : Fin m -> Bool) :
    liftWord (K := Ext6Q) (defectWord gs enc asg auxv) b =
      algebraMap BabyBear Ext6Q (gateTableA gs enc asg auxv b) *
        algebraMap BabyBear Ext6Q (gateTableB gs enc asg auxv b) -
          algebraMap BabyBear Ext6Q (gateTableC gs enc asg auxv b) := by
  simp [liftWord, defectWord, map_mul, map_sub]

/-- The same compatibility at a Boolean MLE corner, using the existing MLE
agreement theorem. -/
theorem lifted_defectWord_mle_corner {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (gs : List (Gate BabyBear Idx))
    (enc : Fin gs.length ↪ (Fin m -> Bool))
    (asg : Idx -> BabyBear) (auxv : Nat -> BabyBear) (b : Fin m -> Bool) :
    mle (liftWord (K := Ext6Q) (defectWord gs enc asg auxv)) (cubePt b) =
      algebraMap BabyBear Ext6Q (gateTableA gs enc asg auxv b) *
        algebraMap BabyBear Ext6Q (gateTableB gs enc asg auxv b) -
          algebraMap BabyBear Ext6Q (gateTableC gs enc asg auxv b) := by
  rw [mle_agrees]
  exact lift_defectWord_apply gs enc asg auxv b

/-! ## 4. Ext6 MLE sumcheck round chain and terminal -/

/-- The honest degree-one round messages for the materialized Ext6 table. -/
noncomputable def honestRounds
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (chi : Nat -> Ext6Q) : Nat -> Polynomial Ext6Q :=
  mleHonest (gammaResidualTable d wv enc gamma) chi

/-- Every honest round satisfies the zero-anchored sumcheck recurrence. -/
theorem honestRounds_boolean_sum
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) (r : Fin m -> Ext6Q) :
    ∀ i, i < m ->
      (honestRounds d wv enc gamma (chalOf r) i).eval 0 +
          (honestRounds d wv enc gamma (chalOf r) i).eval 1 =
        scChain 0 (honestRounds d wv enc gamma (chalOf r)) (chalOf r) i := by
  have hz := gammaResidual_zeroClaim d wv enc gamma hd
  simpa only [honestRounds, hz] using
    mleHonest_boolean_sum (gammaResidualTable d wv enc gamma) r

/-- After all rounds, the zero-anchored chain is the exact MLE of the exact
gamma-weighted residual table. -/
theorem honestRounds_terminal
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) (r : Fin m -> Ext6Q) :
    scChain 0 (honestRounds d wv enc gamma (chalOf r)) (chalOf r) m =
      mle (gammaResidualTable d wv enc gamma) r := by
  have h := scChain_mleHonest_final (gammaResidualTable d wv enc gamma) r
  rw [gammaResidual_zeroClaim d wv enc gamma hd] at h
  exact h

/-! ## 5. The one explicit succinct opening interface -/

/-- An authenticated succinct terminal.  The forthcoming Mobius/FRI assembly
constructs this record by opening its factored selector commitments.  This
module assumes only the resulting equality to the exact clear-table MLE. -/
structure CommittedTerminal
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (r : Fin m -> Ext6Q) where
  value : Ext6Q
  factoredSelectorOpening :
    value = mle (gammaResidualTable d wv enc gamma) r

/-- The clear sumcheck terminal closes against any authenticated committed
terminal implementing the interface above. -/
theorem honestRounds_closes_committed
    (d : ConstraintDescriptor BabyBear) (wv : Nat -> BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m -> Bool))
    (gamma : Ext6Q) (hd : descriptorHolds d wv) (r : Fin m -> Ext6Q)
    (opened : CommittedTerminal d wv enc gamma r) :
    scChain 0 (honestRounds d wv enc gamma (chalOf r)) (chalOf r) m = opened.value := by
  rw [honestRounds_terminal d wv enc gamma hd r, opened.factoredSelectorOpening]

#check @descriptorHolds_iff_residualTable_zero
#check @gammaResidualTable_read
#check @honestRounds_boolean_sum
#check @honestRounds_closes_committed

/-- info: 'Minidregg.Compiler.GateMleExt6.honestRounds_closes_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestRounds_closes_committed

end GateMleExt6
end Minidregg.Compiler
