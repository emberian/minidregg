import Mathlib.LinearAlgebra.Basic
import Theory.AssertAxioms

/- Masking is a linear observation coverage problem. A mask count alone is
not a hiding theorem: the actual evaluation maps and whole transcript must
satisfy the range premise below. Uniform independent masks then admit a
translation bijection between any two witness-conditioned observations. -/
namespace Minidregg.Theory.BendMaskingDimension
set_option autoImplicit false

structure QueryBudget where
  extensionDegree : Nat
  extensionOpenings : Nat
  baseOpenings : Nat
  deriving DecidableEq, Repr

def QueryBudget.required (budget : QueryBudget) : Nat :=
  budget.extensionDegree * budget.extensionOpenings + budget.baseOpenings

def QueryBudget.Covers (budget : QueryBudget) (masks : Nat) : Prop :=
  budget.required ≤ masks

/-- Exact present local-row IR2 trace schedule: default main AIR opens local
and next at degree4; the PCS exposes one base input row in each of19 FRI
queries. Auxiliary lookup/permutation tables are outside this profile. -/
def ir2Trace : QueryBudget := ⟨4, 2, 19⟩

theorem ir2_trace_required : ir2Trace.required = 27 := by decide
theorem ir2_32_covers : ir2Trace.Covers 32 := by decide
theorem ir2_16_insufficient : ¬ ir2Trace.Covers 16 := by decide

section LinearCoverage
variable {F W M O : Type*} [Field F]
  [AddCommGroup W] [Module F W] [AddCommGroup M] [Module F M]
  [AddCommGroup O] [Module F O]

/-- A concrete sufficient opening condition. The producer must discharge this
for the actual trace-domain mask and actual public opening maps; replacing it
by a name or field count would not prove the claim. -/
def CoversObservations (witness : W →ₗ[F] O) (mask : M →ₗ[F] O) : Prop :=
  ∀ value, ∃ randomness, mask randomness = witness value

/-- Constructive coupling: translating masks by a fixed offset preserves the
entire observation vector when changing any private witness. Translation is
bijective, hence preserves uniform independent finite-field mask sampling. -/
theorem observation_translation (witness : W →ₗ[F] O) (mask : M →ₗ[F] O)
    (coverage : CoversObservations witness mask) (left right : W) :
    ∃ offset : M, ∀ randomness : M,
      witness left + mask randomness = witness right + mask (randomness + offset) := by
  obtain ⟨offset, exactOffset⟩ := coverage (left - right)
  refine ⟨offset, ?_⟩
  intro randomness
  rw [map_add, exactOffset, map_sub]
  abel

theorem mask_translation_bijective (offset : M) :
    Function.Bijective (fun randomness : M => randomness + offset) := by
  constructor
  · intro a b h
    exact add_right_cancel h
  · intro value
    exact ⟨value - offset, by abel⟩
end LinearCoverage

#assert_axioms ir2_trace_required
#assert_axioms ir2_32_covers
#assert_axioms ir2_16_insufficient
#assert_axioms observation_translation
#assert_axioms mask_translation_bijective
end Minidregg.Theory.BendMaskingDimension
