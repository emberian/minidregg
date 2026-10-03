import Theory.BendQuotientMasking

/- The pinned native verifier multiplies each other chunk's vanishing value by
its value at this chunk's anchor inverse. The prover's ci is the inverse product
of those anchor values. These identities connect those formulas, not an assumed
free normalization equation. Domain disjointness remains a native obligation. -/
namespace Minidregg.Theory.BendQuotientSelectors
set_option autoImplicit false
open scoped BigOperators
variable {F J : Type*} [Field F] [Fintype J] [DecidableEq J]

def normalizer (anchors : J → J → F) (i : J) : F :=
  (∏ j ∈ Finset.univ.erase i, anchors i j)⁻¹

def weight (anchors : J → J → F) (vanish : J → F) (i : J) : F :=
  ∏ j ∈ Finset.univ.erase i, vanish j * (anchors i j)⁻¹

/-- The actual product expression used for quotient recombination. -/
theorem normalization (anchors : J → J → F) (vanish : J → F) (i : J) :
    weight anchors vanish i * vanish i = (∏ j, vanish j) * normalizer anchors i := by
  classical
  simp only [weight, normalizer, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  calc
    _ = ((∏ j ∈ Finset.univ.erase i, vanish j) * vanish i) *
        (∏ j ∈ Finset.univ.erase i, anchors i j)⁻¹ := by ring
    _ = _ := by rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

theorem normalizer_ne_zero (anchors : J → J → F) (i : J)
    (disjoint : ∀ j, j ≠ i → anchors i j ≠ 0) : normalizer anchors i ≠ 0 := by
  apply inv_ne_zero
  exact Finset.prod_ne_zero_iff.mpr fun j member => disjoint j (Finset.mem_erase.mp member).1

theorem common_ne_zero (vanish : J → F) (outside : ∀ j, vanish j ≠ 0) :
    (∏ j, vanish j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => outside j

/-- Direct consumer for the native quotient formulas, with one distinguished
last chunk and independently sampled masks for all remaining chunks. The only
normalization premises now concern actual domain separation and query location. -/
theorem opening_coupling {I : Type*} [Fintype I] [DecidableEq I]
    (anchors : Option I → Option I → F) (vanish : Option I → F)
    (disjoint : ∀ j, j ≠ none → anchors none j ≠ 0)
    (outside : ∀ j, vanish j ≠ 0)
    (left right : I → F) (leftLast rightLast : F)
    (sameRecomposition :
      BendQuotientMasking.recompose (fun i => weight anchors vanish (some i))
        (weight anchors vanish none) left leftLast =
      BendQuotientMasking.recompose (fun i => weight anchors vanish (some i))
        (weight anchors vanish none) right rightLast) :
    ∃ shift : (I → F) ≃ (I → F), ∀ masks,
      (∀ i, left i + vanish (some i) * masks i =
        right i + vanish (some i) * shift masks i) ∧
      leftLast + vanish none * BendQuotientMasking.lastMask
        (fun i => normalizer anchors (some i)) (normalizer anchors none) masks =
      rightLast + vanish none * BendQuotientMasking.lastMask
        (fun i => normalizer anchors (some i)) (normalizer anchors none) (shift masks) := by
  exact BendQuotientMasking.opening_coupling
    (fun i => normalizer anchors (some i)) (fun i => weight anchors vanish (some i))
    (fun i => vanish (some i)) (normalizer anchors none) (weight anchors vanish none)
    (vanish none) (∏ j, vanish j) (normalizer_ne_zero anchors none disjoint)
    (common_ne_zero vanish outside) (fun i => outside (some i))
    (fun i => normalization anchors vanish (some i)) (normalization anchors vanish none)
    left right leftLast rightLast sameRecomposition

#assert_axioms opening_coupling
#assert_axioms normalization
#assert_axioms normalizer_ne_zero
#assert_axioms common_ne_zero
end Minidregg.Theory.BendQuotientSelectors
