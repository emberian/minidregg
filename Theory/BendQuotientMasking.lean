import Theory.BendMaskingInterpolation

/- Algebraic qualification of the ACTUAL pinned HidingFriPcs quotient-mask
construction: free chunk masks, and the last mask corrected by -ci/c_last.
This is a fixed-observation coupling, not a full-transcript ZK theorem. Native
DFT/vanishing/Lagrange constants, extension/base-field descent, adaptive query
composition and Fiat–Shamir remain explicit correspondence obligations. -/
namespace Minidregg.Theory.BendQuotientMasking
set_option autoImplicit false
open scoped BigOperators
variable {F I : Type*} [Field F] [Fintype I]

/-- Matches the per-coefficient last-chunk loop in the pinned backend. -/
def lastMask (normalizers : I → F) (lastNormalizer : F) (free : I → F) : F :=
  - ∑ i, (normalizers i / lastNormalizer) * free i

theorem mask_balance (normalizers : I → F) (lastNormalizer : F)
    (nonzero : lastNormalizer ≠ 0) (free : I → F) :
    (∑ i, normalizers i * free i) + lastNormalizer * lastMask normalizers lastNormalizer free = 0 := by
  have coordinate : ∀ i, lastNormalizer * ((normalizers i / lastNormalizer) * free i) =
      normalizers i * free i := by
    intro i
    field_simp
  simp only [lastMask, mul_neg, Finset.mul_sum, coordinate]
  ring

def recompose (weights : I → F) (lastWeight : F) (values : I → F) (lastValue : F) : F :=
  (∑ i, weights i * values i) + lastWeight * lastValue

/-- Quotient masking preserves exactly the verifier's weighted recombination
when its real vanishing-polynomial normalization identities hold. -/
theorem masked_recompose (normalizers weights vanish : I → F)
    (lastNormalizer lastWeight lastVanish common : F)
    (nonzero : lastNormalizer ≠ 0)
    (normalization : ∀ i, weights i * vanish i = common * normalizers i)
    (lastNormalization : lastWeight * lastVanish = common * lastNormalizer)
    (values free : I → F) (lastValue : F) :
    recompose weights lastWeight (fun i => values i + vanish i * free i)
      (lastValue + lastVanish * lastMask normalizers lastNormalizer free) =
      recompose weights lastWeight values lastValue := by
  have coordinates : ∀ i, weights i * (values i + vanish i * free i) =
      weights i * values i + common * (normalizers i * free i) := by
    intro i
    rw [mul_add, ← mul_assoc, normalization]
    ring
  have last : lastWeight * (lastValue + lastVanish * lastMask normalizers lastNormalizer free) =
      lastWeight * lastValue + common * (lastNormalizer * lastMask normalizers lastNormalizer free) := by
    rw [mul_add, ← mul_assoc, lastNormalization]
    ring
  simp only [recompose, coordinates, Finset.sum_add_distrib, ← Finset.mul_sum, last]
  have balanced := mask_balance normalizers lastNormalizer nonzero free
  calc
    _ = (∑ i, weights i * values i) + lastWeight * lastValue +
        common * ((∑ i, normalizers i * free i) + lastNormalizer * lastMask normalizers lastNormalizer free) := by ring
    _ = _ := by rw [balanced]; ring

/-- Translation on the actual free mask coordinates, with an explicit inverse. -/
def translate (offset : I → F) : (I → F) ≃ (I → F) where
  toFun masks := fun i => masks i + offset i
  invFun masks := fun i => masks i - offset i
  left_inv := by intro masks; funext i; dsimp; ring
  right_inv := by intro masks; funext i; dsimp; ring

/-- For two chunk tuples with the same recomposed quotient value, translation
of the independent masks makes every individual opened chunk identical,
including the dependent last mask. All first-chunk vanishing factors and the
common recombination factor must be nonzero at this actual observation point.
This is NOT silently quantified over base-field polynomial coefficients when
F is an extension field, nor over an adaptive whole proof transcript. -/
theorem opening_coupling (normalizers weights vanish : I → F)
    (lastNormalizer lastWeight lastVanish common : F)
    (lastNonzero : lastNormalizer ≠ 0) (commonNonzero : common ≠ 0)
    (outside : ∀ i, vanish i ≠ 0)
    (normalization : ∀ i, weights i * vanish i = common * normalizers i)
    (lastNormalization : lastWeight * lastVanish = common * lastNormalizer)
    (left right : I → F) (leftLast rightLast : F)
    (sameRecomposition : recompose weights lastWeight left leftLast =
      recompose weights lastWeight right rightLast) :
    ∃ shift : (I → F) ≃ (I → F), ∀ masks,
      (∀ i, left i + vanish i * masks i = right i + vanish i * shift masks i) ∧
      leftLast + lastVanish * lastMask normalizers lastNormalizer masks =
        rightLast + lastVanish * lastMask normalizers lastNormalizer (shift masks) := by
  let offset : I → F := fun i => (left i - right i) / vanish i
  refine ⟨translate offset, ?_⟩
  intro masks
  have first : ∀ i, left i + vanish i * masks i =
      right i + vanish i * (translate offset masks) i := by
    intro i
    change left i + vanish i * masks i = right i + vanish i * (masks i + (left i - right i) / vanish i)
    field_simp [outside i]
    ring
  have leftBalanced := masked_recompose normalizers weights vanish lastNormalizer lastWeight
    lastVanish common lastNonzero normalization lastNormalization left masks leftLast
  have rightBalanced := masked_recompose normalizers weights vanish lastNormalizer lastWeight
    lastVanish common lastNonzero normalization lastNormalization right (translate offset masks) rightLast
  have total := leftBalanced.trans (sameRecomposition.trans rightBalanced.symm)
  have weightNonzero : lastWeight ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at lastNormalization
    exact (mul_ne_zero commonNonzero lastNonzero) lastNormalization.symm
  refine ⟨first, ?_⟩
  apply mul_left_cancel₀ weightNonzero
  simpa only [recompose, first, add_right_inj] using total

#assert_axioms mask_balance
#assert_axioms masked_recompose
#assert_axioms opening_coupling
end Minidregg.Theory.BendQuotientMasking
