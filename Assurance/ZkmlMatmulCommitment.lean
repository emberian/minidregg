/-
# Assurance.ZkmlMatmulCommitment — the three root-bound claims of a contraction

The contraction verifier does not need two unpriced openings. It needs THREE
multilinear evaluation claims: the output commitment at `(x,y)`, the left operand
at `(x,r)`, and the right operand at `(r,y)`. The sumcheck connects the first value
to the product of the latter two. Passing the complete output table to a native
verifier hides the first claim rather than eliminating it.

This file binds all three claims to `MleEvalClaim` over Selvage's existing
positional vector commitment. The remaining `[MATMUL-pcs]` work is the BaseFold
`Reduction`/`RbrKnowledgeSoundness` transcript, not a new KZG-shaped `openAt`.
-/
import Assurance.ZkmlMatmulSumcheck
import Selvage.MultilinearCommitment
import Selvage.Rank1GradientCheck

namespace Minidregg.Assurance

open Minidregg.Selvage

/-! ## One cube for a two-block table -/

section Flatten

variable {F : Type} [CommRing F] {μ ν : ℕ}

/-- Flatten a curried two-block table along `Fin.appendEquiv`, row block first. -/
def flatten₂ (f : (Fin μ → Bool) → (Fin ν → Bool) → F) :
    (Fin (μ + ν) → Bool) → F :=
  fun b => f (rowHalf μ ν b) (colHalf μ ν b)

omit [CommRing F] in
@[simp] theorem flatten₂_append (f : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (a : Fin μ → Bool) (b : Fin ν → Bool) :
    flatten₂ f (Fin.append a b) = f a b := by
  simp [flatten₂]

/-- BaseFold's one-cube MLE is exactly the contraction file's two-block MLE. -/
theorem mle_flatten₂ (f : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) :
    mle (flatten₂ f) (Fin.append x y) = mle₂ f x y := by
  rw [mle]
  calc
    (∑ b, flatten₂ f b * chiEval b (Fin.append x y))
        = ∑ p : ((Fin μ → Bool) × (Fin ν → Bool)),
            flatten₂ f (Fin.append p.1 p.2)
              * chiEval (Fin.append p.1 p.2) (Fin.append x y) := by
          exact (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) μ ν)
            (fun p => flatten₂ f (Fin.append p.1 p.2)
              * chiEval (Fin.append p.1 p.2) (Fin.append x y))
            (fun b => flatten₂ f b * chiEval b (Fin.append x y))
            (fun _ => rfl)).symm
    _ = ∑ a, ∑ b, f a b * chiEval a x * chiEval b y := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [flatten₂_append, chiEval_split, rowHalf_append, colHalf_append]
            ring
    _ = mle₂ f x y := rfl

end Flatten

/-! ## The three claims -/

/-- The PCS-facing statement of one matmul sumcheck. Distinct root/domain types allow
the three tables to have dimensions `μ+κ`, `κ+ν`, and `μ+ν`. -/
structure MatmulMleClaims (RootA RootB RootC F : Type*) (μ κ ν : ℕ) where
  output : MleEvalClaim RootC F (μ + ν)
  left : MleEvalClaim RootA F (μ + κ)
  right : MleEvalClaim RootB F (κ + ν)

section Honest

variable {F : Type} {RootA RootB RootC OpA OpB OpC ιA ιB ιC : Type*}
variable [Field F] {μ κ ν : ℕ}

/-- Construct the three exact claims for a contraction transcript. The output claim
is rooted in caller-supplied `C`; soundness later compares it with `matmulTable A B`. -/
noncomputable def honestMatmulMleClaims
    (SA : BindingCommitment RootA F ιA OpA)
    (SB : BindingCommitment RootB F ιB OpB)
    (SC : BindingCommitment RootC F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F) :
    MatmulMleClaims RootA RootB RootC F μ κ ν where
  output :=
    ⟨SC.commit (basefoldWord domC (flatten₂ C)), Fin.append x y, mle₂ C x y⟩
  left :=
    ⟨SA.commit (basefoldWord domA (flatten₂ A)), Fin.append x r,
      mle (rowPartial A x) r⟩
  right :=
    ⟨SB.commit (basefoldWord domB (flatten₂ B)), Fin.append r y,
      mle (colPartial B y) r⟩

/-- Completeness at the commitment-claim layer: all three honest claims are true.
This does not yet construct their BaseFold transcripts. -/
theorem honestMatmulMleClaims_hold
    (SA : BindingCommitment RootA F ιA OpA)
    (SB : BindingCommitment RootB F ιB OpB)
    (SC : BindingCommitment RootC F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F) :
    let claims := honestMatmulMleClaims SA SB SC domA domB domC A B C x y r
    claims.output.Holds SC domC ∧
      claims.left.Holds SA domA ∧ claims.right.Holds SB domB := by
  dsimp only [honestMatmulMleClaims]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨flatten₂ C, rfl, ?_⟩
    exact mle_flatten₂ C x y
  · refine ⟨flatten₂ A, rfl, ?_⟩
    rw [mle_flatten₂, mle₂_row]
  · refine ⟨flatten₂ B, rfl, ?_⟩
    rw [mle_flatten₂, mle₂_col]

end Honest

/-! ## Binding all three values -/

section Binding

variable {F : Type} {RootA RootB RootC OpA OpB OpC ιA ιB ιC : Type*}
variable [Field F] [DecidableEq F]
variable [Fintype ιA] [Fintype ιB] [Fintype ιC]
variable {μ κ ν : ℕ}

/-- If the claims verify against the expected roots and points, their values are the
three exact MLEs consumed by the contraction sumcheck. -/
theorem matmul_opening_values_bound
    (SA : BindingCommitment RootA F ιA OpA)
    (SB : BindingCommitment RootB F ιB OpB)
    (SC : BindingCommitment RootC F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card ιA)
    (hcardB : 2 ^ (κ + ν) ≤ Fintype.card ιB)
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card ιC)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F)
    (claims : MatmulMleClaims RootA RootB RootC F μ κ ν)
    (hrootA : claims.left.rt = SA.commit (basefoldWord domA (flatten₂ A)))
    (hrootB : claims.right.rt = SB.commit (basefoldWord domB (flatten₂ B)))
    (hrootC : claims.output.rt = SC.commit (basefoldWord domC (flatten₂ C)))
    (hptA : claims.left.pt = Fin.append x r)
    (hptB : claims.right.pt = Fin.append r y)
    (hptC : claims.output.pt = Fin.append x y)
    (hA : claims.left.Holds SA domA)
    (hB : claims.right.Holds SB domB)
    (hC : claims.output.Holds SC domC) :
    claims.output.val = mle₂ C x y ∧
      claims.left.val = mle (rowPartial A x) r ∧
      claims.right.val = mle (colPartial B y) r := by
  have hvA := (MleEvalClaim.holds_iff_of_committed
    SA domA hcardA (flatten₂ A) claims.left hrootA).mp hA
  have hvB := (MleEvalClaim.holds_iff_of_committed
    SB domB hcardB (flatten₂ B) claims.right hrootB).mp hB
  have hvC := (MleEvalClaim.holds_iff_of_committed
    SC domC hcardC (flatten₂ C) claims.output hrootC).mp hC
  rw [hptA, mle_flatten₂, mle₂_row] at hvA
  rw [hptB, mle_flatten₂, mle₂_col] at hvB
  rw [hptC, mle_flatten₂] at hvC
  exact ⟨hvC.symm, hvA.symm, hvB.symm⟩

end Binding

/-! ## F7 premise firing and the hidden third-opening tooth -/

namespace MatmulCommitmentExample

open MatmulExample

/-- Four distinct F7 points, enough for a two-variable BaseFold word. -/
def dom₇₄ : Fin 4 ↪ ZMod 7 where
  toFun i := i.val
  inj' := by decide

/-- All three honest contraction claims are inhabited over identity commitments. -/
theorem honest_three_claims_hold :
    let S := idealCommitment (ZMod 7) (Fin 4)
    let claims := honestMatmulMleClaims S S S dom₇₄ dom₇₄ dom₇₄ eA eB
      (matmulTable eA eB) ![3] ![5] ![2]
    claims.output.Holds S dom₇₄ ∧
      claims.left.Holds S dom₇₄ ∧ claims.right.Holds S dom₇₄ :=
  honestMatmulMleClaims_hold _ _ _ _ _ _ _ _ _ _ _ _

/-- The output opening is load-bearing: changing only its value `5 -> 6` is refused.
A verifier handed the whole output table had hidden this third claim. -/
theorem wrong_output_value_refused :
    let S := idealCommitment (ZMod 7) (Fin 4)
    ¬ MleEvalClaim.Holds S dom₇₄
      ⟨S.commit (basefoldWord dom₇₄ (flatten₂ (matmulTable eA eB))),
        Fin.append ![3] ![5], 6⟩ := by
  dsimp only
  refine MleEvalClaim.wrong_value_refused _ _ (by norm_num)
    (flatten₂ (matmulTable eA eB)) (Fin.append ![3] ![5]) ?_
  rw [mle_flatten₂, contraction_offcube.1]
  decide

end MatmulCommitmentExample

/-- info: 'Minidregg.Assurance.mle_flatten₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_flatten₂
/-- info: 'Minidregg.Assurance.honestMatmulMleClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestMatmulMleClaims_hold
/-- info: 'Minidregg.Assurance.matmul_opening_values_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_opening_values_bound
/-- info: 'Minidregg.Assurance.MatmulCommitmentExample.wrong_output_value_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MatmulCommitmentExample.wrong_output_value_refused

end Minidregg.Assurance
