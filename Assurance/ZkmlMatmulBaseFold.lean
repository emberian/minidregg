/-
# Assurance.ZkmlMatmulBaseFold — price the three contraction openings

The contraction sumcheck and the polynomial-opening argument have different
soundness ledgers.  The former contributes `κ * 3 / |F|` because its round
polynomials have degree at most three.  The latter must separately open THREE
multilinear claims, with dimensions `μ + ν`, `μ + κ`, and `κ + ν`.

This file connects each field of `MatmulMleClaims` to the arbitrary-word
full-word BaseFold IOR theorem.  A false strict opening claim therefore costs
its dimension times `3 / |F|`: one fold-distance root and two sumcheck roots
per round.  `matmulBaseFoldIorAlgebraicBudget` records the additive envelope
for the three opening slots without pretending that sampled Merkle queries or
their BCS/Fiat--Shamir compilation have already been proved.
-/
import Assurance.ZkmlMatmulCommitment
import Selvage.BaseFoldIor

namespace Minidregg.Assurance

open Minidregg.Selvage
open Polynomial

variable {F RootA RootB RootC : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable {μ κ ν : ℕ}

/-! ## One exact full-word theorem for each committed claim -/

section Openings

variable {ιA ιB ιC : ℕ → Type*}

/-- If the output word and the output field of the matmul statement do not form
one strict BaseFold claim, the full-word output opening costs
`(μ + ν) * 3 / |F|`. -/
theorem matmul_output_basefold_sound [∀ n, Fintype (ιC n)]
    (TC : FoldingTower F ιC (μ + ν))
    (claims : MatmulMleClaims RootA RootB RootC F μ κ ν)
    (wordC : ιC 0 → F)
    (proverC : (ℕ → F) → ℕ → Polynomial F)
    (hneC : ∀ n, n ≤ μ + ν → Nonempty (ιC n))
    (hfalseC : ¬ BaseFoldExactClaim TC claims.output.pt claims.output.val wordC)
    (hpmC : PrefixMeasurable proverC)
    (hdegC : ∀ (χ : ℕ → F) (i : ℕ), i < μ + ν →
      (proverC χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin (μ + ν) → F) (fun r =>
      BaseFoldIorAccepts TC claims.output.pt claims.output.val wordC proverC r)
      ≤ ((μ + ν : ℕ) : ℝ) * (3 / Fintype.card F) := by
  exact basefoldIor_exact_sound TC claims.output.pt claims.output.val wordC
    proverC hneC hfalseC hpmC hdegC

/-- If the left-operand word and its matmul claim field do not form one strict
BaseFold claim, the full-word opening costs `(μ + κ) * 3 / |F|`. -/
theorem matmul_left_basefold_sound [∀ n, Fintype (ιA n)]
    (TA : FoldingTower F ιA (μ + κ))
    (claims : MatmulMleClaims RootA RootB RootC F μ κ ν)
    (wordA : ιA 0 → F)
    (proverA : (ℕ → F) → ℕ → Polynomial F)
    (hneA : ∀ n, n ≤ μ + κ → Nonempty (ιA n))
    (hfalseA : ¬ BaseFoldExactClaim TA claims.left.pt claims.left.val wordA)
    (hpmA : PrefixMeasurable proverA)
    (hdegA : ∀ (χ : ℕ → F) (i : ℕ), i < μ + κ →
      (proverA χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin (μ + κ) → F) (fun r =>
      BaseFoldIorAccepts TA claims.left.pt claims.left.val wordA proverA r)
      ≤ ((μ + κ : ℕ) : ℝ) * (3 / Fintype.card F) := by
  exact basefoldIor_exact_sound TA claims.left.pt claims.left.val wordA
    proverA hneA hfalseA hpmA hdegA

/-- If the right-operand word and its matmul claim field do not form one strict
BaseFold claim, the full-word opening costs `(κ + ν) * 3 / |F|`. -/
theorem matmul_right_basefold_sound [∀ n, Fintype (ιB n)]
    (TB : FoldingTower F ιB (κ + ν))
    (claims : MatmulMleClaims RootA RootB RootC F μ κ ν)
    (wordB : ιB 0 → F)
    (proverB : (ℕ → F) → ℕ → Polynomial F)
    (hneB : ∀ n, n ≤ κ + ν → Nonempty (ιB n))
    (hfalseB : ¬ BaseFoldExactClaim TB claims.right.pt claims.right.val wordB)
    (hpmB : PrefixMeasurable proverB)
    (hdegB : ∀ (χ : ℕ → F) (i : ℕ), i < κ + ν →
      (proverB χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin (κ + ν) → F) (fun r =>
      BaseFoldIorAccepts TB claims.right.pt claims.right.val wordB proverB r)
      ≤ ((κ + ν : ℕ) : ℝ) * (3 / Fintype.card F) := by
  exact basefoldIor_exact_sound TB claims.right.pt claims.right.val wordB
    proverB hneB hfalseB hpmB hdegB

end Openings

/-! ## Honest numerical ledger -/

/-- The algebraic full-word IOR envelope obtained by adding the prices of the
output, left, and right opening slots.  This is an accounting quantity, not a
claim that the sampled commitment/BCS layer has already composed the events. -/
noncomputable def matmulBaseFoldIorAlgebraicBudget
    (F : Type*) [Fintype F] (μ κ ν : ℕ) : ℝ :=
  ((μ + ν : ℕ) : ℝ) * (3 / Fintype.card F) +
  ((μ + κ : ℕ) : ℝ) * (3 / Fintype.card F) +
  ((κ + ν : ℕ) : ℝ) * (3 / Fintype.card F)

/-- The three opening dimensions sum to twice the total bit width. -/
theorem matmulBaseFoldIorAlgebraicBudget_eq :
    matmulBaseFoldIorAlgebraicBudget F μ κ ν =
      (2 * ((μ + κ + ν : ℕ) : ℝ)) * (3 / Fintype.card F) := by
  simp only [matmulBaseFoldIorAlgebraicBudget, Nat.cast_add]
  ring

/-- info: 'Minidregg.Assurance.matmul_output_basefold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_output_basefold_sound
/-- info: 'Minidregg.Assurance.matmul_left_basefold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_left_basefold_sound
/-- info: 'Minidregg.Assurance.matmul_right_basefold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_right_basefold_sound

end Minidregg.Assurance
