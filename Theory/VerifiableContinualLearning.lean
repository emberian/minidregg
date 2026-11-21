/-
# `Theory/VerifiableContinualLearning.lean` — Verifiable Continual Fast-Weight Learning & Rank-`r` Subspace Machine Unlearning

**Substrate, said out loud: this is Lean-authored denotational and algebraic metatheory.**
Mathlib + `Theory.ZkmlDeltaNet` imports only (`scripts/check-import-boundary.sh`: `Theory/` tier).
Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.

## What this module proves

Building on `Theory/ZkmlDeltaNet.lean` (`arXiv:2608.30320` Eqs. 1–5), we lift 1-step Gated DeltaNet
(`GDN`) Householder transitions into **Continual Multi-Episode Fast-Weight Learning** and
**Counterfactual Gold-Standard Rank-`r` Subspace Machine Unlearning** over **any commutative ring `R`**
(`ℤ`, `ZMod 2013265921` BabyBear, `ZMod (2^k)` BFV/SPDZ2k rings with zero divisors, etc.):

1. **Part A — Exact Rank-`r` Orthogonal Subspace Unlearning (`gdnErase`, `gdnEraseSeq`)**:
   - `gdnErase k S := gdnStep 1 1 k 0 S` equals left multiplication by the complementary projector
     `orthProjCompl k := 1 - k ⊗ k` (`gdnErase_eq_proj_mul`).
   - **Order-Independent Commutativity (`gdnErase_comm_of_orth`) vs Non-Orthogonal Falsifier
     (`gdnErase_noncomm_of_nonorth`)**: whenever `dotProduct k₁ k₂ = 0` (which over `CommRing R`
     equivalently gives `dotProduct k₂ k₁ = 0`), `gdnErase k₁ (gdnErase k₂ S) = gdnErase k₂ (gdnErase k₁ S)`.
     Dropping orthogonality (`k₁ = ![1, 0]`, `k₂ = ![1, 1]` over `ℤ`) breaks commutativity (`by decide`),
     proving why Gram–Schmidt orthonormalization of concept keys is algebraically mandatory.
   - **Closed-Form Projector Collapse (`gdnEraseSeq_ofFn_eq_subspaceProjCompl` & `gdnEraseSeq_eq_one_sub_basisMatrix_mul`)**:
     for any pairwise-orthonormal family `u : Fin r → (Fin dk → R)` (`Uᵀ * U = 1`), sequential rank-1
     erasure `gdnEraseSeq (List.ofFn u) S` collapses to one-shot matrix projection
     `(1 - ∑ a, u_a ⊗ u_a) * S = (1 - U * Uᵀ) * S` with zero cross-terms.
   - **Full Subspace Annihilation & Orthogonal-Complement Preservation
     (`gdnEraseSeq_annihilates_span` & `gdnEraseSeq_preserves_orth`)**: after `S' = gdnEraseSeq (List.ofFn u) S`,
     every linear combination `x = ∑ a : Fin r, c a • u a` in the `r`-dimensional concept subspace has
     zero readout `(S')ᵀ.mulVec x = 0`, while every orthogonal query `q` (`∀ a, dotProduct (u a) q = 0`)
     retains its exact pre-unlearning readout `(S')ᵀ.mulVec q = Sᵀ.mulVec q`.
   - **Corrupted-Orthogonality Falsifier Tooth (`corrupted_orthogonality_leaves_residual_falsifier`)**:
     duplicating a column in `U` (`Uᵀ * U ≠ 1`) causes `(1 - U * Uᵀ) * S` to negate rather than erase
     the secret association (`((1 - U * Uᵀ) * S)ᵀ * U ≠ 0`), proving why ZK unlearning certificates must
     verify `Uᵀ * U = 1` (or bounded fixed-point Gram error).

2. **Part B — Multi-Episode Stateful Composition (`gdnRun`, `gdnMultiStep_state_associative`)**:
   - Defines `GdnUpdate R dk dv` and sequential multi-step execution `gdnRun`, proving exact episode
     concatenation associativity `gdnRun (ep₁ ++ ep₂) S₀ = gdnRun ep₂ (gdnRun ep₁ S₀)`, affine monoid
     homomorphism `GdnChunkSummary` (`summarizeEpisode_append`, `summarizeEpisode_eval_eq_gdnRun`)
     decomposing stateful chunks into decayed-projected prior state plus zero-state WY summary, and
     concrete kernel-decided witnesses over both `ℤ` and `ZMod 2013265921` (`BabyBear`).

3. **Part C — Exact Post-Adaptation Retroactive Unlearning (`retroactive_unlearn_after_episode`)**:
   - Proves **counterfactual gold-standard machine unlearning** over any `CommRing R`: when forgettable
     episode steps write along keys `k_m ∈ span(u_1, …, u_r)` at `α = 1` arbitrarily interleaved with
     orthogonal retained user steps (`∀ a, dotProduct (u a) q_j = 0`, at arbitrary decay `α_j` and
     write gate `β_j`), applying `gdnEraseSeq (List.ofFn u)` *once* after the entire multi-episode
     session yields:
       (i) **exact counterfactual state** `gdnRun retainedSession (gdnEraseSeq (List.ofFn u) S₀)`
           (identical to `gdnRun retainedSession S₀` whenever `S₀` had no prior component in `span(u)`),
       (ii) **exact counterfactual readout** `(S_unlearned)ᵀ.mulVec q = (gdnRun retainedSession S₀)ᵀ.mulVec q`
            on all surviving queries `q ⊥ span(u)` for *arbitrary* genesis state `S₀` (zero retraining!), and
       (iii) **complete annihilation** `(S_unlearned)ᵀ.mulVec x = 0` on all `x ∈ span(u)`.
   - **Sharpness Teeth (`retroactive_unlearn_nonorth_interference_falsifier` &
     `retroactive_unlearn_decay_falsifier`)**: dropping key orthogonality on subsequent retained updates
     propagates secret values into `span(u)⊥` via residual prediction error `e = v - Sᵀ k`, and dropping
     `α = 1` on forgotten updates scales surviving associations — proving both premises load-bearing.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Theory.ZkmlDeltaNet

namespace Minidregg.Theory.VerifiableContinualLearning

open Matrix Minidregg.Theory.ZkmlDeltaNet

/-! ## Part A. Exact Rank-`r` Orthogonal Subspace Unlearning (`gdnErase`, `gdnEraseSeq`) -/

section SubspaceUnlearning

variable {R : Type*} [CommRing R]

/-- Commutativity of `dotProduct` over any `CommRing R`. -/
theorem dotProduct_symm {n : ℕ} (a b : Fin n → R) :
    dotProduct a b = dotProduct b a :=
  Finset.sum_congr rfl fun i _ => mul_comm (a i) (b i)

/-- Complementary rank-1 Householder/orthogonal projector `1 - k ⊗ k`. -/
def orthProjCompl {dk : ℕ} (k : Fin dk → R) : Matrix (Fin dk) (Fin dk) R :=
  1 - Matrix.vecMulVec k k

/-- **Zero-Value GDN Erasure (`gdnErase`)**: 1-step GDN transition at `α = 1, β = 1, v = 0`. -/
def gdnErase {dk dv : ℕ} (k : Fin dk → R) (S : Matrix (Fin dk) (Fin dv) R) :
    Matrix (Fin dk) (Fin dv) R :=
  gdnStep 1 1 k 0 S

/-- Sequential zero-value erasure across a list of concept keys `ks`. -/
def gdnEraseSeq {dk dv : ℕ} (ks : List (Fin dk → R)) (S : Matrix (Fin dk) (Fin dv) R) :
    Matrix (Fin dk) (Fin dv) R :=
  ks.foldl (fun acc k => gdnErase k acc) S

@[simp]
theorem gdnEraseSeq_nil {dk dv : ℕ} (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq ([] : List (Fin dk → R)) S = S :=
  rfl

@[simp]
theorem gdnEraseSeq_cons {dk dv : ℕ} (k : Fin dk → R) (ks : List (Fin dk → R))
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (k :: ks) S = gdnEraseSeq ks (gdnErase k S) :=
  rfl

theorem gdnEraseSeq_append {dk dv : ℕ} (ks₁ ks₂ : List (Fin dk → R))
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (ks₁ ++ ks₂) S = gdnEraseSeq ks₂ (gdnEraseSeq ks₁ S) :=
  List.foldl_append

/-- **Projector Factorization (`gdnErase_eq_proj_mul`):**
`gdnErase k S` equals left matrix multiplication `(1 - k ⊗ k) * S = orthProjCompl k * S`. -/
theorem gdnErase_eq_proj_mul {dk dv : ℕ} (k : Fin dk → R) (S : Matrix (Fin dk) (Fin dv) R) :
    gdnErase k S = (1 - Matrix.vecMulVec k k) * S := by
  have hv0 : Matrix.vecMulVec k (0 : Fin dv → R) = 0 := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [gdnErase, gdnStep_eq_householder_update, one_smul, one_smul, one_smul, hv0, add_zero]

/-- Outer-product contraction identity `(a ⊗ b) * (c ⊗ d) = (b · c) • (a ⊗ d)` over any `CommRing R`. -/
theorem vecMulVec_mul_vecMulVec {m n p : ℕ}
    (a : Fin m → R) (b : Fin n → R) (c : Fin n → R) (d : Fin p → R) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d =
      dotProduct b c • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    dotProduct, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- When `dotProduct k₁ k₂ = 0`, the product of complementary rank-1 projectors drops its cross term:
`(1 - k₁ ⊗ k₁) * (1 - k₂ ⊗ k₂) = 1 - k₁ ⊗ k₁ - k₂ ⊗ k₂`. -/
theorem orthProjCompl_mul_of_orth {dk : ℕ} (k₁ k₂ : Fin dk → R)
    (horth : dotProduct k₁ k₂ = 0) :
    orthProjCompl k₁ * orthProjCompl k₂ =
      1 - Matrix.vecMulVec k₁ k₁ - Matrix.vecMulVec k₂ k₂ := by
  unfold orthProjCompl
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    vecMulVec_mul_vecMulVec, horth, zero_smul, sub_zero, sub_right_comm]

/-- **Commutativity of Orthogonal Unlearning (`gdnErase_comm_of_orth`):**
Whenever `dotProduct k₁ k₂ = 0` and `dotProduct k₂ k₁ = 0` (note: over `CommRing R`, `h₁₂` and `h₂₁`
are equivalent via `dotProduct_symm`; we accept both as stated in the interface specification),
erasing `k₂` then `k₁` equals erasing `k₁` then `k₂` on every memory matrix `S`. -/
theorem gdnErase_comm_of_orth {dk dv : ℕ} (k₁ k₂ : Fin dk → R)
    (S : Matrix (Fin dk) (Fin dv) R)
    (h₁₂ : dotProduct k₁ k₂ = 0) (h₂₁ : dotProduct k₂ k₁ = 0) :
    gdnErase k₁ (gdnErase k₂ S) = gdnErase k₂ (gdnErase k₁ S) := by
  rw [gdnErase_eq_proj_mul, gdnErase_eq_proj_mul, gdnErase_eq_proj_mul, gdnErase_eq_proj_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (orthProjCompl k₁ * orthProjCompl k₂) * S = (orthProjCompl k₂ * orthProjCompl k₁) * S
  rw [orthProjCompl_mul_of_orth k₁ k₂ h₁₂, orthProjCompl_mul_of_orth k₂ k₁ h₂₁, sub_right_comm]

/-- **Non-Orthogonal Order-Dependence Falsifier (`gdnErase_noncomm_of_nonorth`):**
Over `ℤ`, unorthogonalized keys `k₁ = ![1, 0]` and `k₂ = ![1, 1]` (`dotProduct k₁ k₂ = 1 ≠ 0`)
fail order-independent unlearning on `S = 1`: `gdnErase k₁ (gdnErase k₂ 1) ≠ gdnErase k₂ (gdnErase k₁ 1)`. -/
theorem gdnErase_noncomm_of_nonorth :
    let k₁ : Fin 2 → ℤ := ![1, 0]
    let k₂ : Fin 2 → ℤ := ![1, 1]
    let S : Matrix (Fin 2) (Fin 2) ℤ := 1
    dotProduct k₁ k₂ ≠ 0 ∧
    gdnErase k₁ (gdnErase k₂ S) ≠ gdnErase k₂ (gdnErase k₁ S) := by
  decide

/-- Pairwise-orthonormal `r`-frame `u : Fin r → (Fin dk → R)` over `CommRing R`:
`dotProduct (u a) (u b) = if a = b then 1 else 0`. -/
def IsOrthonormalFamily {r dk : ℕ} (u : Fin r → Fin dk → R) : Prop :=
  ∀ a b : Fin r, dotProduct (u a) (u b) = if a = b then 1 else 0

/-- Closed-form complementary projector `1 - ∑_{a : Fin r} u_a ⊗ u_a` onto `span(u)⊥`. -/
def subspaceProjCompl {r dk : ℕ} (u : Fin r → Fin dk → R) : Matrix (Fin dk) (Fin dk) R :=
  1 - ∑ a : Fin r, Matrix.vecMulVec (u a) (u a)

/-- Helper: if `∀ y ∈ tl, dotProduct k y = 0`, then `(∑_{x ∈ tl} x ⊗ x) * (k ⊗ k) = 0`. -/
theorem list_sum_vecMulVec_mul_eq_zero {dk : ℕ} (k : Fin dk → R) :
    ∀ (tl : List (Fin dk → R)),
      (∀ y ∈ tl, dotProduct k y = 0) →
      (tl.map (fun x => Matrix.vecMulVec x x)).sum * Matrix.vecMulVec k k = 0
  | [], _ => by simp
  | y :: ys, hk_tl => by
      have hyk : dotProduct y k = 0 := by
        rw [dotProduct_symm]
        exact hk_tl y List.mem_cons_self
      have hrest : ∀ z ∈ ys, dotProduct k z = 0 :=
        fun z hz => hk_tl z (List.mem_cons_of_mem y hz)
      simp only [List.map_cons, List.sum_cons, Matrix.add_mul,
        vecMulVec_mul_vecMulVec, hyk, zero_smul, zero_add]
      exact list_sum_vecMulVec_mul_eq_zero k ys hrest

/-- Inductive closed-form collapse for any pairwise-orthogonal list `ks`:
`gdnEraseSeq ks S = (1 - ∑_{x ∈ ks} x ⊗ x) * S`. -/
theorem gdnEraseSeq_eq_one_sub_sum_mul_of_pairwise {dk dv : ℕ}
    (ks : List (Fin dk → R))
    (hpw : ks.Pairwise (fun x y => dotProduct x y = 0))
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq ks S = (1 - (ks.map (fun x => Matrix.vecMulVec x x)).sum) * S := by
  induction ks generalizing S with
  | nil =>
      simp [gdnEraseSeq]
  | cons k tl ih =>
      obtain ⟨hk_tl, hpw_tl⟩ := List.pairwise_cons.mp hpw
      rw [gdnEraseSeq_cons, ih hpw_tl (gdnErase k S), gdnErase_eq_proj_mul, ← Matrix.mul_assoc]
      congr 1
      have hcross := list_sum_vecMulVec_mul_eq_zero k tl hk_tl
      simp only [List.map_cons, List.sum_cons]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hcross, sub_zero,
        sub_sub, add_comm]

/-- **Arbitrary Permutation Order-Independence (`gdnEraseSeq_perm_of_pairwise_orth`):**
Erasing any pairwise-orthogonal list of concept keys `ks₁` produces the **exact same fast-weight
matrix** under ANY permutation `ks₁.Perm ks₂`. -/
theorem gdnEraseSeq_perm_of_pairwise_orth {dk dv : ℕ}
    {ks₁ ks₂ : List (Fin dk → R)}
    (hperm : ks₁.Perm ks₂)
    (hpw₁ : ks₁.Pairwise (fun x y => dotProduct x y = 0))
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq ks₁ S = gdnEraseSeq ks₂ S := by
  have hpw₂ : ks₂.Pairwise (fun x y => dotProduct x y = 0) :=
    (hperm.pairwise_iff (fun h => by rw [dotProduct_symm]; exact h)).mp hpw₁
  rw [gdnEraseSeq_eq_one_sub_sum_mul_of_pairwise ks₁ hpw₁ S,
    gdnEraseSeq_eq_one_sub_sum_mul_of_pairwise ks₂ hpw₂ S,
    (hperm.map (fun x => Matrix.vecMulVec x x)).sum_eq]

/-- Pairwise orthogonality of `List.ofFn u` follows immediately from `IsOrthonormalFamily u`. -/
theorem pairwise_orth_ofFn {r dk : ℕ} {u : Fin r → Fin dk → R}
    (hu : IsOrthonormalFamily u) :
    (List.ofFn u).Pairwise (fun x y => dotProduct x y = 0) := by
  rw [List.pairwise_ofFn]
  intro i j hij
  have hne : i ≠ j := ne_of_lt hij
  simpa [hne] using hu i j

/-- Sum over `List.ofFn f` equals `∑ a : Fin r, f a` in any `AddCommMonoid`. -/
theorem list_sum_ofFn {M : Type*} [AddCommMonoid M] {r : ℕ} (f : Fin r → M) :
    (List.ofFn f).sum = ∑ a : Fin r, f a := by
  rw [List.ofFn_eq_map, ← Fin.sum_univ_def]

/-- **Closed-Form Subspace Projector Theorem (`gdnEraseSeq_ofFn_eq_subspaceProjCompl`):**
For any pairwise-orthonormal family `u : Fin r → (Fin dk → R)`, sequential rank-1 zero-value
erasure `gdnEraseSeq (List.ofFn u) S` equals `(1 - ∑_{a : Fin r} u_a ⊗ u_a) * S`. -/
theorem gdnEraseSeq_ofFn_eq_subspaceProjCompl {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) S = subspaceProjCompl u * S := by
  rw [gdnEraseSeq_eq_one_sub_sum_mul_of_pairwise (List.ofFn u) (pairwise_orth_ofFn hu) S]
  unfold subspaceProjCompl
  have hmap : ((List.ofFn u).map (fun x => Matrix.vecMulVec x x)).sum =
      ∑ a : Fin r, Matrix.vecMulVec (u a) (u a) := by
    rw [List.map_ofFn]
    exact list_sum_ofFn _
  rw [hmap]

/-- Column-basis matrix `U ∈ R^{dk × r}` associated to `u : Fin r → (Fin dk → R)`. -/
def basisMatrix {r dk : ℕ} (u : Fin r → Fin dk → R) : Matrix (Fin dk) (Fin r) R :=
  Matrix.of (fun i a => u a i)

/-- **Gram Matrix Orthonormality Equivalence (`basisMatrix_transpose_mul_eq_one_iff`):**
`(basisMatrix u)ᵀ * basisMatrix u = 1` iff `IsOrthonormalFamily u`. -/
theorem basisMatrix_transpose_mul_eq_one_iff {r dk : ℕ} (u : Fin r → Fin dk → R) :
    (basisMatrix u)ᵀ * basisMatrix u = 1 ↔ IsOrthonormalFamily u := by
  constructor
  · intro h a b
    have hab := congrArg (fun M => M a b) h
    simpa [basisMatrix, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.one_apply] using hab
  · intro hu
    ext a b
    simpa [basisMatrix, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.one_apply] using hu a b

/-- `U * Uᵀ = ∑_{a : Fin r} u_a ⊗ u_a`, bridging sequential `gdnEraseSeq` directly to the ZK
unlearning certificate's rank-`r` matrix equation `S_unlearned = (1 - U * Uᵀ) * S_before`. -/
theorem basisMatrix_mul_transpose_eq_sum {r dk : ℕ} (u : Fin r → Fin dk → R) :
    basisMatrix u * (basisMatrix u)ᵀ = ∑ a : Fin r, Matrix.vecMulVec (u a) (u a) := by
  ext i j
  simp [basisMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply]

theorem gdnEraseSeq_eq_one_sub_basisMatrix_mul {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) S = (1 - basisMatrix u * (basisMatrix u)ᵀ) * S := by
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, subspaceProjCompl,
    basisMatrix_mul_transpose_eq_sum]

/-- Rectangular finite-sum left-distributivity `(∑ a, M a) * N = ∑ a, M a * N`. -/
theorem finset_sum_matrix_mul {ι m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (s : Finset ι) (M : ι → Matrix m n R) (N : Matrix n p R) :
    (s.sum M) * N = s.sum (fun a => M a * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Fundamental readout duality for `subspaceProjCompl`:
`((subspaceProjCompl u * S)ᵀ).mulVec x = Sᵀ.mulVec (x - ∑ a, (dotProduct (u a) x) • u a)`. -/
theorem subspaceProjCompl_mul_transpose_mulVec {r dk dv : ℕ}
    (u : Fin r → Fin dk → R) (S : Matrix (Fin dk) (Fin dv) R) (x : Fin dk → R) :
    (subspaceProjCompl u * S)ᵀ.mulVec x =
      Sᵀ.mulVec (x - ∑ a : Fin r, dotProduct (u a) x • u a) := by
  unfold subspaceProjCompl
  rw [Matrix.sub_mul, Matrix.one_mul, finset_sum_matrix_mul]
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  calc ∑ m : Fin dk, (∑ a : Fin r, ∑ k : Fin dk, u a m * u a k * S k j) * x m
      = ∑ m : Fin dk, ∑ a : Fin r, ∑ k : Fin dk, u a m * u a k * S k j * x m := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
    _ = ∑ a : Fin r, ∑ m : Fin dk, ∑ k : Fin dk, u a m * u a k * S k j * x m :=
          Finset.sum_comm
    _ = ∑ a : Fin r, ∑ k : Fin dk, ∑ m : Fin dk, u a m * u a k * S k j * x m :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k : Fin dk, ∑ a : Fin r, ∑ m : Fin dk, S k j * (u a m * x m * u a k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ k : Fin dk, S k j * ∑ a : Fin r, (∑ m : Fin dk, u a m * x m) * u a k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]

/-- Action of `x ↦ x - ∑ a, (u_a · x) • u_a` on any linear combination `x = ∑ b, c b • u b`:
orthonormality cancels every basis coordinate identically to `0`. -/
theorem orth_decomp_vanishes_on_span {r dk : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u) (c : Fin r → R) :
    (∑ b : Fin r, c b • u b) -
      (∑ a : Fin r, dotProduct (u a) (∑ b : Fin r, c b • u b) • u a) = 0 := by
  have hdot : ∀ a : Fin r, dotProduct (u a) (∑ b : Fin r, c b • u b) = c a := by
    intro a
    have hexp : dotProduct (u a) (∑ b : Fin r, c b • u b) =
        ∑ b : Fin r, c b * dotProduct (u a) (u b) := by
      simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp]
    have hsingle : (∑ b : Fin r, c b * dotProduct (u a) (u b)) =
        ∑ b : Fin r, if a = b then c b else 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hu a b]
      split_ifs <;> ring
    rw [hsingle]
    simp
  have hsum_eq : (∑ a : Fin r, dotProduct (u a) (∑ b : Fin r, c b • u b) • u a) =
      ∑ a : Fin r, c a • u a :=
    Finset.sum_congr rfl fun a _ => by rw [hdot a]
  rw [hsum_eq, sub_self]

/-- **Full Rank-`r` Subspace Annihilation (`gdnEraseSeq_annihilates_span`):**
For any pairwise-orthonormal family `u : Fin r → (Fin dk → R)` and ANY coefficient vector
`c : Fin r → R`, sequential erasure `S' = gdnEraseSeq (List.ofFn u) S` completely erases
the memory readout along `x = ∑ a : Fin r, c a • u a`: `(S')ᵀ.mulVec (∑ a, c a • u a) = 0`. -/
theorem gdnEraseSeq_annihilates_span {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) (c : Fin r → R) :
    (gdnEraseSeq (List.ofFn u) S)ᵀ.mulVec (∑ a : Fin r, c a • u a) = 0 := by
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu,
    subspaceProjCompl_mul_transpose_mulVec,
    orth_decomp_vanishes_on_span hu c]
  ext j
  simp [Matrix.mulVec, dotProduct]

/-- Matrix-certificate corollary (`unlearned_transpose_mul_basisMatrix_eq_zero`):
under `IsOrthonormalFamily u`, `(gdnEraseSeq (List.ofFn u) S)ᵀ * basisMatrix u = 0` identically. -/
theorem unlearned_transpose_mul_basisMatrix_eq_zero {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) :
    (gdnEraseSeq (List.ofFn u) S)ᵀ * basisMatrix u = 0 := by
  ext j b
  let c : Fin r → R := fun a => if a = b then 1 else 0
  have hspan : (∑ a : Fin r, c a • u a) = u b := by
    ext i
    rw [Finset.sum_apply]
    have hterm : (∑ a : Fin r, (c a • u a) i) = ∑ a : Fin r, if a = b then u a i else 0 := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hab : a = b <;> simp [c, hab]
    rw [hterm]
    simp
  have hann := congrArg (fun v => v j) (gdnEraseSeq_annihilates_span hu S c)
  rw [hspan] at hann
  simpa [basisMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hann

/-- **Orthogonal-Complement Exact Preservation (`gdnEraseSeq_preserves_orth`):**
For any pairwise-orthonormal family `u : Fin r → (Fin dk → R)` and any query `q` orthogonal to
all `u a` (`∀ a : Fin r, dotProduct (u a) q = 0`), sequential erasure leaves `q`'s memory readout
identically untouched: `(gdnEraseSeq (List.ofFn u) S)ᵀ.mulVec q = Sᵀ.mulVec q`. -/
theorem gdnEraseSeq_preserves_orth {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) (q : Fin dk → R)
    (hq : ∀ a : Fin r, dotProduct (u a) q = 0) :
    (gdnEraseSeq (List.ofFn u) S)ᵀ.mulVec q = Sᵀ.mulVec q := by
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, subspaceProjCompl_mul_transpose_mulVec]
  have hz : (∑ a : Fin r, dotProduct (u a) q • u a) = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hq a, zero_smul]
  rw [hz, sub_zero]

/-- **Corrupted-Orthogonality Falsifier Tooth (`corrupted_orthogonality_leaves_residual_falsifier`):**
If `U` violates `Uᵀ * U = 1` (e.g., duplicate rank-1 columns `u = ![![1, 0], ![1, 0]]`), then the
putative projection `(1 - U * Uᵀ) * S` negates rather than erases the secret (`S'ᵀ * U = -Sᵀ * U ≠ 0`),
refuting soundness of unlearning certificates that omit the `Uᵀ * U = 1` Gram check! -/
theorem corrupted_orthogonality_leaves_residual_falsifier :
    let u : Fin 2 → Fin 2 → ℤ := ![![1, 0], ![1, 0]]
    let U := basisMatrix u
    let S : Matrix (Fin 2) (Fin 1) ℤ := Matrix.of ![![42], ![7]]
    let S_bad := (1 - U * Uᵀ) * S
    (Uᵀ * U ≠ 1) ∧ (S_badᵀ * U ≠ 0) := by
  decide

end SubspaceUnlearning

/-! ## Part B. Multi-Episode Stateful Composition & Chunkwise Affine Monoid (`gdnRun`) -/

section MultiEpisodeComposition

/-- Single Gated DeltaNet fast-weight event `(α, β, k, v)`. -/
structure GdnUpdate (R : Type*) (dk dv : ℕ) where
  α : R
  β : R
  k : Fin dk → R
  v : Fin dv → R

/-- Multi-step stateful GDN execution across an episode `ep : List (GdnUpdate R dk dv)`. -/
def gdnRun {R : Type*} [CommRing R] {dk dv : ℕ}
    (ep : List (GdnUpdate R dk dv)) (S : Matrix (Fin dk) (Fin dv) R) :
    Matrix (Fin dk) (Fin dv) R :=
  ep.foldl (fun acc u => gdnStep u.α u.β u.k u.v acc) S

@[simp]
theorem gdnRun_nil {R : Type*} [CommRing R] {dk dv : ℕ}
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnRun ([] : List (GdnUpdate R dk dv)) S = S :=
  rfl

@[simp]
theorem gdnRun_cons {R : Type*} [CommRing R] {dk dv : ℕ}
    (u : GdnUpdate R dk dv) (ep : List (GdnUpdate R dk dv))
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnRun (u :: ep) S = gdnRun ep (gdnStep u.α u.β u.k u.v S) :=
  rfl

/-- **Multi-Episode Stateful Fold Associativity (`gdnMultiStep_state_associative`):**
Running concatenated episodes `ep₁ ++ ep₂` from `S₀` equals running `ep₁` to obtain intermediate
persistent memory `S₁ = gdnRun ep₁ S₀` and resuming `ep₂` from `S₁`. -/
theorem gdnMultiStep_state_associative {R : Type*} [CommRing R] {dk dv : ℕ}
    (ep₁ ep₂ : List (GdnUpdate R dk dv)) (S₀ : Matrix (Fin dk) (Fin dv) R) :
    gdnRun (ep₁ ++ ep₂) S₀ = gdnRun ep₂ (gdnRun ep₁ S₀) :=
  List.foldl_append

/-- Affine state-transition summary `S ↦ trans * S + add` of a chunk/episode, decomposing any
stateful chunk (`S₀ ≠ 0`) into its decayed-Householder state transition `trans * S₀` plus its
zero-state WY value accumulation `add = gdnRun ep 0`. -/
structure GdnChunkSummary (R : Type*) (dk dv : ℕ) where
  trans : Matrix (Fin dk) (Fin dk) R
  add : Matrix (Fin dk) (Fin dv) R

/-- Identity summary (`trans = 1`, `add = 0`). -/
def GdnChunkSummary.id {R : Type*} [CommRing R] {dk dv : ℕ} : GdnChunkSummary R dk dv :=
  { trans := 1, add := 0 }

/-- Sequential composition of two chunk summaries (`s₁` followed by `s₂`). -/
def GdnChunkSummary.comp {R : Type*} [CommRing R] {dk dv : ℕ}
    (s₁ s₂ : GdnChunkSummary R dk dv) : GdnChunkSummary R dk dv :=
  { trans := s₂.trans * s₁.trans
    add := s₂.trans * s₁.add + s₂.add }

/-- Evaluate a chunk summary on an arbitrary incoming persistent memory state `S`. -/
def GdnChunkSummary.eval {R : Type*} [CommRing R] {dk dv : ℕ}
    (s : GdnChunkSummary R dk dv) (S : Matrix (Fin dk) (Fin dv) R) :
    Matrix (Fin dk) (Fin dv) R :=
  s.trans * S + s.add

/-- Single-step affine summary matching `gdnStep_eq_householder_update`. -/
def stepSummary {R : Type*} [CommRing R] {dk dv : ℕ}
    (u : GdnUpdate R dk dv) : GdnChunkSummary R dk dv :=
  { trans := u.α • (1 - u.β • Matrix.vecMulVec u.k u.k)
    add := u.β • Matrix.vecMulVec u.k u.v }

/-- Fold an episode into its exact `O(dk² + dk·dv)` affine chunk summary. -/
def summarizeEpisode {R : Type*} [CommRing R] {dk dv : ℕ}
    (ep : List (GdnUpdate R dk dv)) : GdnChunkSummary R dk dv :=
  ep.foldl (fun acc u => GdnChunkSummary.comp acc (stepSummary u)) GdnChunkSummary.id

theorem GdnChunkSummary.comp_assoc {R : Type*} [CommRing R] {dk dv : ℕ}
    (s₁ s₂ s₃ : GdnChunkSummary R dk dv) :
    GdnChunkSummary.comp (GdnChunkSummary.comp s₁ s₂) s₃ =
      GdnChunkSummary.comp s₁ (GdnChunkSummary.comp s₂ s₃) := by
  cases s₁; cases s₂; cases s₃
  simp only [GdnChunkSummary.comp, Matrix.mul_assoc, Matrix.mul_add, add_assoc]

theorem GdnChunkSummary.id_comp {R : Type*} [CommRing R] {dk dv : ℕ}
    (s : GdnChunkSummary R dk dv) :
    GdnChunkSummary.comp GdnChunkSummary.id s = s := by
  cases s
  simp [GdnChunkSummary.comp, GdnChunkSummary.id]

/-- Monoid homomorphism law: `summarizeEpisode (ep₁ ++ ep₂) = comp (summarizeEpisode ep₁) (summarizeEpisode ep₂)`. -/
theorem summarizeEpisode_append {R : Type*} [CommRing R] {dk dv : ℕ}
    (ep₁ ep₂ : List (GdnUpdate R dk dv)) :
    summarizeEpisode (ep₁ ++ ep₂) =
      GdnChunkSummary.comp (summarizeEpisode ep₁) (summarizeEpisode ep₂) := by
  have hgen : ∀ (acc : GdnChunkSummary R dk dv),
      ep₂.foldl (fun a u => GdnChunkSummary.comp a (stepSummary u)) acc =
        GdnChunkSummary.comp acc (summarizeEpisode ep₂) := by
    induction ep₂ with
    | nil =>
        intro acc
        cases acc
        simp [summarizeEpisode, GdnChunkSummary.comp, GdnChunkSummary.id]
    | cons u tl ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih (GdnChunkSummary.comp acc (stepSummary u))]
        have h1 : summarizeEpisode (u :: tl) =
            tl.foldl (fun a v => GdnChunkSummary.comp a (stepSummary v)) (stepSummary u) := by
          simp only [summarizeEpisode, List.foldl_cons, GdnChunkSummary.id_comp]
        rw [h1, ih (stepSummary u), GdnChunkSummary.comp_assoc]
  unfold summarizeEpisode
  rw [List.foldl_append]
  exact hgen _

theorem GdnChunkSummary.eval_comp {R : Type*} [CommRing R] {dk dv : ℕ}
    (s₁ s₂ : GdnChunkSummary R dk dv) (S : Matrix (Fin dk) (Fin dv) R) :
    (GdnChunkSummary.comp s₁ s₂).eval S = s₂.eval (s₁.eval S) := by
  simp only [GdnChunkSummary.eval, GdnChunkSummary.comp, Matrix.mul_add,
    Matrix.mul_assoc, add_assoc]

/-- **Stateful Chunk Summary Equivalence (`summarizeEpisode_eval_eq_gdnRun`):**
Evaluating `summarizeEpisode ep` on ANY prior memory `S₀` equals sequential execution `gdnRun ep S₀`,
so `gdnRun ep S₀ = (summarizeEpisode ep).trans * S₀ + gdnRun ep 0`. -/
theorem summarizeEpisode_eval_eq_gdnRun {R : Type*} [CommRing R] {dk dv : ℕ}
    (ep : List (GdnUpdate R dk dv)) (S₀ : Matrix (Fin dk) (Fin dv) R) :
    (summarizeEpisode ep).eval S₀ = gdnRun ep S₀ := by
  have hgen : ∀ (acc : GdnChunkSummary R dk dv),
      (ep.foldl (fun a u => GdnChunkSummary.comp a (stepSummary u)) acc).eval S₀ =
        gdnRun ep (acc.eval S₀) := by
    induction ep with
    | nil =>
        intro acc
        rfl
    | cons u tl ih =>
        intro acc
        simp only [List.foldl_cons, gdnRun_cons]
        rw [ih (GdnChunkSummary.comp acc (stepSummary u)), GdnChunkSummary.eval_comp]
        have hstep : (stepSummary u).eval (acc.eval S₀) =
            gdnStep u.α u.β u.k u.v (acc.eval S₀) := by
          rw [gdnStep_eq_householder_update, stepSummary, GdnChunkSummary.eval,
            Matrix.smul_mul]
        rw [hstep]
  simpa [summarizeEpisode, GdnChunkSummary.id, GdnChunkSummary.eval] using
    hgen GdnChunkSummary.id

/-- **Satisfying Multi-Episode Witness over `ℤ` (`gdnMultiStep_witness_int`):**
Concrete 2-episode continual fast-weight session over `ℤ` verifying both `gdnMultiStep_state_associative`
and `summarizeEpisode_eval_eq_gdnRun` on non-zero initial memory `S₀`. -/
theorem gdnMultiStep_witness_int :
    let ep₁ : List (GdnUpdate ℤ 2 2) :=
      [ { α := 1, β := 1, k := ![1, 0], v := ![10, -3] },
        { α := 2, β := 1, k := ![0, 1], v := ![4, 7] } ]
    let ep₂ : List (GdnUpdate ℤ 2 2) :=
      [ { α := 1, β := 2, k := ![1, 1], v := ![-2, 5] } ]
    let S₀ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![3, 1], ![4, -2]]
    gdnRun (ep₁ ++ ep₂) S₀ = gdnRun ep₂ (gdnRun ep₁ S₀) ∧
    (summarizeEpisode (ep₁ ++ ep₂)).eval S₀ = gdnRun (ep₁ ++ ep₂) S₀ ∧
    gdnRun ep₁ S₀ ≠ S₀ := by
  decide

/-- BabyBear prime `p = 15 · 2^27 + 1 = 2013265921`. -/
abbrev BabyBearMod : ℕ := 2013265921

/-- **Satisfying Multi-Episode Witness over BabyBear `ZMod 2013265921` (`gdnMultiStep_witness_babybear`):**
Kernel-decided multi-episode continual adaptation + rank-2 orthogonal unlearning witness directly
over the native Rust prover's field `ZMod 2013265921`! -/
theorem gdnMultiStep_witness_babybear :
    let epA : List (GdnUpdate (ZMod BabyBearMod) 3 2) :=
      [ { α := 1, β := 1, k := ![1, 0, 0], v := ![123456, 654321] } ]
    let epB : List (GdnUpdate (ZMod BabyBearMod) 3 2) :=
      [ { α := 1, β := 1, k := ![0, 1, 0], v := ![999999, 777777] },
        { α := 1, β := 1, k := ![0, 0, 1], v := ![888888, 111111] } ]
    let S₀ : Matrix (Fin 3) (Fin 2) (ZMod BabyBearMod) := 0
    let S₂ := gdnRun (epA ++ epB) S₀
    let uB : Fin 2 → Fin 3 → ZMod BabyBearMod := ![![0, 1, 0], ![0, 0, 1]]
    let S_unl := gdnEraseSeq (List.ofFn uB) S₂
    S₂ = gdnRun epB (gdnRun epA S₀) ∧
    (S_unl)ᵀ.mulVec ![0, 1, 0] = 0 ∧
    (S_unl)ᵀ.mulVec ![0, 0, 1] = 0 ∧
    (S_unl)ᵀ.mulVec ![1, 0, 0] = ![123456, 654321] ∧
    S_unl = gdnRun epA S₀ := by
  decide

end MultiEpisodeComposition

/-! ## Part C. Counterfactual Gold-Standard Retroactive Unlearning (`retroactive_unlearn_after_episode`) -/

section RetroactiveUnlearning

variable {R : Type*} [CommRing R]

/-- Left-multiplying `(k ⊗ w)` by `subspaceProjCompl u` annihilates the outer product whenever
`k = ∑ a, c a • u a` lies in `span(u)`. -/
theorem subspaceProjCompl_mul_vecMulVec_of_span {r dk m : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (c : Fin r → R) (w : Fin m → R) :
    subspaceProjCompl u * Matrix.vecMulVec (∑ a : Fin r, c a • u a) w = 0 := by
  let k := ∑ a : Fin r, c a • u a
  unfold subspaceProjCompl
  rw [Matrix.sub_mul, Matrix.one_mul, finset_sum_matrix_mul]
  have hsum : (∑ a : Fin r, Matrix.vecMulVec (u a) (u a) * Matrix.vecMulVec k w) =
      Matrix.vecMulVec (∑ a : Fin r, dotProduct (u a) k • u a) w := by
    ext i j
    simp only [vecMulVec_mul_vecMulVec, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => (mul_assoc _ _ _).symm
  rw [hsum]
  have hvan : k - ∑ a : Fin r, dotProduct (u a) k • u a = 0 :=
    orth_decomp_vanishes_on_span hu c
  have keq : k = ∑ a : Fin r, dotProduct (u a) k • u a := sub_eq_zero.mp hvan
  rw [← keq, sub_self]

/-- **Forgettable-Step Absorption Lemma (`gdnEraseSeq_absorbs_span_step`):**
When an episode writes along ANY key `k = ∑ a, c a • u a` in `span(u)` (at `α = 1`, with arbitrary
write gate `β` and arbitrary value `v`), applying `gdnEraseSeq (List.ofFn u)` absorbs the update
completely: `gdnEraseSeq (List.ofFn u) (gdnStep 1 β (∑ a, c a • u a) v S) = gdnEraseSeq (List.ofFn u) S`! -/
theorem gdnEraseSeq_absorbs_span_step {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (β : R) (c : Fin r → R) (v : Fin dv → R) (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) (gdnStep 1 β (∑ a : Fin r, c a • u a) v S) =
      gdnEraseSeq (List.ofFn u) S := by
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, gdnEraseSeq_ofFn_eq_subspaceProjCompl hu,
    gdnStep_eq_householder_update, one_smul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.mul_assoc (subspaceProjCompl u),
    subspaceProjCompl_mul_vecMulVec_of_span hu c,
    subspaceProjCompl_mul_vecMulVec_of_span hu c v,
    Matrix.zero_mul, smul_zero, sub_zero, add_zero]

/-- **Orthogonal-Step Commutation Lemma (`gdnEraseSeq_comm_orth_step`):**
For ANY step whose key `q` is orthogonal to `span(u)` (`∀ a, dotProduct (u a) q = 0`), with
**arbitrary** decay `α ∈ R` and **arbitrary** write gate `β ∈ R`, `gdnEraseSeq (List.ofFn u)`
commutes past `gdnStep α β q v`! -/
theorem gdnEraseSeq_comm_orth_step {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (α β : R) (q : Fin dk → R) (v : Fin dv → R)
    (S : Matrix (Fin dk) (Fin dv) R)
    (hq : ∀ a : Fin r, dotProduct (u a) q = 0) :
    gdnEraseSeq (List.ofFn u) (gdnStep α β q v S) =
      gdnStep α β q v (gdnEraseSeq (List.ofFn u) S) := by
  have hPq_L : subspaceProjCompl u * Matrix.vecMulVec q q = Matrix.vecMulVec q q := by
    unfold subspaceProjCompl
    rw [Matrix.sub_mul, Matrix.one_mul, Finset.sum_mul]
    have hz : (∑ a : Fin r, Matrix.vecMulVec (u a) (u a) * Matrix.vecMulVec q q) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [vecMulVec_mul_vecMulVec, hq a, zero_smul]
    rw [hz, sub_zero]
  have hPq_R : Matrix.vecMulVec q q * subspaceProjCompl u = Matrix.vecMulVec q q := by
    unfold subspaceProjCompl
    rw [Matrix.mul_sub, Matrix.mul_one, Finset.mul_sum]
    have hz : (∑ a : Fin r, Matrix.vecMulVec q q * Matrix.vecMulVec (u a) (u a)) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        have hqu : dotProduct q (u a) = 0 := by rw [dotProduct_symm]; exact hq a
        rw [vecMulVec_mul_vecMulVec, hqu, zero_smul]
    rw [hz, sub_zero]
  have hPv : subspaceProjCompl u * Matrix.vecMulVec q v = Matrix.vecMulVec q v := by
    unfold subspaceProjCompl
    rw [Matrix.sub_mul, Matrix.one_mul, finset_sum_matrix_mul]
    have hz : (∑ a : Fin r, Matrix.vecMulVec (u a) (u a) * Matrix.vecMulVec q v) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [vecMulVec_mul_vecMulVec, hq a, zero_smul]
    rw [hz, sub_zero]
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, gdnEraseSeq_ofFn_eq_subspaceProjCompl hu,
    gdnStep_eq_householder_update, gdnStep_eq_householder_update]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hPv,
    Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
    ← Matrix.mul_assoc (subspaceProjCompl u) (Matrix.vecMulVec q q) S, hPq_L]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_assoc (Matrix.vecMulVec q q) (subspaceProjCompl u) S, hPq_R]

/-- Tagged continual-session step: either a forgettable episode update along `∑ a, c a • u a`
(at `α = 1`, gate `β`, value `v`) or a retained user episode update `(α, β, q, v)`. -/
inductive SessionStep (R : Type*) (r dk dv : ℕ) where
  | forget (β : R) (c : Fin r → R) (v : Fin dv → R)
  | retain (α β : R) (q : Fin dk → R) (v : Fin dv → R)

/-- Predicate stating all `.retain` steps in `session` use keys orthogonal to `span(u)`. -/
def AllRetainedOrth {r dk dv : ℕ} (u : Fin r → Fin dk → R) :
    List (SessionStep R r dk dv) → Prop
  | [] => True
  | .forget _ _ _ :: rest => AllRetainedOrth u rest
  | .retain _ _ q _ :: rest => (∀ a : Fin r, dotProduct (u a) q = 0) ∧ AllRetainedOrth u rest

/-- Lower a full interleaved session (including forgettable Episode B steps) to `List (GdnUpdate R dk dv)`. -/
def fullSessionUpdates {r dk dv : ℕ} (u : Fin r → Fin dk → R) :
    List (SessionStep R r dk dv) → List (GdnUpdate R dk dv)
  | [] => []
  | .forget β c v :: rest =>
      { α := 1, β := β, k := ∑ a : Fin r, c a • u a, v := v } :: fullSessionUpdates u rest
  | .retain α β q v :: rest =>
      { α := α, β := β, k := q, v := v } :: fullSessionUpdates u rest

/-- Counterfactual training stream `D \ D_forget`: drops all `.forget` steps, keeping only `.retain`! -/
def counterfactualUpdates {r dk dv : ℕ} :
    List (SessionStep R r dk dv) → List (GdnUpdate R dk dv)
  | [] => []
  | .forget _ _ _ :: rest => counterfactualUpdates rest
  | .retain α β q v :: rest => { α := α, β := β, k := q, v := v } :: counterfactualUpdates rest

/-- Inductive commutation of `gdnEraseSeq (List.ofFn u)` with any all-orthogonal `gdnRun` stream. -/
theorem gdnEraseSeq_comm_counterfactual {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (session : List (SessionStep R r dk dv))
    (horth : AllRetainedOrth u session)
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) (gdnRun (counterfactualUpdates session) S) =
      gdnRun (counterfactualUpdates session) (gdnEraseSeq (List.ofFn u) S) := by
  induction session generalizing S with
  | nil => rfl
  | cons st rest ih =>
      cases st with
      | forget β c v =>
          exact ih horth S
      | retain α β q v =>
          obtain ⟨hq, hrest⟩ := horth
          simp only [counterfactualUpdates, gdnRun_cons]
          rw [ih hrest (gdnStep α β q v S), gdnEraseSeq_comm_orth_step hu α β q v S hq]

/-- **Exact Counterfactual State Theorem (`retroactive_unlearn_state_eq_counterfactual`):**
Applying `gdnEraseSeq (List.ofFn u)` *once* after running `fullSessionUpdates u session` produces
the **exact** matrix `gdnRun (counterfactualUpdates session) (gdnEraseSeq (List.ofFn u) S₀)`! -/
theorem retroactive_unlearn_state_eq_counterfactual {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (session : List (SessionStep R r dk dv))
    (horth : AllRetainedOrth u session)
    (S₀ : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) (gdnRun (fullSessionUpdates u session) S₀) =
      gdnRun (counterfactualUpdates session) (gdnEraseSeq (List.ofFn u) S₀) := by
  induction session generalizing S₀ with
  | nil => rfl
  | cons st rest ih =>
      cases st with
      | forget β c v =>
          simp only [fullSessionUpdates, counterfactualUpdates, gdnRun_cons]
          rw [ih horth, gdnEraseSeq_absorbs_span_step hu β c v S₀]
      | retain α β q v =>
          obtain ⟨hq, hrest⟩ := horth
          simp only [fullSessionUpdates, counterfactualUpdates, gdnRun_cons]
          rw [ih hrest, gdnEraseSeq_comm_orth_step hu α β q v S₀ hq]

/-- **Main Theorem — Counterfactual Gold-Standard Retroactive Unlearning (`retroactive_unlearn_after_episode`):**
Over ANY `CommRing R` and for ANY initial memory `S₀` (even with arbitrary pre-existing state!),
if an episode wrote associations along keys in `span(u₁, …, uᵣ)` (at `α = 1`) arbitrarily
interleaved with orthogonal user episodes (`AllRetainedOrth u session`), then applying
`gdnEraseSeq (List.ofFn u)` *after* the entire multi-episode session simultaneously guarantees:
1. **Counterfactual Exactness on All Surviving Queries**: for every query `q ⊥ span(u)`,
   `(S_unlearned)ᵀ.mulVec q = (gdnRun (counterfactualUpdates session) S₀)ᵀ.mulVec q` — **identical**
   to having NEVER trained on the unlearned episode at all (`0` retraining from genesis!).
2. **Complete Subspace Annihilation**: for every linear combination `x = ∑ a, c a • u a ∈ span(u)`,
   `(S_unlearned)ᵀ.mulVec x = 0`.
3. **Full Matrix Equality from Clean Genesis (`S₀ = 0`)**: when `S₀ = 0`, `S_unlearned` equals
   `gdnRun (counterfactualUpdates session) 0` entry-for-entry across all `dk × dv` fast-weights! -/
theorem retroactive_unlearn_after_episode {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (session : List (SessionStep R r dk dv))
    (horth : AllRetainedOrth u session)
    (S₀ : Matrix (Fin dk) (Fin dv) R) :
    (∀ q : Fin dk → R, (∀ a : Fin r, dotProduct (u a) q = 0) →
      (gdnEraseSeq (List.ofFn u) (gdnRun (fullSessionUpdates u session) S₀))ᵀ.mulVec q =
        (gdnRun (counterfactualUpdates session) S₀)ᵀ.mulVec q) ∧
    (∀ c : Fin r → R,
      (gdnEraseSeq (List.ofFn u) (gdnRun (fullSessionUpdates u session) S₀))ᵀ.mulVec
        (∑ a : Fin r, c a • u a) = 0) ∧
    (gdnEraseSeq (List.ofFn u) (gdnRun (fullSessionUpdates u session) 0) =
      gdnRun (counterfactualUpdates session) 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [retroactive_unlearn_state_eq_counterfactual hu session horth S₀,
      ← gdnEraseSeq_comm_counterfactual hu session horth S₀,
      gdnEraseSeq_preserves_orth hu _ q hq]
  · intro c
    exact gdnEraseSeq_annihilates_span hu _ c
  · have h0 : gdnEraseSeq (List.ofFn u) (0 : Matrix (Fin dk) (Fin dv) R) = 0 := by
      rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, Matrix.mul_zero]
    rw [retroactive_unlearn_state_eq_counterfactual hu session horth 0, h0]

/-- **Idempotence of Rank-`r` Subspace Unlearning (`gdnEraseSeq_idempotent`):**
Re-applying `gdnEraseSeq (List.ofFn u)` to an already-unlearned state is an exact ring identity
(`P² = P`), making repeated delete/GDPR requests algebraically idempotent. -/
theorem gdnEraseSeq_idempotent {r dk dv : ℕ}
    {u : Fin r → Fin dk → R} (hu : IsOrthonormalFamily u)
    (S : Matrix (Fin dk) (Fin dv) R) :
    gdnEraseSeq (List.ofFn u) (gdnEraseSeq (List.ofFn u) S) =
      gdnEraseSeq (List.ofFn u) S := by
  rw [gdnEraseSeq_ofFn_eq_subspaceProjCompl hu, gdnEraseSeq_ofFn_eq_subspaceProjCompl hu,
    ← Matrix.mul_assoc]
  congr 1
  have hsub : subspaceProjCompl u * (∑ b : Fin r, Matrix.vecMulVec (u b) (u b)) = 0 := by
    rw [Matrix.mul_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    let c : Fin r → R := fun a => if a = b then 1 else 0
    have hb : u b = ∑ a : Fin r, c a • u a := by
      ext i
      rw [Finset.sum_apply]
      have ht : (∑ a : Fin r, (c a • u a) i) = ∑ a : Fin r, if a = b then u a i else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hab : a = b <;> simp [c, hab]
      rw [ht]
      simp
    conv_lhs => rw [hb]
    exact subspaceProjCompl_mul_vecMulVec_of_span hu c _
  calc subspaceProjCompl u * subspaceProjCompl u
      = subspaceProjCompl u * (1 - ∑ b : Fin r, Matrix.vecMulVec (u b) (u b)) := rfl
    _ = subspaceProjCompl u - subspaceProjCompl u * (∑ b : Fin r, Matrix.vecMulVec (u b) (u b)) := by
          rw [Matrix.mul_sub, Matrix.mul_one]
    _ = subspaceProjCompl u := by rw [hsub, sub_zero]

/-- **Satisfying 3-Episode Witness (`retroactive_unlearn_three_episode_witness`):**
Episode A (`retain`) -> Episode B (`forget`, writing along mixed non-unit combinations `2u₀ - 3u₁`
and `-u₀ + 4u₁`) -> Episode C (`retain`): post-hoc `gdnEraseSeq` recovers counterfactual `Train(A+C)`
entry-for-entry! -/
theorem retroactive_unlearn_three_episode_witness :
    let u : Fin 2 → Fin 4 → ℤ := ![![1, 0, 0, 0], ![0, 1, 0, 0]]
    let session : List (SessionStep ℤ 2 4 2) :=
      [ .retain 1 1 ![0, 0, 1, 0] ![17, -9],
        .forget 1 ![2, -3] ![55, 66],
        .forget 2 ![-1, 4] ![-77, 88],
        .retain 1 1 ![0, 0, 0, 1] ![42, 13] ]
    let S_all := gdnRun (fullSessionUpdates u session) 0
    let S_cf := gdnRun (counterfactualUpdates session) 0
    let S_unl := gdnEraseSeq (List.ofFn u) S_all
    IsOrthonormalFamily u ∧
    AllRetainedOrth u session ∧
    S_all ≠ S_cf ∧
    S_unl = S_cf ∧
    (S_unl)ᵀ.mulVec ![2, -3, 0, 0] = 0 ∧
    (S_unl)ᵀ.mulVec ![0, 0, 1, 0] = ![17, -9] ∧
    (S_unl)ᵀ.mulVec ![0, 0, 0, 1] = ![42, 13] := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro a b
    fin_cases a <;> fin_cases b <;> decide
  · refine ⟨?_, ?_, trivial⟩ <;> (intro a; fin_cases a <;> decide)

/-- **Unit-Norm Pythagorean Falsifier over BabyBear (`gdnErase_noncomm_unit_babybear`):**
Isolates non-orthogonality alone (with BOTH keys strictly unit-norm `k · k = 1`!):
`k₁ = ![1, 0]` and `k₂ = ![3·5⁻¹, 4·5⁻¹] = ![805306369, 402653185]` over `ZMod 2013265921`
satisfy `k₁ · k₁ = 1 ∧ k₂ · k₂ = 1`, yet `k₁ · k₂ ≠ 0` breaks order-independent unlearning! -/
theorem gdnErase_noncomm_unit_babybear :
    let k₁ : Fin 2 → ZMod BabyBearMod := ![1, 0]
    let k₂ : Fin 2 → ZMod BabyBearMod := ![805306369, 402653185]
    let S : Matrix (Fin 2) (Fin 2) (ZMod BabyBearMod) := 1
    dotProduct k₁ k₁ = 1 ∧
    dotProduct k₂ k₂ = 1 ∧
    dotProduct k₁ k₂ ≠ 0 ∧
    gdnErase k₁ (gdnErase k₂ S) ≠ gdnErase k₂ (gdnErase k₁ S) := by
  decide

/-- **Sharpness Falsifier 1 — Non-Orthogonal Cross-Episode Contamination
(`retroactive_unlearn_nonorth_interference_falsifier`):**
Drop `AllRetainedOrth`: Episode B writes secret `v_B = ![100]` along `u₀ = ![1, 0]`, and later
Episode C writes `v_C = ![0]` along overlapping key `q_C = ![1, 1]` (`u₀ · q_C = 1 ≠ 0`). Residual
error `e_C = 0 - 100 = -100` leaks Episode B's secret into the orthogonal coordinate `![0, 1]`, so
post-hoc erasure of `u₀` yields `![-100] ≠ ![0]` on surviving query `q = ![0, 1]`! -/
theorem retroactive_unlearn_nonorth_interference_falsifier :
    let u : Fin 1 → Fin 2 → ℤ := ![![1, 0]]
    let epB : GdnUpdate ℤ 2 1 := { α := 1, β := 1, k := ![1, 0], v := ![100] }
    let epC_overlap : GdnUpdate ℤ 2 1 := { α := 1, β := 1, k := ![1, 1], v := ![0] }
    let q_surv : Fin 2 → ℤ := ![0, 1]
    let S_full := gdnRun [epB, epC_overlap] 0
    let S_unl := gdnEraseSeq (List.ofFn u) S_full
    let S_cf := gdnRun [epC_overlap] 0
    dotProduct (u 0) epC_overlap.k ≠ 0 ∧
    dotProduct (u 0) q_surv = 0 ∧
    (S_unl)ᵀ.mulVec q_surv ≠ (S_cf)ᵀ.mulVec q_surv := by
  decide

/-- **Sharpness Falsifier 2 — Non-Unit Decay on Forgotten Episode (`retroactive_unlearn_decay_falsifier`):**
Drop `α = 1` on a forgotten step (`α_B = 2`): even when keys are strictly orthogonal, the forgotten
step scales prior Episode A associations by `2`, so post-hoc erasure yields `![20] ≠ ![10]` vs
counterfactual `Train(A)`. -/
theorem retroactive_unlearn_decay_falsifier :
    let u : Fin 1 → Fin 2 → ℤ := ![![1, 0]]
    let epA : GdnUpdate ℤ 2 1 := { α := 1, β := 1, k := ![0, 1], v := ![10] }
    let epB_decay : GdnUpdate ℤ 2 1 := { α := 2, β := 1, k := ![1, 0], v := ![99] }
    let q_surv : Fin 2 → ℤ := ![0, 1]
    let S_unl := gdnEraseSeq (List.ofFn u) (gdnRun [epA, epB_decay] 0)
    let S_cf := gdnRun [epA] 0
    (S_unl)ᵀ.mulVec q_surv ≠ (S_cf)ᵀ.mulVec q_surv := by
  decide

end RetroactiveUnlearning

/-! ## Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnErase_eq_proj_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnErase_eq_proj_mul
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.vecMulVec_mul_vecMulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms vecMulVec_mul_vecMulVec
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnErase_comm_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnErase_comm_of_orth
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnErase_noncomm_of_nonorth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnErase_noncomm_of_nonorth
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_ofFn_eq_subspaceProjCompl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_ofFn_eq_subspaceProjCompl
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.basisMatrix_transpose_mul_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basisMatrix_transpose_mul_eq_one_iff
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_eq_one_sub_basisMatrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_eq_one_sub_basisMatrix_mul
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_annihilates_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_annihilates_span
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.unlearned_transpose_mul_basisMatrix_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unlearned_transpose_mul_basisMatrix_eq_zero
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_preserves_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_preserves_orth
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.corrupted_orthogonality_leaves_residual_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms corrupted_orthogonality_leaves_residual_falsifier
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnMultiStep_state_associative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnMultiStep_state_associative
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.GdnChunkSummary.comp_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GdnChunkSummary.comp_assoc
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.summarizeEpisode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms summarizeEpisode_append
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnErase_noncomm_unit_babybear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnErase_noncomm_unit_babybear
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.summarizeEpisode_eval_eq_gdnRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms summarizeEpisode_eval_eq_gdnRun
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnMultiStep_witness_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnMultiStep_witness_int
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnMultiStep_witness_babybear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnMultiStep_witness_babybear
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_absorbs_span_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_absorbs_span_step
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_comm_orth_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_comm_orth_step
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.retroactive_unlearn_state_eq_counterfactual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retroactive_unlearn_state_eq_counterfactual
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_perm_of_pairwise_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_perm_of_pairwise_orth
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.gdnEraseSeq_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnEraseSeq_idempotent
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.retroactive_unlearn_three_episode_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retroactive_unlearn_three_episode_witness
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.retroactive_unlearn_after_episode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retroactive_unlearn_after_episode
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.retroactive_unlearn_nonorth_interference_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retroactive_unlearn_nonorth_interference_falsifier
/-- info: 'Minidregg.Theory.VerifiableContinualLearning.retroactive_unlearn_decay_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retroactive_unlearn_decay_falsifier

end Minidregg.Theory.VerifiableContinualLearning
