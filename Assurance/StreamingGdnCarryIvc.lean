/-
# `Assurance/StreamingGdnCarryIvc.lean` — Continuous Wearable JITT Multi-Chunk `Qwen3.5` Gated-DeltaNet State Carry (`S_c -> S_{c+1}`)

**Rainbows End Wearable SHE Organ #2 (Continuous All-Day JITT Agent Cognition).**
Closes Wave-8 `§4 [OPEN]` item 3 (*"cross-chunk recurrent GDN state carry `S_{chunk,c} -> S_{chunk,c+1}`
beyond `S_{init} = 0`"*). Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.

1. **Stateful Multi-Chunk WY-to-Sequential Equivalence (`§1`)**: `wyStatefulChunk_eq_sequential_gdn`,
   `wyStatefulReadout_eq_sequential_readout`, and `chunkedGdnChain_eq_sequential_gdn` prove over ANY
   `CommRing R` that `S_{c+1} = γ_c • S_c + V_cᵀ * U_{wy,c}` with `(1 + L_c) * U_{wy,c} = V_{β,c} - K_{dec,c} * S_c`
   equals exact unchunked token-by-token `gdnStep` evolution across `C · L_chunk` tokens.
2. **Commitment-Chained Receipts, `O(1)` Verifier RAM, & `C · ε_chunk` Union Bound (`§2`)**:
   `CarryVerifierState.byteFootprint_const`, `streamingCarryChain_eq_or_collision` (`cSHAKE256`),
   and `streamingCarryChain_soundness_union_bound` (`≤ (C : ℚ) * ε_chunk`).
3. **Exact `TVD = 0` Inter-Chunk Handoff (`§3`)**: `dualMaskHandoff_bijective`, `handoffTVD_eq_zero`,
   `babyBearExt4_handoffTVD_eq_zero`, and `dualMaskHandoff_binding_of_isUnit`.
4. **Witnesses & Four `#tooth` Falsifiers (`§4`)**: `tooth_silent_s_init_zero_reset`,
   `tooth_chunk_reorder_splice`, `tooth_dropped_kc_sc_wy_coupling`, `tooth_reused_single_mask_breaks_tvd_zero`.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theory.StreamCodec
import Theory.ZkmlDeltaNet
import Selvage.BabyBearExt4
import Compiler.Tower256CshakeMerkleBinding
import Compiler.Tower256CoordinateMerkle

namespace Minidregg.Assurance.StreamingGdnCarryIvc

open Matrix Minidregg.Theory.ZkmlDeltaNet
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Compiler.Tower256CshakeMerkleBinding (FramedXofCollision)
open Minidregg.Compiler.Tower256CoordinateMerkle (cshakeC)

set_option autoImplicit false

/-! ## §1. Stateful Multi-Chunk Gated-DeltaNet WY Recurrence over Any `CommRing` -/

section StatefulChunkWY

structure GdnToken (R : Type*) (dk dv : ℕ) where
  α : R
  β : R
  k : Fin dk → R
  v : Fin dv → R
  q : Fin dk → R

def gdnSeqList {R : Type*} [CommRing R] {dk dv : ℕ}
    (tokens : List (GdnToken R dk dv)) (S₀ : Matrix (Fin dk) (Fin dv) R) :
    Matrix (Fin dk) (Fin dv) R :=
  tokens.foldl (fun S tok => gdnStep tok.α tok.β tok.k tok.v S) S₀

@[simp] theorem gdnSeqList_nil {R : Type*} [CommRing R] {dk dv : ℕ}
    (S₀ : Matrix (Fin dk) (Fin dv) R) : gdnSeqList ([] : List (GdnToken R dk dv)) S₀ = S₀ := rfl

@[simp] theorem gdnSeqList_cons {R : Type*} [CommRing R] {dk dv : ℕ}
    (tok : GdnToken R dk dv) (tokens : List (GdnToken R dk dv)) (S₀ : Matrix (Fin dk) (Fin dv) R) :
    gdnSeqList (tok :: tokens) S₀ = gdnSeqList tokens (gdnStep tok.α tok.β tok.k tok.v S₀) := rfl

theorem gdnSeqList_append {R : Type*} [CommRing R] {dk dv : ℕ}
    (xs ys : List (GdnToken R dk dv)) (S₀ : Matrix (Fin dk) (Fin dv) R) :
    gdnSeqList (xs ++ ys) S₀ = gdnSeqList ys (gdnSeqList xs S₀) := List.foldl_append

def finPrefixList {A : Type*} {L : ℕ} (chunk : Fin L → A) : (n : ℕ) → n ≤ L → List A
  | 0, _ => []
  | n + 1, hn => finPrefixList chunk n (Nat.le_of_succ_le hn) ++ [chunk ⟨n, hn⟩]

theorem finPrefixList_length {A : Type*} {L : ℕ} (chunk : Fin L → A) :
    ∀ (n : ℕ) (hn : n ≤ L), (finPrefixList chunk n hn).length = n
  | 0, _ => rfl
  | n + 1, hn => by simp [finPrefixList, finPrefixList_length chunk n (Nat.le_of_succ_le hn)]

theorem finPrefixList_getElem {A : Type*} {L : ℕ} (chunk : Fin L → A) :
    ∀ (n : ℕ) (hn : n ≤ L) (i : ℕ) (hi : i < (finPrefixList chunk n hn).length),
      (finPrefixList chunk n hn)[i]'hi =
        chunk ⟨i, Nat.lt_of_lt_of_le (by simpa [finPrefixList_length] using hi) hn⟩
  | 0, _, i, hi => by simp [finPrefixList] at hi
  | n + 1, hn, i, hi => by
      have hi' : i < n + 1 := by simpa [finPrefixList_length] using hi
      simp only [finPrefixList]
      by_cases hlt : i < n
      · have hlt_len : i < (finPrefixList chunk n (Nat.le_of_succ_le hn)).length := by
          simpa [finPrefixList_length] using hlt
        rw [List.getElem_append_left hlt_len]
        exact finPrefixList_getElem chunk n (Nat.le_of_succ_le hn) i hlt_len
      · obtain rfl : i = n := by omega
        have hge : (finPrefixList chunk i (Nat.le_of_succ_le hn)).length ≤ i := by simp [finPrefixList_length]
        rw [List.getElem_append_right hge]; simp [finPrefixList_length]

theorem finPrefixList_full_eq_ofFn {A : Type*} {L : ℕ} (chunk : Fin L → A) :
    finPrefixList chunk L (le_refl L) = List.ofFn chunk := by
  apply List.ext_getElem
  · simp [finPrefixList_length]
  · intro i hi₁ _; rw [finPrefixList_getElem, List.getElem_ofFn]

/-- Division-free causal decay product `∏_{a ≤ m < b} α_m` over any `CommRing R`. -/
def decayRange {R : Type*} [CommRing R] {L : ℕ} (α : Fin L → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | b + 1 => if a ≤ b then (if hb : b < L then α ⟨b, hb⟩ else 1) * decayRange α a b else 1

@[simp] theorem decayRange_self {R : Type*} [CommRing R] {L : ℕ} (α : Fin L → R) (a : ℕ) :
    decayRange α a a = 1 := by
  cases a with
  | zero => rfl
  | succ k =>
      have h : ¬ (k + 1 ≤ k) := by omega
      unfold decayRange; simp [h]

theorem decayRange_succ_of_le {R : Type*} [CommRing R] {L : ℕ} (α : Fin L → R)
    {a n : ℕ} (han : a ≤ n) (hn : n < L) :
    decayRange α a (n + 1) = α ⟨n, hn⟩ * decayRange α a n := by
  conv_lhs => unfold decayRange
  simp [han, hn]

def prefixDecay {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) (i : Fin L) : R :=
  decayRange (fun m => (chunk m).α) 0 (i.val + 1)

def pairDecay {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) (i j : Fin L) : R :=
  decayRange (fun m => (chunk m).α) (j.val + 1) (i.val + 1)

def tailDecay {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) (i : Fin L) : R :=
  decayRange (fun m => (chunk m).α) (i.val + 1) L

def chunkDecay {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : R :=
  decayRange (fun m => (chunk m).α) 0 L

/-- Strictly lower-triangular `L × L` WY coupling matrix `L_c`. -/
def wyL {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin L) R :=
  fun i j => if j < i then (chunk i).β * pairDecay chunk i j * dotProduct (chunk i).k (chunk j).k else 0

theorem wyL_isStrictLowerTri {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) : IsStrictLowerTri (wyL chunk) := by
  intro i j hij; simp [wyL, not_lt_of_ge hij]

/-- Incoming-state decayed key coupling `K_{dec,c} ∈ R^{L × dk}` (`row i = β_i γ^{(i)} k_iᵀ`). -/
def wyKDec {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin dk) R :=
  fun i x => (chunk i).β * prefixDecay chunk i * (chunk i).k x

/-- Write-gated value matrix `V_{β,c} ∈ R^{L × dv}` (`row i = β_i v_iᵀ`). -/
def wyVBeta {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin dv) R :=
  fun i d => (chunk i).β * (chunk i).v d

/-- Tail-decayed key projection `V_c = wyKTail ∈ R^{L × dk}` (`S_{c+1} = γ_c • S_c + V_cᵀ * U_{wy,c}`). -/
def wyKTail {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin dk) R :=
  fun i x => tailDecay chunk i * (chunk i).k x

/-- Stateful WY right-hand side `RHS_c(S_c) = V_{β,c} - K_{dec,c} * S_c`. -/
def wyStatefulRhs {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_in : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin L) (Fin dv) R :=
  wyVBeta chunk - wyKDec chunk * S_in

/-- Closed-form division-free stateful WY witness `U_{wy,c} = neumannInv L_c * (V_{β,c} - K_{dec,c} * S_c)`. -/
def solveStatefulWy {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_in : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin L) (Fin dv) R :=
  neumannInv (wyL chunk) * wyStatefulRhs chunk S_in

theorem solveStatefulWy_spec {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_in : Matrix (Fin dk) (Fin dv) R) :
    (1 + wyL chunk) * solveStatefulWy chunk S_in = wyStatefulRhs chunk S_in := by
  unfold solveStatefulWy
  rw [← Matrix.mul_assoc, mul_neumannInv_eq_one (wyL_isStrictLowerTri chunk), Matrix.one_mul]

def wyQDec {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin dk) R :=
  fun i x => prefixDecay chunk i * (chunk i).q x

def wyCausalAttn {R : Type*} [CommRing R] {L dk dv : ℕ} (chunk : Fin L → GdnToken R dk dv) : Matrix (Fin L) (Fin L) R :=
  fun i j => if j ≤ i then pairDecay chunk i j * dotProduct (chunk i).q (chunk j).k else 0

/-- **Core Prefix Invariant (`gdnPrefix_eq_stateful_wy`):**
Whenever `(1 + wyL chunk) * U = wyVBeta chunk - wyKDec chunk * S_in`, sequential `gdnStep` after `n ≤ L`
tokens equals `decayRange α 0 n • S_in + ∑_{j < n} decayRange α (j + 1) n • (k_j ⊗ U_j)` over ANY `CommRing R`. -/
theorem gdnPrefix_eq_stateful_wy {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_in : Matrix (Fin dk) (Fin dv) R)
    (U : Matrix (Fin L) (Fin dv) R) (hWY : (1 + wyL chunk) * U = wyStatefulRhs chunk S_in) :
    ∀ (n : ℕ) (hn : n ≤ L),
      gdnSeqList (finPrefixList chunk n hn) S_in =
        decayRange (fun m => (chunk m).α) 0 n • S_in +
          ∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < n),
            decayRange (fun m => (chunk m).α) (j.val + 1) n •
              Matrix.vecMulVec (chunk j).k (fun d => U j d) := by
  have hRecAll :=
    ((wyChunk_bilinear_iff_recurrence (wyL_isStrictLowerTri chunk) U (wyStatefulRhs chunk S_in)).1.trans
      (wyChunk_bilinear_iff_recurrence (wyL_isStrictLowerTri chunk) U (wyStatefulRhs chunk S_in)).2).mp hWY
  intro n; induction n with
  | zero =>
      intro _; simp [finPrefixList]
  | succ n ih =>
      intro hn
      let i : Fin L := ⟨n, hn⟩
      have hn_le : n ≤ L := Nat.le_of_succ_le hn
      simp only [finPrefixList, gdnSeqList_append, gdnSeqList_cons, gdnSeqList_nil]
      rw [ih hn_le]
      set S_n := decayRange (fun m => (chunk m).α) 0 n • S_in +
        ∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < n),
          decayRange (fun m => (chunk m).α) (j.val + 1) n • Matrix.vecMulVec (chunk j).k (fun d => U j d)
      have hDec0 : (chunk i).α • (decayRange (fun m => (chunk m).α) 0 n • S_in) =
          decayRange (fun m => (chunk m).α) 0 (n + 1) • S_in := by
        rw [smul_smul, ← decayRange_succ_of_le (fun m => (chunk m).α) (Nat.zero_le n) hn]
      have hDecSum : (chunk i).α • (∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < n),
            decayRange (fun m => (chunk m).α) (j.val + 1) n • Matrix.vecMulVec (chunk j).k (fun d => U j d)) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < n),
            decayRange (fun m => (chunk m).α) (j.val + 1) (n + 1) • Matrix.vecMulVec (chunk j).k (fun d => U j d) := by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj => ?_
        have hj_lt : j.val < n := (Finset.mem_filter.mp hj).2
        rw [smul_smul, ← decayRange_succ_of_le (fun m => (chunk m).α) (by omega) hn]
      have hRes : (chunk i).β • gdnResidual (chunk i).α (chunk i).k (chunk i).v S_n = fun d => U i d := by
        funext d
        have hUi := hRecAll i d
        have hFltEq : Finset.univ.filter (· < i) = Finset.univ.filter (fun j : Fin L => j.val < n) := by
          ext j; simp [i, Fin.lt_def]
        rw [hFltEq] at hUi
        let flt := Finset.univ.filter (fun j : Fin L => j.val < n)
        have hRead : ((chunk i).α • S_n)ᵀ.mulVec (chunk i).k d =
            prefixDecay chunk i * (∑ x : Fin dk, (chunk i).k x * S_in x d) +
              ∑ j ∈ flt, pairDecay chunk i j * dotProduct (chunk i).k (chunk j).k * U j d := by
          have hPfx : prefixDecay chunk i = (chunk i).α * decayRange (fun m => (chunk m).α) 0 n :=
            decayRange_succ_of_le (fun m => (chunk m).α) (Nat.zero_le n) hn
          simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.smul_apply, S_n,
            Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
          trans (∑ x : Fin dk, (chunk i).α * decayRange (fun m => (chunk m).α) 0 n * ((chunk i).k x * S_in x d) +
              ∑ x : Fin dk, ∑ j ∈ flt,
                (chunk i).α * decayRange (fun m => (chunk m).α) (j.val + 1) n * ((chunk i).k x * (chunk j).k x) * U j d)
          · rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun x _ => ?_
            rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
            congr 1; · ring
            · exact Finset.sum_congr rfl fun _ _ => by ring
          · congr 1
            · rw [hPfx, Finset.mul_sum]
            · rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j hj => ?_
              have hj_lt : j.val < n := (Finset.mem_filter.mp hj).2
              have hPair : pairDecay chunk i j = (chunk i).α * decayRange (fun m => (chunk m).α) (j.val + 1) n :=
                decayRange_succ_of_le (fun m => (chunk m).α) (by omega) hn
              rw [hPair, ← Finset.sum_mul, Finset.mul_sum]
        have hSub : (chunk i).β * (gdnResidual (chunk i).α (chunk i).k (chunk i).v S_n d) =
            wyStatefulRhs chunk S_in i d - ∑ j ∈ flt, wyL chunk i j * U j d := by
          change (chunk i).β * ((chunk i).v d - ((chunk i).α • S_n)ᵀ.mulVec (chunk i).k d) =
            (wyVBeta chunk i d - ∑ x : Fin dk, wyKDec chunk i x * S_in x d) -
              ∑ j ∈ flt, wyL chunk i j * U j d
          rw [hRead, mul_sub, mul_add]
          have hK : (chunk i).β * (prefixDecay chunk i * ∑ x : Fin dk, (chunk i).k x * S_in x d) =
              ∑ x : Fin dk, wyKDec chunk i x * S_in x d := by
            rw [← mul_assoc, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by dsimp [wyKDec]; ring
          have hL : (chunk i).β * (∑ j ∈ flt, pairDecay chunk i j * dotProduct (chunk i).k (chunk j).k * U j d) =
              ∑ j ∈ flt, wyL chunk i j * U j d := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j hj => ?_
            have hji : j < i := Fin.lt_def.mpr (Finset.mem_filter.mp hj).2
            simp only [wyL, hji, ↓reduceIte]; ring
          rw [hK, hL]; dsimp only [wyVBeta]; ring
        simpa [Pi.smul_apply, smul_eq_mul, flt, hUi] using hSub
      have hVec : (chunk i).β • Matrix.vecMulVec (chunk i).k (gdnResidual (chunk i).α (chunk i).k (chunk i).v S_n) =
          decayRange (fun m => (chunk m).α) (i.val + 1) (n + 1) • Matrix.vecMulVec (chunk i).k (fun d => U i d) := by
        have hOne : decayRange (fun m => (chunk m).α) (i.val + 1) (n + 1) = 1 := decayRange_self _ (n + 1)
        rw [hOne, one_smul, ← hRes]; ext x d; simp [Matrix.vecMulVec_apply, smul_eq_mul, mul_left_comm]
      have hSplit : Finset.univ.filter (fun j : Fin L => j.val < n + 1) =
          insert i (Finset.univ.filter (fun j : Fin L => j.val < n)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, i]; omega
      have hi_not_mem : i ∉ Finset.univ.filter (fun j : Fin L => j.val < n) := by simp [i]
      unfold gdnStep
      rw [smul_add, hDec0, hDecSum, hVec, hSplit, Finset.sum_insert hi_not_mem]; abel

/-- **Single-Chunk Stateful WY State-Carry (`wyStatefulChunk_eq_sequential_gdn`):**
`γ_c • S_c + (wyKTail chunk)ᵀ * U_{wy}` equals sequential `gdnStep` evolution from non-zero `S_c`. -/
theorem wyStatefulChunk_eq_sequential_gdn {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_c : Matrix (Fin dk) (Fin dv) R)
    (U_wy : Matrix (Fin L) (Fin dv) R) (hWY : (1 + wyL chunk) * U_wy = wyStatefulRhs chunk S_c) :
    chunkDecay chunk • S_c + (wyKTail chunk)ᵀ * U_wy = gdnSeqList (List.ofFn chunk) S_c := by
  rw [← finPrefixList_full_eq_ofFn chunk, gdnPrefix_eq_stateful_wy chunk S_c U_wy hWY L (le_refl L)]
  have hUniv : Finset.univ.filter (fun j : Fin L => j.val < L) = Finset.univ := by ext j; simp
  rw [hUniv]; congr 1; ext x d
  simp [wyKTail, tailDecay, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]

/-- **Single-Chunk Stateful WY Readout (`wyStatefulReadout_eq_sequential_readout`):**
Intra-chunk token readout `y_i = (S^{(i+1)})ᵀ q_i` equals row `i` of `Q_{dec} * S_c + A_c * U_{wy}`. -/
theorem wyStatefulReadout_eq_sequential_readout {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_c : Matrix (Fin dk) (Fin dv) R)
    (U_wy : Matrix (Fin L) (Fin dv) R) (hWY : (1 + wyL chunk) * U_wy = wyStatefulRhs chunk S_c) (i : Fin L) :
    gdnReadout (chunk i).q (gdnSeqList (finPrefixList chunk (i.val + 1) i.isLt) S_c) =
      fun d => (wyQDec chunk * S_c + wyCausalAttn chunk * U_wy) i d := by
  rw [gdnPrefix_eq_stateful_wy chunk S_c U_wy hWY (i.val + 1) i.isLt]; funext d
  let flt := Finset.univ.filter (fun j : Fin L => j.val < i.val + 1)
  simp only [gdnReadout, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, smul_eq_mul]
  change ∑ x : Fin dk, (prefixDecay chunk i * S_c x d +
        ∑ j ∈ flt, pairDecay chunk i j * ((chunk j).k x * U_wy j d)) * (chunk i).q x =
      (∑ x : Fin dk, wyQDec chunk i x * S_c x d) + ∑ j : Fin L, wyCausalAttn chunk i j * U_wy j d
  have hAttn : (∑ j : Fin L, wyCausalAttn chunk i j * U_wy j d) =
      ∑ j ∈ flt, pairDecay chunk i j * dotProduct (chunk i).q (chunk j).k * U_wy j d := by
    have hSub : (∑ j ∈ flt, wyCausalAttn chunk i j * U_wy j d) =
        ∑ j : Fin L, wyCausalAttn chunk i j * U_wy j d := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hnot : ¬ (j ≤ i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Fin.le_iff_val_le_val]; omega
      simp [wyCausalAttn, hnot]
    rw [← hSub]; refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ i := Fin.le_iff_val_le_val.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
    simp only [wyCausalAttn, hj_le, ↓reduceIte]
  rw [hAttn]
  trans (∑ x : Fin dk, prefixDecay chunk i * S_c x d * (chunk i).q x +
      ∑ x : Fin dk, ∑ j ∈ flt, pairDecay chunk i j * ((chunk j).k x * U_wy j d) * (chunk i).q x)
  · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by rw [add_mul, Finset.sum_mul]
  · congr 1
    · exact Finset.sum_congr rfl fun _ _ => by dsimp [wyQDec]; ring
    · rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
      unfold dotProduct; rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring

/-- Flatten `C` chunks of `L` tokens into one unchunked `C · L`-token stream. -/
def flattenChunks {R : Type*} {L dk dv : ℕ} :
    {C : ℕ} → (Fin C → Fin L → GdnToken R dk dv) → List (GdnToken R dk dv)
  | 0, _ => []
  | _ + 1, chunks => List.ofFn (chunks 0) ++ flattenChunks (fun c => chunks c.succ)

theorem flattenChunks_length {R : Type*} {L dk dv : ℕ} :
    ∀ {C : ℕ} (chunks : Fin C → Fin L → GdnToken R dk dv), (flattenChunks chunks).length = C * L
  | 0, _ => by simp [flattenChunks]
  | C + 1, chunks => by simp [flattenChunks, flattenChunks_length (fun c => chunks c.succ), Nat.succ_mul, Nat.add_comm]

def ValidStatefulWyChunk {R : Type*} [CommRing R] {L dk dv : ℕ}
    (chunk : Fin L → GdnToken R dk dv) (S_in S_out : Matrix (Fin dk) (Fin dv) R)
    (U_wy : Matrix (Fin L) (Fin dv) R) : Prop :=
  (1 + wyL chunk) * U_wy = wyStatefulRhs chunk S_in ∧
  S_out = chunkDecay chunk • S_in + (wyKTail chunk)ᵀ * U_wy

/-- **Main Multi-Chunk GDN Recurrence Theorem (`chunkedGdnChain_eq_sequential_gdn`):**
Over ANY `CommRing R`, across `C` chunks of `L` tokens (`C · L` total tokens) from ANY `S 0`, per-chunk
`ValidStatefulWyChunk` forces `S (Fin.last C) = gdnSeqList (flattenChunks chunks) (S 0)`! -/
theorem chunkedGdnChain_eq_sequential_gdn {R : Type*} [CommRing R] {L dk dv : ℕ} :
    ∀ {C : ℕ} (chunks : Fin C → Fin L → GdnToken R dk dv)
      (S : Fin (C + 1) → Matrix (Fin dk) (Fin dv) R) (U_wy : Fin C → Matrix (Fin L) (Fin dv) R),
      (∀ c : Fin C, ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c)) →
      S (Fin.last C) = gdnSeqList (flattenChunks chunks) (S 0)
  | 0, chunks, S, _, _ => rfl
  | C + 1, chunks, S, U_wy, hAll => by
      have h0 := hAll 0
      have hStep0 : S 1 = gdnSeqList (List.ofFn (chunks 0)) (S 0) :=
        h0.2.trans (wyStatefulChunk_eq_sequential_gdn (chunks 0) (S 0) (U_wy 0) h0.1)
      let chunks' : Fin C → Fin L → GdnToken R dk dv := fun c => chunks c.succ
      let S' : Fin (C + 1) → Matrix (Fin dk) (Fin dv) R := fun c => S c.succ
      let U' : Fin C → Matrix (Fin L) (Fin dv) R := fun c => U_wy c.succ
      have hTail : ∀ c : Fin C, ValidStatefulWyChunk (chunks' c) (S' c.castSucc) (S' c.succ) (U' c) :=
        fun c => by
          dsimp only [chunks', S', U']
          have hEq : c.castSucc.succ = c.succ.castSucc := Fin.ext (by simp)
          rw [hEq]; exact hAll c.succ
      have hIH := chunkedGdnChain_eq_sequential_gdn chunks' S' U' hTail
      have hLast : S (Fin.last (C + 1)) = S' (Fin.last C) := rfl
      have hS1 : S 1 = S' 0 := rfl
      rw [flattenChunks, gdnSeqList_append, ← hStep0, hS1, hLast, hIH]

end StatefulChunkWY

/-! ## §2. `O(1)` Verifier Memory, `cSHAKE256` Commitment Chain, & `C · ε_chunk` Union-Bound Soundness -/

section StreamingReceiptChain

def carryChainCust : List UInt8 :=
  "QW35-JITT-CHAIN-V1".toList.map (fun c => UInt8.ofNat c.toNat)

/-- Constant-size (`O(1)`) wearable verifier state (`144` bytes independent of `C` and `C · L_chunk`). -/
structure CarryVerifierState where
  sessionId        : Digest
  modelWeightRoot  : Digest
  layerIdx         : Nat
  expectedChunkIdx : Nat
  currentStateRoot : Digest
  chainDigest      : Digest
  deriving DecidableEq, Repr

def CarryVerifierState.byteFootprint (_st : CarryVerifierState) : Nat := 4 * 32 + 2 * 8

theorem CarryVerifierState.byteFootprint_const (st₁ st₂ : CarryVerifierState) :
    st₁.byteFootprint = st₂.byteFootprint ∧ st₁.byteFootprint = 144 := ⟨rfl, rfl⟩

structure CarryChunkReceipt (Proof : Type*) where
  sessionId       : Digest
  modelWeightRoot : Digest
  layerIdx        : Nat
  chunkIdx        : Nat
  sInRoot         : Digest
  sOutRoot        : Digest
  chunkTokCommit  : Digest
  proof           : Proof

def carryStepHashInput (prevChain : Digest) (chunkIdx layerIdx : Nat) (sInRoot sOutRoot tokCommit : Digest) : List UInt8 :=
  StreamCodec.nat.encode prevChain.value ++
    (StreamCodec.nat.encode chunkIdx ++
      (StreamCodec.nat.encode layerIdx ++
        (StreamCodec.nat.encode sInRoot.value ++
          (StreamCodec.nat.encode sOutRoot.value ++ StreamCodec.nat.encode tokCommit.value))))

def stepCarryChainDigest (prevChain : Digest) (chunkIdx layerIdx : Nat) (sInRoot sOutRoot tokCommit : Digest) : Digest :=
  cshakeC.xofDigest carryChainCust (carryStepHashInput prevChain chunkIdx layerIdx sInRoot sOutRoot tokCommit)

private theorem peel_nat {a b : Nat} {r₁ r₂ : List UInt8}
    (h : StreamCodec.nat.encode a ++ r₁ = StreamCodec.nat.encode b ++ r₂) : a = b ∧ r₁ = r₂ := by
  have hd := congrArg StreamCodec.nat.decodePrefix h
  rw [StreamCodec.nat.decodePrefix_encode, StreamCodec.nat.decodePrefix_encode] at hd
  exact Prod.mk.inj (Option.some.inj hd)

private theorem digest_eq_of_val {d₁ d₂ : Digest} (h : d₁.value = d₂.value) : d₁ = d₂ := by
  cases d₁; cases d₂; cases h; rfl

theorem carryStepHashInput_inj {p₁ p₂ : Digest} {c₁ c₂ l₁ l₂ : Nat} {si₁ si₂ so₁ so₂ tk₁ tk₂ : Digest}
    (heq : carryStepHashInput p₁ c₁ l₁ si₁ so₁ tk₁ = carryStepHashInput p₂ c₂ l₂ si₂ so₂ tk₂) :
    p₁ = p₂ ∧ c₁ = c₂ ∧ l₁ = l₂ ∧ si₁ = si₂ ∧ so₁ = so₂ ∧ tk₁ = tk₂ := by
  unfold carryStepHashInput at heq
  obtain ⟨hp, r1⟩ := peel_nat heq
  obtain ⟨hc, r2⟩ := peel_nat r1
  obtain ⟨hl, r3⟩ := peel_nat r2
  obtain ⟨hsi, r4⟩ := peel_nat r3
  obtain ⟨hso, r5⟩ := peel_nat r4
  have r5' : StreamCodec.nat.encode tk₁.value ++ [] = StreamCodec.nat.encode tk₂.value ++ [] := by simpa using r5
  obtain ⟨htk, _⟩ := peel_nat r5'
  exact ⟨digest_eq_of_val hp, hc, hl, digest_eq_of_val hsi, digest_eq_of_val hso, digest_eq_of_val htk⟩

def verifyStreamingCarryStep {Proof : Type*} (verifyProof : CarryChunkReceipt Proof → Bool)
    (st : CarryVerifierState) (r : CarryChunkReceipt Proof) : Option CarryVerifierState :=
  if r.sessionId == st.sessionId && r.modelWeightRoot == st.modelWeightRoot &&
     r.layerIdx == st.layerIdx && r.chunkIdx == st.expectedChunkIdx &&
     r.sInRoot == st.currentStateRoot && verifyProof r then
    some { sessionId := st.sessionId, modelWeightRoot := st.modelWeightRoot, layerIdx := st.layerIdx,
           expectedChunkIdx := st.expectedChunkIdx + 1, currentStateRoot := r.sOutRoot,
           chainDigest := stepCarryChainDigest st.chainDigest r.chunkIdx r.layerIdx
             r.sInRoot r.sOutRoot r.chunkTokCommit }
  else none

def verifyStreamingCarryChain {Proof : Type*} (verifyProof : CarryChunkReceipt Proof → Bool)
    (initState : CarryVerifierState) : List (CarryChunkReceipt Proof) → Option CarryVerifierState
  | [] => some initState
  | r :: rs => (verifyStreamingCarryStep verifyProof initState r).bind (verifyStreamingCarryChain verifyProof · rs)

theorem verifyStreamingCarryChain_invariants {Proof : Type*} (verifyProof : CarryChunkReceipt Proof → Bool) :
    ∀ (rs : List (CarryChunkReceipt Proof)) (st₀ stF : CarryVerifierState),
      verifyStreamingCarryChain verifyProof st₀ rs = some stF →
      stF.expectedChunkIdx = st₀.expectedChunkIdx + rs.length ∧
      (∀ r ∈ rs, verifyProof r = true ∧ r.sessionId = st₀.sessionId ∧
        r.modelWeightRoot = st₀.modelWeightRoot ∧ r.layerIdx = st₀.layerIdx) ∧
      (match rs with
       | [] => stF.currentStateRoot = st₀.currentStateRoot
       | hd :: tl => hd.sInRoot = st₀.currentStateRoot ∧
           ((hd :: tl).getLast (List.cons_ne_nil hd tl)).sOutRoot = stF.currentStateRoot)
  | [], st₀, stF, h => by injection h with hEq; subst hEq; simp
  | r :: rs, st₀, stF, h => by
      simp only [verifyStreamingCarryChain, Option.bind_eq_some_iff] at h
      rcases h with ⟨mid, hStep, hTail⟩
      unfold verifyStreamingCarryStep at hStep; split_ifs at hStep with hCond
      injection hStep with hMid; subst hMid
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      rcases hCond with ⟨⟨⟨⟨⟨hSess, hMod⟩, hLay⟩, hIdx⟩, hSIn⟩, hPrf⟩
      obtain ⟨hExp, hAll, hEnds⟩ := verifyStreamingCarryChain_invariants verifyProof rs _ stF hTail
      dsimp only at hExp hAll
      refine ⟨by simp [List.length_cons]; omega, fun x hx => ?_, hSIn, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨hPrf, hSess, hMod, hLay⟩
        · exact hAll x hmem
      · cases rs with
        | nil => simp only [verifyStreamingCarryChain] at hTail; injection hTail with hEq; subst hEq; rfl
        | cons r₂ tl => simpa [List.getLast_cons] using hEnds.2

theorem stepCarryChainDigest_eq_or_collision {p₁ p₂ : Digest} {c₁ c₂ l₁ l₂ : Nat} {si₁ si₂ so₁ so₂ tk₁ tk₂ : Digest}
    (hd : stepCarryChainDigest p₁ c₁ l₁ si₁ so₁ tk₁ = stepCarryChainDigest p₂ c₂ l₂ si₂ so₂ tk₂) :
    (p₁ = p₂ ∧ c₁ = c₂ ∧ l₁ = l₂ ∧ si₁ = si₂ ∧ so₁ = so₂ ∧ tk₁ = tk₂) ∨
    FramedXofCollision cshakeC carryChainCust
      (carryStepHashInput p₁ c₁ l₁ si₁ so₁ tk₁) (carryStepHashInput p₂ c₂ l₂ si₂ so₂ tk₂) := by
  rcases Classical.em (carryStepHashInput p₁ c₁ l₁ si₁ so₁ tk₁ = carryStepHashInput p₂ c₂ l₂ si₂ so₂ tk₂) with hinp | hinp
  · exact Or.inl (carryStepHashInput_inj hinp)
  · exact Or.inr ⟨hinp, hd⟩

attribute [irreducible] stepCarryChainDigest

def foldCarryHeaders (initChain : Digest) : List (Nat × Nat × Digest × Digest × Digest) → Digest
  | [] => initChain
  | (c, l, si, so, tk) :: tl => foldCarryHeaders (stepCarryChainDigest initChain c l si so tk) tl

theorem foldCarryHeaders_snoc (initChain : Digest) (xs : List (Nat × Nat × Digest × Digest × Digest))
    (c l : Nat) (si so tk : Digest) :
    foldCarryHeaders initChain (xs ++ [(c, l, si, so, tk)]) =
      stepCarryChainDigest (foldCarryHeaders initChain xs) c l si so tk := by
  induction xs generalizing initChain with
  | nil => simp only [List.nil_append, foldCarryHeaders]
  | cons hd tl ih =>
      rcases hd with ⟨c₀, l₀, si₀, so₀, tk₀⟩
      simp only [List.cons_append, foldCarryHeaders]
      exact ih (stepCarryChainDigest initChain c₀ l₀ si₀ so₀ tk₀)

/-- **Full Multi-Chunk `cSHAKE256` History Integrity (`streamingCarryChain_eq_or_collision`):**
Two `C`-chunk header histories with equal terminal `chainDigest` either agree on `init` and every
chunk's `(chunkIdx, layerIdx, rt_{S,c}, rt_{S,c+1}, tokCommit)` or exhibit a `FramedXofCollision`. -/
theorem streamingCarryChain_eq_or_collision :
    ∀ (xs ys : List (Nat × Nat × Digest × Digest × Digest)) (init₁ init₂ : Digest),
      xs.length = ys.length →
      foldCarryHeaders init₁ xs = foldCarryHeaders init₂ ys →
      (init₁ = init₂ ∧ xs = ys) ∨ ∃ inp₁ inp₂, FramedXofCollision cshakeC carryChainCust inp₁ inp₂ := by
  intro xs; induction xs using List.reverseRecOn with
  | nil =>
      intro ys init₁ init₂ hlen hd
      cases ys with | nil => exact Or.inl ⟨hd, rfl⟩ | cons _ _ => simp at hlen
  | append_singleton xs last₁ ih =>
      intro ys init₁ init₂ hlen hd
      rcases last₁ with ⟨c₁, l₁, si₁, so₁, tk₁⟩
      have hne : ys ≠ [] := by intro h; subst h; simp at hlen
      rcases List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hne) with ⟨last₂, revTl, hrev⟩
      have hys : ys = revTl.reverse ++ [last₂] := by
        simpa [List.reverse_cons] using congrArg List.reverse hrev
      subst hys
      rcases last₂ with ⟨c₂, l₂, si₂, so₂, tk₂⟩
      have hlen' : xs.length = revTl.reverse.length := by
        simp only [List.length_append, List.length_singleton, List.length_reverse] at hlen ⊢; omega
      rw [foldCarryHeaders_snoc, foldCarryHeaders_snoc] at hd
      rcases stepCarryChainDigest_eq_or_collision hd with ⟨hp, rfl, rfl, rfl, rfl, rfl⟩ | hcol
      · rcases ih revTl.reverse init₁ init₂ hlen' hp with ⟨rfl, rfl⟩ | hcol'
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hcol'
      · exact Or.inr ⟨_, _, hcol⟩

theorem union_bound_fin_prob {Ω : Type*} [Fintype Ω] [Nonempty Ω] {C : ℕ}
    (Bad : Fin C → Ω → Prop) [∀ c, DecidablePred (Bad c)] (ε_chunk : ℚ)
    (hBound : ∀ c : Fin C, ((Finset.univ.filter (Bad c)).card : ℚ) / (Fintype.card Ω : ℚ) ≤ ε_chunk) :
    ((Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω)).card : ℚ) /
      (Fintype.card Ω : ℚ) ≤ (C : ℚ) * ε_chunk := by
  classical
  have hPos : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast Fintype.card_pos (α := Ω)
  have hSub : Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω) ⊆
      Finset.univ.biUnion (fun c : Fin C => Finset.univ.filter (Bad c)) := fun ω hω => by
    rcases (Finset.mem_filter.mp hω).2 with ⟨c, hc⟩
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hc⟩⟩
  have hCardRat : ((Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω)).card : ℚ) ≤
      ∑ c : Fin C, ((Finset.univ.filter (Bad c)).card : ℚ) :=
    by exact_mod_cast (le_trans (Finset.card_le_card hSub) Finset.card_biUnion_le)
  calc ((Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω)).card : ℚ) / (Fintype.card Ω : ℚ)
      ≤ (∑ c : Fin C, ((Finset.univ.filter (Bad c)).card : ℚ)) / (Fintype.card Ω : ℚ) :=
        div_le_div_of_nonneg_right hCardRat (le_of_lt hPos)
    _ = ∑ c : Fin C, (((Finset.univ.filter (Bad c)).card : ℚ) / (Fintype.card Ω : ℚ)) := Finset.sum_div _ _ _
    _ ≤ ∑ _c : Fin C, ε_chunk := Finset.sum_le_sum fun c _ => hBound c
    _ = (C : ℚ) * ε_chunk := by simp

/-- **End-to-End Multi-Chunk Soundness Union Bound (`streamingCarryChain_soundness_union_bound`):**
Whenever `S (Fin.last C) ≠ gdnSeqList (flattenChunks chunks) (S 0)` and each invalid chunk accepts
with probability `≤ ε_chunk`, all `C` chunks simultaneously accept with probability `≤ (C : ℚ) * ε_chunk`. -/
theorem streamingCarryChain_soundness_union_bound
    {R : Type*} [CommRing R] {C L dk dv : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (chunks : Fin C → Fin L → GdnToken R dk dv)
    (S : Fin (C + 1) → Matrix (Fin dk) (Fin dv) R) (U_wy : Fin C → Matrix (Fin L) (Fin dv) R)
    (acceptChunk : Fin C → Ω → Bool) (ε_chunk : ℚ) (hε_nonneg : 0 ≤ ε_chunk)
    (hChunkSound : ∀ c : Fin C, ¬ ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c) →
      ((Finset.univ.filter (fun ω : Ω => acceptChunk c ω = true)).card : ℚ) / (Fintype.card Ω : ℚ) ≤ ε_chunk)
    (hFalseClaim : S (Fin.last C) ≠ gdnSeqList (flattenChunks chunks) (S 0)) :
    ((Finset.univ.filter (fun ω : Ω => ∀ c : Fin C, acceptChunk c ω = true)).card : ℚ) /
      (Fintype.card Ω : ℚ) ≤ (C : ℚ) * ε_chunk := by
  classical
  have hExistsBad : ∃ c : Fin C, ¬ ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c) := by
    apply Classical.byContradiction; intro hNoBad
    have hAllGood : ∀ c : Fin C, ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c) :=
      fun c => Classical.byContradiction fun hc => hNoBad ⟨c, hc⟩
    exact hFalseClaim (chunkedGdnChain_eq_sequential_gdn chunks S U_wy hAllGood)
  let Bad : Fin C → Ω → Prop := fun c ω =>
    ¬ ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c) ∧ acceptChunk c ω = true
  have hSub : Finset.univ.filter (fun ω : Ω => ∀ c : Fin C, acceptChunk c ω = true) ⊆
      Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω) := fun ω hω => by
    rcases hExistsBad with ⟨c₀, hc₀⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, ⟨c₀, hc₀, (Finset.mem_filter.mp hω).2 c₀⟩⟩
  have hPos : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast Fintype.card_pos (α := Ω)
  have hLeUnion : ((Finset.univ.filter (fun ω : Ω => ∀ c : Fin C, acceptChunk c ω = true)).card : ℚ) /
        (Fintype.card Ω : ℚ) ≤
      ((Finset.univ.filter (fun ω : Ω => ∃ c : Fin C, Bad c ω)).card : ℚ) / (Fintype.card Ω : ℚ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hPos); exact_mod_cast Finset.card_le_card hSub
  refine le_trans hLeUnion (union_bound_fin_prob Bad ε_chunk fun c => ?_)
  by_cases hVal : ValidStatefulWyChunk (chunks c) (S c.castSucc) (S c.succ) (U_wy c)
  · have hemp : Finset.univ.filter (Bad c) = ∅ := by ext ω; simp [Bad, hVal]
    rw [hemp]; simp [hε_nonneg]
  · have hEqFlt : Finset.univ.filter (Bad c) = Finset.univ.filter (fun ω : Ω => acceptChunk c ω = true) := by
      ext ω; simp [Bad, hVal]
    rw [hEqFlt]; exact hChunkSound c hVal

end StreamingReceiptChain

/-! ## §3. Exact `TVD = 0` Inter-Chunk `S_c(r_h, r_v, r_k)` Handoff via Dual Random-Mask Difference -/

section BlindedHandoffTVDZero

def dualMaskHandoff {F : Type*} [CommRing F] (α s : F) (masks : F × F) : F × F :=
  (masks.1 - masks.2, α * s + masks.1)

def dualMaskHandoffInv {F : Type*} [CommRing F] (α s : F) (transcript : F × F) : F × F :=
  (transcript.2 - α * s, transcript.2 - α * s - transcript.1)

def dualMaskHandoffEquiv {F : Type*} [CommRing F] (α s : F) : (F × F) ≃ (F × F) where
  toFun := dualMaskHandoff α s
  invFun := dualMaskHandoffInv α s
  left_inv m := by ext <;> simp [dualMaskHandoff, dualMaskHandoffInv]
  right_inv t := by ext <;> simp [dualMaskHandoff, dualMaskHandoffInv]

theorem dualMaskHandoff_bijective {F : Type*} [CommRing F] (α s : F) :
    Function.Bijective (dualMaskHandoff α s) := (dualMaskHandoffEquiv α s).bijective

theorem dualMaskHandoff_binding_of_isUnit {F : Type*} [CommRing F]
    {α s₁ s₂ m₁ m₂ deltaM mu : F} (hUnit : IsUnit α)
    (hDelta : deltaM = m₁ - m₂) (hOpen₁ : α * s₁ + m₁ = mu) (hOpen₂ : α * s₂ + m₂ = mu - deltaM) :
    s₁ = s₂ := by
  have hMul : α * s₁ = α * s₂ := by linear_combination hOpen₁ - hOpen₂ + hDelta
  exact hUnit.mul_left_cancel hMul

def handoffTranscriptProb {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    (α s : F) (target : F × F) : ℚ :=
  ((Finset.univ.filter (fun m : F × F => dualMaskHandoff α s m = target)).card : ℚ) / (Fintype.card (F × F) : ℚ)

theorem handoffTranscriptProb_eq_uniform {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    (α s : F) (target : F × F) :
    handoffTranscriptProb α s target = 1 / (Fintype.card (F × F) : ℚ) := by
  unfold handoffTranscriptProb
  have hSingle : Finset.univ.filter (fun m : F × F => dualMaskHandoff α s m = target) =
      {dualMaskHandoffInv α s target} := by
    ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hm => ?_, fun hm => hm ▸ (dualMaskHandoffEquiv α s).right_inv target⟩
    have h := congrArg (dualMaskHandoffInv α s) hm
    exact ((dualMaskHandoffEquiv α s).left_inv m).symm.trans h
  rw [hSingle, Finset.card_singleton, Nat.cast_one]

def handoffTVD {F : Type*} [CommRing F] [Fintype F] [DecidableEq F] (α s₁ s₂ : F) : ℚ :=
  (1 / 2 : ℚ) * ∑ t : F × F, |handoffTranscriptProb α s₁ t - handoffTranscriptProb α s₂ t|

/-- **Exact `TVD = 0` Handoff Theorem (`handoffTVD_eq_zero`):**
Dual random-mask handoff `(Δ_M, α * s + M_1)` achieves `TVD = 0` for all `α, s₁, s₂ : F`. -/
theorem handoffTVD_eq_zero {F : Type*} [CommRing F] [Fintype F] [DecidableEq F] (α s₁ s₂ : F) :
    handoffTVD α s₁ s₂ = 0 := by
  unfold handoffTVD
  have hZero : ∀ t : F × F, |handoffTranscriptProb α s₁ t - handoffTranscriptProb α s₂ t| = 0 := fun t => by
    rw [handoffTranscriptProb_eq_uniform α s₁ t, handoffTranscriptProb_eq_uniform α s₂ t, sub_self, abs_zero]
  simp [hZero]

theorem babyBearExt4_handoffTVD_eq_zero
    (α : Minidregg.Selvage.BabyBearExt4.Ext4)
    (S₁ S₂ : (Fin 4 → Minidregg.Selvage.BabyBearExt4.Ext4) →
             (Fin 7 → Minidregg.Selvage.BabyBearExt4.Ext4) →
             (Fin 7 → Minidregg.Selvage.BabyBearExt4.Ext4) →
             Minidregg.Selvage.BabyBearExt4.Ext4)
    (r_h : Fin 4 → Minidregg.Selvage.BabyBearExt4.Ext4)
    (r_v r_k : Fin 7 → Minidregg.Selvage.BabyBearExt4.Ext4) :
    @handoffTVD Minidregg.Selvage.BabyBearExt4.Ext4 _
      (Fintype.ofEquiv _ Minidregg.Selvage.BabyBearExt4.coefficients.toEquiv.symm)
      (Classical.decEq _) α (S₁ r_h r_v r_k) (S₂ r_h r_v r_k) = 0 :=
  @handoffTVD_eq_zero Minidregg.Selvage.BabyBearExt4.Ext4 _
    (Fintype.ofEquiv _ Minidregg.Selvage.BabyBearExt4.coefficients.toEquiv.symm)
    (Classical.decEq _) α (S₁ r_h r_v r_k) (S₂ r_h r_v r_k)

end BlindedHandoffTVDZero

/-! ## §4. Premise Inhabitation Witnesses & Four `#tooth` Falsifiers -/

section WitnessesAndTeeth

abbrev BabyBearMod : ℕ := 2013265921

def sampleChunksInt : Fin 3 → Fin 2 → GdnToken ℤ 2 2
  | 0, 0 => { α := 2, β := 1, k := ![1, 0], v := ![5, -3], q := ![1, 1] }
  | 0, 1 => { α := 1, β := 2, k := ![1, 1], v := ![4, 2],  q := ![0, 1] }
  | 1, 0 => { α := 3, β := 1, k := ![0, 1], v := ![-2, 7], q := ![1, 0] }
  | 1, 1 => { α := 1, β := 1, k := ![1, -1], v := ![6, 1], q := ![1, 1] }
  | 2, 0 => { α := 2, β := 2, k := ![1, 0], v := ![3, 3],  q := ![1, -1] }
  | 2, 1 => { α := 1, β := 1, k := ![0, 1], v := ![-4, 9], q := ![1, 0] }

theorem multiChunk_stateful_wy_witness_int :
    let S₀ : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![3, -2], ![5, 4]]
    let U₀ := solveStatefulWy (sampleChunksInt 0) S₀
    let S₁ := chunkDecay (sampleChunksInt 0) • S₀ + (wyKTail (sampleChunksInt 0))ᵀ * U₀
    let U₁ := solveStatefulWy (sampleChunksInt 1) S₁
    let S₂ := chunkDecay (sampleChunksInt 1) • S₁ + (wyKTail (sampleChunksInt 1))ᵀ * U₁
    let U₂ := solveStatefulWy (sampleChunksInt 2) S₂
    let S₃ := chunkDecay (sampleChunksInt 2) • S₂ + (wyKTail (sampleChunksInt 2))ᵀ * U₂
    S₀ ≠ 0 ∧ S₁ ≠ 0 ∧ S₂ ≠ 0 ∧ S₃ = gdnSeqList (flattenChunks sampleChunksInt) S₀ ∧
    (∀ d : Fin 2,
      gdnReadout (sampleChunksInt 1 1).q (gdnSeqList (List.ofFn (sampleChunksInt 1)) S₁) d =
        (wyQDec (sampleChunksInt 1) * S₁ + wyCausalAttn (sampleChunksInt 1) * U₁) 1 d) := by
  refine ⟨by decide, by decide, by decide, by decide, fun d => ?_⟩
  fin_cases d <;> decide

theorem multiChunk_witness_zmod16 :
    let c₀ : Fin 2 → GdnToken (ZMod 16) 2 2
      | 0 => { α := 3, β := 2, k := ![1, 2], v := ![5, 7], q := ![1, 0] }
      | 1 => { α := 2, β := 3, k := ![2, 1], v := ![9, 4], q := ![0, 1] }
    let c₁ : Fin 2 → GdnToken (ZMod 16) 2 2
      | 0 => { α := 4, β := 1, k := ![1, 1], v := ![3, 6], q := ![1, 1] }
      | 1 => { α := 1, β := 2, k := ![0, 1], v := ![8, 5], q := ![1, 0] }
    let chunks : Fin 2 → Fin 2 → GdnToken (ZMod 16) 2 2 | 0 => c₀ | 1 => c₁
    let S₀ : Matrix (Fin 2) (Fin 2) (ZMod 16) := ![![7, 3], ![11, 5]]
    let U₀ := solveStatefulWy c₀ S₀
    let S₁ := chunkDecay c₀ • S₀ + (wyKTail c₀)ᵀ * U₀
    let U₁ := solveStatefulWy c₁ S₁
    let S₂ := chunkDecay c₁ • S₁ + (wyKTail c₁)ᵀ * U₁
    ((4 : ZMod 16) ≠ 0 ∧ (4 : ZMod 16) * 4 = 0) ∧ S₂ = gdnSeqList (flattenChunks chunks) S₀ := by
  decide

/-- **`#tooth` 1 (`tooth_silent_s_init_zero_reset`):** catches `S_init = 0` mid-session state reset! -/
theorem tooth_silent_s_init_zero_reset :
    (let S₀ : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -2], ![5, 4]]
     let S₁_true := gdnSeqList (List.ofFn (sampleChunksInt 0)) S₀
     gdnSeqList (List.ofFn (sampleChunksInt 1)) 0 ≠ gdnSeqList (List.ofFn (sampleChunksInt 1)) S₁_true) ∧
    (∀ {Proof : Type*} (vp : CarryChunkReceipt Proof → Bool) (st₀ : CarryVerifierState)
       (r₀ r₁_reset : CarryChunkReceipt Proof),
       r₁_reset.sInRoot ≠ r₀.sOutRoot → verifyStreamingCarryChain vp st₀ [r₀, r₁_reset] = none) := by
  refine ⟨by decide, fun vp st₀ r₀ r₁ hNe => ?_⟩
  simp only [verifyStreamingCarryChain]
  cases hStep₀ : verifyStreamingCarryStep vp st₀ r₀ with
  | none => rfl
  | some mid =>
      unfold verifyStreamingCarryStep at hStep₀
      split_ifs at hStep₀ with hCond
      injection hStep₀ with hMid; subst hMid
      simp [verifyStreamingCarryStep, hNe]

/-- **`#tooth` 2 (`tooth_chunk_reorder_splice`):** catches chunk-reorder / swap splice! -/
theorem tooth_chunk_reorder_splice :
    (let S₀ : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -2], ![5, 4]]
     gdnSeqList (List.ofFn (sampleChunksInt 1) ++ List.ofFn (sampleChunksInt 0)) S₀ ≠
       gdnSeqList (List.ofFn (sampleChunksInt 0) ++ List.ofFn (sampleChunksInt 1)) S₀) ∧
    (∀ {Proof : Type*} (vp : CarryChunkReceipt Proof → Bool) (st₀ : CarryVerifierState)
       (r_spliced : CarryChunkReceipt Proof) (tl : List (CarryChunkReceipt Proof)),
       r_spliced.chunkIdx ≠ st₀.expectedChunkIdx →
       verifyStreamingCarryChain vp st₀ (r_spliced :: tl) = none) := by
  refine ⟨by decide, fun vp st₀ r tl hNe => ?_⟩
  simp only [verifyStreamingCarryChain]; unfold verifyStreamingCarryStep
  have hFalse : (r.chunkIdx == st₀.expectedChunkIdx) = false := beq_eq_false_iff_ne.mpr hNe
  simp [hFalse]

/-- **`#tooth` 3 (`tooth_dropped_kc_sc_wy_coupling`):** catches dropped `- K_c · S_c` WY coupling! -/
theorem tooth_dropped_kc_sc_wy_coupling :
    (let chunk := sampleChunksInt 1
     let S_c : Matrix (Fin 2) (Fin 2) ℤ := ![![2, 5], ![-3, 4]]
     let U_dropped := neumannInv (wyL chunk) * wyVBeta chunk
     (1 + wyL chunk) * U_dropped = wyVBeta chunk ∧
     chunkDecay chunk • S_c + (wyKTail chunk)ᵀ * U_dropped ≠ gdnSeqList (List.ofFn chunk) S_c) ∧
    (let chunkBB : Fin 2 → GdnToken (ZMod BabyBearMod) 2 2
       | 0 => { α := 2, β := 1, k := ![1, 0], v := ![10, 20], q := ![1, 0] }
       | 1 => { α := 3, β := 1, k := ![1, 1], v := ![30, 40], q := ![0, 1] }
     let S_c : Matrix (Fin 2) (Fin 2) (ZMod BabyBearMod) := ![![7, 9], ![11, 13]]
     let U_dropped := neumannInv (wyL chunkBB) * wyVBeta chunkBB
     chunkDecay chunkBB • S_c + (wyKTail chunkBB)ᵀ * U_dropped ≠ gdnSeqList (List.ofFn chunkBB) S_c) := by
  decide

def brokenSingleMaskHandoff {F : Type*} [CommRing F] (α s_out s_in m : F) : F × F :=
  (α * s_out + m, α * s_in + m)

/-- **`#tooth` 4 (`tooth_reused_single_mask_breaks_tvd_zero`):** reusing a single mask `M` across two
openings `(α * s_out + M, α * s_in + M)` yields disjoint transcript support (`card = 1` vs `card = 0`
at `(0, 0)` over `ZMod 7`), whereas `handoffTVD 1 0 1 = 0`! -/
theorem tooth_reused_single_mask_breaks_tvd_zero :
    (Finset.univ.filter (fun m : ZMod 7 => brokenSingleMaskHandoff (1 : ZMod 7) 0 0 m = (0, 0))).card = 1 ∧
    (Finset.univ.filter (fun m : ZMod 7 => brokenSingleMaskHandoff (1 : ZMod 7) 1 0 m = (0, 0))).card = 0 ∧
    handoffTVD (1 : ZMod 7) (0 : ZMod 7) (1 : ZMod 7) = 0 :=
  ⟨by decide, by decide, handoffTVD_eq_zero 1 0 1⟩

end WitnessesAndTeeth

/-! ## §5. `#guard_msgs`-Pinned `#print axioms` Audit -/

/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.wyL_isStrictLowerTri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyL_isStrictLowerTri
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.solveStatefulWy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms solveStatefulWy_spec
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.gdnPrefix_eq_stateful_wy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnPrefix_eq_stateful_wy
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.wyStatefulChunk_eq_sequential_gdn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyStatefulChunk_eq_sequential_gdn
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.wyStatefulReadout_eq_sequential_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyStatefulReadout_eq_sequential_readout
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.chunkedGdnChain_eq_sequential_gdn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms chunkedGdnChain_eq_sequential_gdn
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.CarryVerifierState.byteFootprint_const' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms CarryVerifierState.byteFootprint_const
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.verifyStreamingCarryChain_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyStreamingCarryChain_invariants
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.stepCarryChainDigest_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepCarryChainDigest_eq_or_collision
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.streamingCarryChain_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms streamingCarryChain_eq_or_collision
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.union_bound_fin_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms union_bound_fin_prob
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.streamingCarryChain_soundness_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms streamingCarryChain_soundness_union_bound
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.dualMaskHandoff_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dualMaskHandoff_bijective
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.dualMaskHandoff_binding_of_isUnit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dualMaskHandoff_binding_of_isUnit
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.handoffTranscriptProb_eq_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms handoffTranscriptProb_eq_uniform
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.handoffTVD_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms handoffTVD_eq_zero
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.babyBearExt4_handoffTVD_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms babyBearExt4_handoffTVD_eq_zero
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.multiChunk_stateful_wy_witness_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms multiChunk_stateful_wy_witness_int
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.multiChunk_witness_zmod16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms multiChunk_witness_zmod16
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.tooth_silent_s_init_zero_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_silent_s_init_zero_reset
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.tooth_chunk_reorder_splice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_chunk_reorder_splice
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.tooth_dropped_kc_sc_wy_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_dropped_kc_sc_wy_coupling
/-- info: 'Minidregg.Assurance.StreamingGdnCarryIvc.tooth_reused_single_mask_breaks_tvd_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_reused_single_mask_breaks_tvd_zero

end Minidregg.Assurance.StreamingGdnCarryIvc
