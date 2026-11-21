/-
# `Theory/ExactKktClearingCert.lean` — `FHQPB001` Exact `O(|E|)` SDD-to-PSD, KKT & Multilateral Netting
Mathlib-only (`Theory/` tier). `0 sorry`, `0` custom `axiom`, `0 native_decide`, `0 #guard`.
Quarries `breadstuffs/fhir` (`FHQPB001`/`FHSDD001`) and `Obend.Judge.{Clearing,Netting}` over `ℤ`/`ℚ`:
- Part A: `sddFactor_quadForm_eq`, `sddFactor_implies_psd`, `scaled_dd_implies_psd`, `checkSddRowDomInt_implies_psd` + teeth.
- Part B: `primal_sub_dual_eq_compGap`, `lagrangian_weak_duality`, `kkt_bounded_gap_global_optimal`,
  `kkt_complementary_slackness_exact_optimal`, `checkFhqpb001BundleInt_sound` + Matrix-Pin/sign/gap teeth.
- Part C: `sum_netBalance_eq_zero`, `checkMultilateralNetting_sound`, `fhqpb001_clearing_and_netting_keystone`,
  `clearing_and_netting_joint_witness` + value-creation/exposure-inflation teeth.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Minidregg.Theory.ExactKktClearingCert

open Matrix
open scoped BigOperators
set_option autoImplicit false

private theorem finset_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℚ) (d : ℚ) :
    (∑ i ∈ s, f i / d) = (∑ i ∈ s, f i) / d := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul]

/-! ## Part A. `O(|E|)` SDD Factor Decomposition & Integer/Rational PSD Convexity (`FHQPB001`) -/

def quadForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := dotProduct x (Q.mulVec x)

structure PsdSymm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) : Prop where
  symm : Matrix.IsSymm Q
  psd  : ∀ x : Fin n → ℚ, 0 ≤ quadForm Q x

/-- 2-sparse scaled-incidence SDD factor edge `b_e = α e_u + β e_v` with weight `w_e : ℚ`. -/
structure SddEdge (n : ℕ) where
  (u v : Fin n)
  (alpha beta weight : ℚ)
  deriving DecidableEq, Repr

def SddEdge.vec {n : ℕ} (e : SddEdge n) : Fin n → ℚ :=
  fun i => (if i = e.u then e.alpha else 0) + (if i = e.v then e.beta else 0)

def SddEdge.eval {n : ℕ} (e : SddEdge n) (x : Fin n → ℚ) : ℚ := e.alpha * x e.u + e.beta * x e.v

theorem SddEdge.eval_eq_dotProduct {n : ℕ} (e : SddEdge n) (x : Fin n → ℚ) :
    e.eval x = dotProduct e.vec x := by
  unfold SddEdge.eval SddEdge.vec dotProduct
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

def SddEdge.outerMatrix {n : ℕ} (e : SddEdge n) : Matrix (Fin n) (Fin n) ℚ :=
  e.weight • Matrix.vecMulVec e.vec e.vec

theorem SddEdge.outerMatrix_isSymm {n : ℕ} (e : SddEdge n) : Matrix.IsSymm e.outerMatrix := by
  rw [Matrix.IsSymm.ext_iff]; intro i j
  simp only [SddEdge.outerMatrix, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]; ring

theorem SddEdge.quadForm_outerMatrix {n : ℕ} (e : SddEdge n) (x : Fin n → ℚ) :
    quadForm e.outerMatrix x = e.weight * (e.eval x) ^ 2 := by
  rw [SddEdge.eval_eq_dotProduct]; unfold quadForm SddEdge.outerMatrix
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  calc
    (∑ i : Fin n, x i * ∑ j : Fin n, e.weight * (e.vec i * e.vec j) * x j)
      = e.weight * (∑ i : Fin n, e.vec i * x i) * (∑ j : Fin n, e.vec j * x j) := by
          simp_rw [Finset.mul_sum]; congr 1; ext i; simp_rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = e.weight * (∑ i : Fin n, e.vec i * x i) ^ 2 := by ring

def sddEdgeSum {n : ℕ} : List (SddEdge n) → Matrix (Fin n) (Fin n) ℚ
  | [] => 0
  | e :: rest => e.outerMatrix + sddEdgeSum rest

/-- Complete SDD factor decomposition `Q = ∑_{e ∈ E} w_e b_e b_eᵀ + diag(d)`. -/
def sddFactorMatrix {n : ℕ} (edges : List (SddEdge n)) (d : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  sddEdgeSum edges + Matrix.diagonal d

def SddFactorValid {n : ℕ} (edges : List (SddEdge n)) (d : Fin n → ℚ) : Prop :=
  (∀ e ∈ edges, 0 ≤ e.weight) ∧ (∀ i : Fin n, 0 ≤ d i)

theorem quadForm_add {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    quadForm (M₁ + M₂) x = quadForm M₁ x + quadForm M₂ x := by
  unfold quadForm; rw [Matrix.add_mulVec, dotProduct_add]

theorem quadForm_zero {n : ℕ} (x : Fin n → ℚ) : quadForm (0 : Matrix (Fin n) (Fin n) ℚ) x = 0 := by
  unfold quadForm; simp

theorem quadForm_diagonal {n : ℕ} (d : Fin n → ℚ) (x : Fin n → ℚ) :
    quadForm (Matrix.diagonal d) x = ∑ i : Fin n, d i * (x i) ^ 2 := by
  unfold quadForm; simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sddEdgeSum_isSymm {n : ℕ} : ∀ (edges : List (SddEdge n)), Matrix.IsSymm (sddEdgeSum edges)
  | [] => Matrix.isSymm_zero
  | e :: rest => e.outerMatrix_isSymm.add (sddEdgeSum_isSymm rest)

theorem sddEdgeSum_quadForm {n : ℕ} : ∀ (edges : List (SddEdge n)) (x : Fin n → ℚ),
    quadForm (sddEdgeSum edges) x = (edges.map (fun e => e.weight * (e.eval x) ^ 2)).sum
  | [], _ => by simp [sddEdgeSum, quadForm_zero]
  | e :: rest, x => by
      simp only [sddEdgeSum, List.map_cons, List.sum_cons]
      rw [quadForm_add, e.quadForm_outerMatrix, sddEdgeSum_quadForm rest x]

/-- **`O(|E| + n)` Sum-of-Squares Identity (`sddFactor_quadForm_eq`)** (`0` sqrts, `0` floats). -/
theorem sddFactor_quadForm_eq {n : ℕ} (edges : List (SddEdge n)) (d : Fin n → ℚ) (x : Fin n → ℚ) :
    quadForm (sddFactorMatrix edges d) x =
      (edges.map (fun e => e.weight * (e.eval x) ^ 2)).sum + ∑ i : Fin n, d i * (x i) ^ 2 := by
  unfold sddFactorMatrix; rw [quadForm_add, sddEdgeSum_quadForm, quadForm_diagonal]

private theorem list_sum_nonneg_of_forall {l : List ℚ} (h : ∀ z ∈ l, (0 : ℚ) ≤ z) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a rest ih => exact add_nonneg (h a (List.Mem.head rest)) (ih fun z hz => h z (List.Mem.tail a hz))

/-- **Keystone A1 (`sddFactor_implies_psd` — `FHQPB001` Core Factor Law)**:
Whenever `w_e ≥ 0` and `d_i ≥ 0`, `Q = ∑_{e ∈ E} w_e b_e b_eᵀ + diag(d)` is symmetric PSD. -/
theorem sddFactor_implies_psd {n : ℕ} {edges : List (SddEdge n)} {d : Fin n → ℚ}
    (hvalid : SddFactorValid edges d) : PsdSymm (sddFactorMatrix edges d) := by
  refine ⟨(sddEdgeSum_isSymm edges).add (Matrix.isSymm_diagonal d), fun x => ?_⟩
  rw [sddFactor_quadForm_eq]
  refine add_nonneg (list_sum_nonneg_of_forall fun z hz => ?_)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hvalid.2 i) (sq_nonneg _))
  rcases List.mem_map.mp hz with ⟨e, he, rfl⟩
  exact mul_nonneg (hvalid.1 e he) (sq_nonneg _)

structure ScaledDiagonallyDominant {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (s : Fin n → ℚ) : Prop where
  symm         : Matrix.IsSymm Q
  scale_pos    : ∀ i : Fin n, 0 < s i
  row_dominant : ∀ i : Fin n, (∑ j ∈ Finset.univ.erase i, |Q i j| * s j) ≤ Q i i * s i

theorem scaled_offdiag_pair_nonneg (a s_u s_v x y : ℚ) (hsu : 0 < s_u) (hsv : 0 < s_v) :
    0 ≤ 2 * a * x * y + (|a| * s_v / s_u) * x ^ 2 + (|a| * s_u / s_v) * y ^ 2 := by
  have hprod : 0 < s_u * s_v := mul_pos hsu hsv
  have hsu_ne : s_u ≠ 0 := ne_of_gt hsu
  have hsv_ne : s_v ≠ 0 := ne_of_gt hsv
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have hsq : 0 ≤ (a / (s_u * s_v)) * (s_v * x + s_u * y) ^ 2 :=
      mul_nonneg (div_nonneg ha (le_of_lt hprod)) (sq_nonneg _)
    have hid : (a / (s_u * s_v)) * (s_v * x + s_u * y) ^ 2 =
        2 * a * x * y + (a * s_v / s_u) * x ^ 2 + (a * s_u / s_v) * y ^ 2 := by field_simp [hsu_ne, hsv_ne]; ring
    linarith
  · have hna : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos hna]
    have hsq : 0 ≤ (-a / (s_u * s_v)) * (s_v * x - s_u * y) ^ 2 :=
      mul_nonneg (div_nonneg (neg_nonneg.mpr hna) (le_of_lt hprod)) (sq_nonneg _)
    have hid : (-a / (s_u * s_v)) * (s_v * x - s_u * y) ^ 2 =
        2 * a * x * y + (-a * s_v / s_u) * x ^ 2 + (-a * s_u / s_v) * y ^ 2 := by field_simp [hsu_ne, hsv_ne]; ring
    linarith

/-- **Keystone A2 (`scaled_dd_implies_psd`)**: Every symmetric SDD rational matrix is PSD. -/
theorem scaled_dd_implies_psd {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {s : Fin n → ℚ}
    (hsdd : ScaledDiagonallyDominant Q s) : PsdSymm Q := by
  refine ⟨hsdd.symm, fun x => ?_⟩
  let rE : ℚ := ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, |Q i j| * s j / s i) * (x i) ^ 2
  let dE : ℚ := ∑ i : Fin n, Q i i * (x i) ^ 2
  let oE : ℚ := ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, Q i j * x i * x j
  have hdecomp : quadForm Q x = dE + oE := by
    unfold quadForm dE oE; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    calc
      (∑ i : Fin n, ∑ j : Fin n, x i * (Q i j * x j)) =
          ∑ i : Fin n, (x i * (Q i i * x i) + ∑ j ∈ Finset.univ.erase i, x i * (Q i j * x j)) :=
        Finset.sum_congr rfl fun i _ =>
          (Finset.add_sum_erase Finset.univ (fun j => x i * (Q i j * x j)) (Finset.mem_univ i)).symm
      _ = (∑ i : Fin n, Q i i * (x i) ^ 2) + ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, Q i j * x i * x j := by
        rw [Finset.sum_add_distrib]; congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hd_ge_r : rE ≤ dE := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg (x i))
    rw [finset_sum_div, div_le_iff₀ (hsdd.scale_pos i)]; exact hsdd.row_dominant i
  have hswap : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (|Q i j| * s i / s j) * (x j) ^ 2) = rE := by
    have hfull : (∑ i : Fin n, ∑ j : Fin n, (|Q i j| * s i / s j) * (x j) ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, (|Q i j| * s j / s i) * (x i) ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hsdd.symm.apply j i]
    unfold rE; simp_rw [Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hfull]
  have hpair : 0 ≤ 2 * oE + 2 * rE := by
    have hsum : 0 ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (2 * Q i j * x i * x j + (|Q i j| * s j / s i) * (x i) ^ 2 + (|Q i j| * s i / s j) * (x j) ^ 2) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        scaled_offdiag_pair_nonneg (Q i j) (s i) (s j) (x i) (x j) (hsdd.scale_pos i) (hsdd.scale_pos j)
    have hc1 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, 2 * Q i j * x i * x j) = 2 * oE := by
      unfold oE; simp_rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hc2 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (|Q i j| * s j / s i) * (x i) ^ 2) = rE :=
      Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    simp_rw [Finset.sum_add_distrib] at hsum; rw [hc1, hc2, hswap] at hsum; linarith
  rw [hdecomp]; linarith

def liftScaledIntMat {r c : ℕ} (S : ℕ) (P : Matrix (Fin r) (Fin c) ℤ) : Matrix (Fin r) (Fin c) ℚ :=
  Matrix.of fun i j => (P i j : ℚ) / (S : ℚ)

def liftScaledIntVec {m : ℕ} (D : ℚ) (v : Fin m → ℤ) : Fin m → ℚ := fun i => (v i : ℚ) / D

/-- Executable `FHSDD001` exact-integer symmetric row-diagonal-dominance checker. -/
def checkSddRowDomInt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  (List.finRange n).all fun i =>
    (List.finRange n).all (fun j => decide (P i j = P j i)) && decide (0 ≤ P i i) &&
    decide (((List.finRange n).map (fun j => if j = i then (0 : ℤ) else |P i j|)).sum ≤ P i i)

private theorem list_finRange_offdiag_eq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    ((List.finRange n).map (fun j => if j = i then (0 : ℤ) else |P i j|)).sum =
      ∑ j ∈ Finset.univ.erase i, |P i j| := by
  have huniv : (List.finRange n).toFinset = (Finset.univ : Finset (Fin n)) := by ext j; simp
  rw [← List.sum_toFinset _ (List.nodup_finRange n), huniv, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [↓reduceIte, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : j ≠ i := Finset.ne_of_mem_erase hj; simp [hne]

/-- **Executable `FHSDD001` Soundness (`checkSddRowDomInt_implies_psd`)**. -/
theorem checkSddRowDomInt_implies_psd {n : ℕ} {S : ℕ} (hS : 0 < S)
    {P : Matrix (Fin n) (Fin n) ℤ} (hchk : checkSddRowDomInt P = true) :
    PsdSymm (liftScaledIntMat S P) := by
  have hS_pos : (0 : ℚ) < (S : ℚ) := Nat.cast_pos.mpr hS
  apply scaled_dd_implies_psd (s := fun _ => 1)
  unfold checkSddRowDomInt at hchk; rw [List.all_eq_true] at hchk
  refine ⟨?_, fun _ => zero_lt_one, ?_⟩
  · rw [Matrix.IsSymm.ext_iff]; intro i j
    have hi := hchk i (List.mem_finRange i)
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hi
    simp [liftScaledIntMat, hi.1.1 j (List.mem_finRange j)]
  · intro i
    have hi := hchk i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [list_finRange_offdiag_eq] at hi
    have hdom : (∑ j ∈ Finset.univ.erase i, |(P i j : ℚ)|) ≤ (P i i : ℚ) := by exact_mod_cast hi.2
    have hlhs : (∑ j ∈ Finset.univ.erase i, |liftScaledIntMat S P i j| * 1) =
        (∑ j ∈ Finset.univ.erase i, |(P i j : ℚ)|) / (S : ℚ) := by
      rw [← finset_sum_div]
      exact Finset.sum_congr rfl fun j _ => by simp [liftScaledIntMat, abs_div, abs_of_pos hS_pos]
    rw [hlhs]; simpa [liftScaledIntMat] using div_le_div_of_nonneg_right hdom (le_of_lt hS_pos)

/-- **Tooth A1**: Negative edge weight `w = -1` makes `sddFactorMatrix` indefinite (`-4 < 0`). -/
theorem tooth_negative_edge_weight_not_psd :
    let Q := sddFactorMatrix ([⟨0, 1, 1, 1, -1⟩] : List (SddEdge 2)) (fun _ => 0)
    quadForm Q ![1, 1] < 0 ∧ ¬ PsdSymm Q := by
  dsimp only
  have hval : quadForm (sddFactorMatrix ([⟨0, 1, 1, 1, -1⟩] : List (SddEdge 2)) (fun _ => 0)) ![1, 1] = -4 := by
    rw [sddFactor_quadForm_eq]; simp [SddEdge.eval]; norm_num
  exact ⟨by linarith, fun hpsd => by have := hpsd.psd ![1, 1]; linarith⟩

def indefinite2Int : Matrix (Fin 2) (Fin 2) ℤ := ![![1, 2], ![2, 1]]

/-- **Tooth A2**: `[[1,2],[2,1]]` refused by `checkSddRowDomInt` and has energy `-2 < 0` at `![1, -1]`. -/
theorem tooth_indefinite2_refused_and_not_psd :
    checkSddRowDomInt indefinite2Int = false ∧
    quadForm (liftScaledIntMat 1 indefinite2Int) ![1, -1] = -2 ∧
    ¬ PsdSymm (liftScaledIntMat 1 indefinite2Int) := by
  have href : checkSddRowDomInt indefinite2Int = false := by decide
  have hqf : quadForm (liftScaledIntMat 1 indefinite2Int) ![1, -1] = -2 := by
    simp [quadForm, liftScaledIntMat, indefinite2Int, dotProduct, Matrix.mulVec, Fin.sum_univ_two]; norm_num
  exact ⟨href, hqf, fun hpsd => by have := hpsd.psd ![1, -1]; linarith⟩

/-! ## Part B. Primal-Dual KKT Convex QP, `p* - d* ≤ ε` Global Optimality & `FHQPB001` Bundle -/

structure ConvexQp (n meq mineq : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℚ
  q : Fin n → ℚ
  A : Matrix (Fin meq) (Fin n) ℚ
  b : Fin meq → ℚ
  G : Matrix (Fin mineq) (Fin n) ℚ
  h : Fin mineq → ℚ
  (l u : Fin n → ℚ)

def primalObj {n meq mineq : ℕ} (qp : ConvexQp n meq mineq) (x : Fin n → ℚ) : ℚ :=
  (1 / 2 : ℚ) * quadForm qp.Q x + dotProduct qp.q x

def PrimalFeasible {n meq mineq : ℕ} (qp : ConvexQp n meq mineq) (x : Fin n → ℚ) : Prop :=
  qp.A.mulVec x = qp.b ∧ (∀ k : Fin mineq, (qp.G.mulVec x) k ≤ qp.h k) ∧
  (∀ i : Fin n, qp.l i ≤ x i) ∧ (∀ i : Fin n, x i ≤ qp.u i)

structure DualWitness (n meq mineq : ℕ) where
  nu : Fin meq → ℚ
  mu : Fin mineq → ℚ
  (lamL lamU : Fin n → ℚ)

def DualNonneg {n meq mineq : ℕ} (dw : DualWitness n meq mineq) : Prop :=
  (∀ k : Fin mineq, 0 ≤ dw.mu k) ∧ (∀ i : Fin n, 0 ≤ dw.lamL i) ∧ (∀ i : Fin n, 0 ≤ dw.lamU i)

def KktStationary {n meq mineq : ℕ} (qp : ConvexQp n meq mineq)
    (x : Fin n → ℚ) (dw : DualWitness n meq mineq) : Prop :=
  ∀ i : Fin n,
    (qp.Q.mulVec x) i + qp.q i + (qp.Aᵀ.mulVec dw.nu) i + (qp.Gᵀ.mulVec dw.mu) i - dw.lamL i + dw.lamU i = 0

def dualObj {n meq mineq : ℕ} (qp : ConvexQp n meq mineq) (x : Fin n → ℚ) (dw : DualWitness n meq mineq) : ℚ :=
  -(1 / 2 : ℚ) * quadForm qp.Q x - dotProduct qp.b dw.nu - dotProduct qp.h dw.mu +
    dotProduct qp.l dw.lamL - dotProduct qp.u dw.lamU

def compGap {n meq mineq : ℕ} (qp : ConvexQp n meq mineq) (x : Fin n → ℚ) (dw : DualWitness n meq mineq) : ℚ :=
  dotProduct dw.mu (qp.h - qp.G.mulVec x) + dotProduct dw.lamL (x - qp.l) + dotProduct dw.lamU (qp.u - x)

theorem quad_bilin_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} (hsym : Matrix.IsSymm Q)
    (x y : Fin n → ℚ) : dotProduct y (Q.mulVec x) = dotProduct x (Q.mulVec y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym.eq, dotProduct_comm]

theorem primalObj_grad_identity {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    (hsym : Matrix.IsSymm qp.Q) (x y : Fin n → ℚ) :
    primalObj qp y - primalObj qp x - dotProduct (qp.Q.mulVec x + qp.q) (y - x) =
      (1 / 2 : ℚ) * quadForm qp.Q (y - x) := by
  have hxy := quad_bilin_symm hsym x y; unfold primalObj quadForm
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, add_dotProduct]
  rw [dotProduct_comm (qp.Q.mulVec x) y, dotProduct_comm (qp.Q.mulVec x) x, hxy]; ring

theorem quad_convex_ge {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    (hQ : PsdSymm qp.Q) (x y : Fin n → ℚ) :
    dotProduct (qp.Q.mulVec x + qp.q) (y - x) ≤ primalObj qp y - primalObj qp x := by
  linarith [primalObj_grad_identity (qp := qp) hQ.symm x y, hQ.psd (y - x)]

private theorem transpose_mulVec_dotProduct {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℚ)
    (u : Fin r → ℚ) (v : Fin c → ℚ) : dotProduct (Mᵀ.mulVec u) v = dotProduct u (M.mulVec v) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Exact Primal-Dual Gap Identity (`primal_sub_dual_eq_compGap`)**: `p* - d* = compGap`. -/
theorem primal_sub_dual_eq_compGap {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    {x : Fin n → ℚ} {dw : DualWitness n meq mineq}
    (heq : qp.A.mulVec x = qp.b) (hstat : KktStationary qp x dw) :
    primalObj qp x - dualObj qp x dw = compGap qp x dw := by
  have hq : qp.q = -(qp.Q.mulVec x) - qp.Aᵀ.mulVec dw.nu - qp.Gᵀ.mulVec dw.mu + dw.lamL - dw.lamU := by
    funext i; have hi := hstat i; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; linarith
  have hqx : dotProduct qp.q x =
      -quadForm qp.Q x - dotProduct dw.nu qp.b - dotProduct dw.mu (qp.G.mulVec x) +
        dotProduct dw.lamL x - dotProduct dw.lamU x := by
    conv_lhs => rw [hq]
    simp only [sub_dotProduct, add_dotProduct, neg_dotProduct]
    rw [transpose_mulVec_dotProduct qp.A dw.nu x, heq, transpose_mulVec_dotProduct qp.G dw.mu x]
    have hqf : dotProduct (qp.Q.mulVec x) x = quadForm qp.Q x := dotProduct_comm _ _
    rw [hqf]
  unfold primalObj dualObj compGap
  rw [hqx, dotProduct_comm qp.b dw.nu, dotProduct_comm qp.h dw.mu,
      dotProduct_comm qp.l dw.lamL, dotProduct_comm qp.u dw.lamU]
  simp only [dotProduct_sub]; ring

theorem compGap_nonneg {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    {x : Fin n → ℚ} {dw : DualWitness n meq mineq}
    (hfeas : PrimalFeasible qp x) (hdnn : DualNonneg dw) : 0 ≤ compGap qp x dw := by
  unfold compGap dotProduct
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (hdnn.1 k) (by simp; linarith [hfeas.2.1 k])
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hdnn.2.1 i) (by simp; linarith [hfeas.2.2.1 i])
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hdnn.2.2 i) (by simp; linarith [hfeas.2.2.2 i])

/-- **Lagrangian Weak Duality (`lagrangian_weak_duality`)**: `dualObj qp x dw ≤ primalObj qp y`. -/
theorem lagrangian_weak_duality {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    (hQ : PsdSymm qp.Q) {x : Fin n → ℚ} {dw : DualWitness n meq mineq}
    (hdnn : DualNonneg dw) (hstat : KktStationary qp x dw)
    {y : Fin n → ℚ} (hfeasY : PrimalFeasible qp y) : dualObj qp x dw ≤ primalObj qp y := by
  have hconv := quad_convex_ge hQ x y
  have hq_eq : qp.q = -(qp.Q.mulVec x) - qp.Aᵀ.mulVec dw.nu - qp.Gᵀ.mulVec dw.mu + dw.lamL - dw.lamU := by
    funext i; have hi := hstat i; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; linarith
  have hexpand : primalObj qp x + dotProduct (qp.Q.mulVec x + qp.q) (y - x) =
      dualObj qp x dw + compGap qp y dw := by
    unfold primalObj dualObj compGap; conv_lhs => rw [hq_eq]
    simp only [sub_dotProduct, add_dotProduct, neg_dotProduct, dotProduct_sub]
    rw [transpose_mulVec_dotProduct qp.A dw.nu x, transpose_mulVec_dotProduct qp.A dw.nu y,
        hfeasY.1, transpose_mulVec_dotProduct qp.G dw.mu x, transpose_mulVec_dotProduct qp.G dw.mu y,
        dotProduct_comm qp.b dw.nu, dotProduct_comm qp.h dw.mu,
        dotProduct_comm qp.l dw.lamL, dotProduct_comm qp.u dw.lamU]
    have hqf : dotProduct (qp.Q.mulVec x) x = quadForm qp.Q x := dotProduct_comm _ _
    rw [hqf]; ring
  linarith [compGap_nonneg hfeasY hdnn]

/-- **Keystone B1 (`kkt_bounded_gap_global_optimal` — Bounded Optimality Gap `p* - d* ≤ ε`)**. -/
theorem kkt_bounded_gap_global_optimal {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    (hQ : PsdSymm qp.Q) {x : Fin n → ℚ} {dw : DualWitness n meq mineq} {ε : ℚ}
    (_hfeasX : PrimalFeasible qp x) (hdnn : DualNonneg dw) (hstat : KktStationary qp x dw)
    (hgap : primalObj qp x - dualObj qp x dw ≤ ε) {y : Fin n → ℚ} (hfeasY : PrimalFeasible qp y) :
    primalObj qp x ≤ primalObj qp y + ε := by
  linarith [lagrangian_weak_duality hQ hdnn hstat hfeasY]

/-- **Keystone B2 (`kkt_complementary_slackness_exact_optimal` — Exact Zero-Gap KKT)**. -/
theorem kkt_complementary_slackness_exact_optimal {n meq mineq : ℕ} {qp : ConvexQp n meq mineq}
    (hQ : PsdSymm qp.Q) {x : Fin n → ℚ} {dw : DualWitness n meq mineq}
    (hfeasX : PrimalFeasible qp x) (hdnn : DualNonneg dw) (hstat : KktStationary qp x dw)
    (hcs_mu : ∀ k : Fin mineq, dw.mu k * (qp.h k - (qp.G.mulVec x) k) = 0)
    (hcs_l  : ∀ i : Fin n, dw.lamL i * (x i - qp.l i) = 0)
    (hcs_u  : ∀ i : Fin n, dw.lamU i * (qp.u i - x i) = 0) :
    primalObj qp x = dualObj qp x dw ∧
    ∀ y : Fin n → ℚ, PrimalFeasible qp y → primalObj qp x ≤ primalObj qp y := by
  have hcg0 : compGap qp x dw = 0 := by
    unfold compGap dotProduct; simp only [Pi.sub_apply]
    rw [Finset.sum_eq_zero fun k _ => hcs_mu k,
        Finset.sum_eq_zero fun i _ => hcs_l i,
        Finset.sum_eq_zero fun i _ => hcs_u i]; ring
  have heq_pd : primalObj qp x = dualObj qp x dw := by linarith [primal_sub_dual_eq_compGap hfeasX.1 hstat]
  exact ⟨heq_pd, fun y hy => by linarith [kkt_bounded_gap_global_optimal hQ hfeasX hdnn hstat (ε := 0) (by linarith) hy]⟩

/-! ### Executable Fixed-Point Integer `FHQPB001` Bundle & Matrix-Pin Checker -/

structure SddEdgeInt (n : ℕ) where
  (u v : Fin n)
  (alpha beta weight : ℤ)
  deriving DecidableEq, Repr

def SddEdgeInt.toRatScaled {n : ℕ} (S : ℕ) (e : SddEdgeInt n) : SddEdge n :=
  ⟨e.u, e.v, (e.alpha : ℚ), (e.beta : ℚ), (e.weight : ℚ) / (S : ℚ)⟩

def SddEdgeInt.vecInt {n : ℕ} (e : SddEdgeInt n) : Fin n → ℤ :=
  fun i => (if i = e.u then e.alpha else 0) + (if i = e.v then e.beta else 0)

def sddFactorMatrixInt {n : ℕ} (edges : List (SddEdgeInt n)) (d : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  (edges.map (fun e => e.weight • Matrix.vecMulVec e.vecInt e.vecInt)).sum + Matrix.diagonal d

structure Fhqpb001BundleInt (n meq mineq : ℕ) where
  scaleDenom : ℕ
  edges      : List (SddEdgeInt n)
  diagSlack  : Fin n → ℤ
  Q_int      : Matrix (Fin n) (Fin n) ℤ
  q_int      : Fin n → ℤ
  A_int      : Matrix (Fin meq) (Fin n) ℤ
  b_int      : Fin meq → ℤ
  G_int      : Matrix (Fin mineq) (Fin n) ℤ
  h_int      : Fin mineq → ℤ
  (l_int u_int x_int lamL_int lamU_int : Fin n → ℤ)
  nu_int     : Fin meq → ℤ
  mu_int     : Fin mineq → ℤ
  eps_int    : ℤ

def Fhqpb001BundleInt.decodeQp {n meq mineq : ℕ} (B : Fhqpb001BundleInt n meq mineq) : ConvexQp n meq mineq :=
  { Q := liftScaledIntMat B.scaleDenom B.Q_int
    q := liftScaledIntVec ((B.scaleDenom : ℚ) ^ 2) B.q_int
    A := liftScaledIntMat B.scaleDenom B.A_int
    b := liftScaledIntVec ((B.scaleDenom : ℚ) ^ 2) B.b_int
    G := liftScaledIntMat B.scaleDenom B.G_int
    h := liftScaledIntVec ((B.scaleDenom : ℚ) ^ 2) B.h_int
    l := liftScaledIntVec (B.scaleDenom : ℚ) B.l_int
    u := liftScaledIntVec (B.scaleDenom : ℚ) B.u_int }

def Fhqpb001BundleInt.decodePrimal {n meq mineq : ℕ} (B : Fhqpb001BundleInt n meq mineq) : Fin n → ℚ :=
  liftScaledIntVec (B.scaleDenom : ℚ) B.x_int

def Fhqpb001BundleInt.decodeDual {n meq mineq : ℕ} (B : Fhqpb001BundleInt n meq mineq) : DualWitness n meq mineq :=
  { nu   := liftScaledIntVec (B.scaleDenom : ℚ) B.nu_int
    mu   := liftScaledIntVec (B.scaleDenom : ℚ) B.mu_int
    lamL := liftScaledIntVec ((B.scaleDenom : ℚ) ^ 2) B.lamL_int
    lamU := liftScaledIntVec ((B.scaleDenom : ℚ) ^ 2) B.lamU_int }

def Fhqpb001BundleInt.decodeEps {n meq mineq : ℕ} (B : Fhqpb001BundleInt n meq mineq) : ℚ :=
  (B.eps_int : ℚ) / ((B.scaleDenom : ℚ) ^ 3)

def intDot {m : ℕ} (u v : Fin m → ℤ) : ℤ := ((List.finRange m).map (fun i => u i * v i)).sum

private theorem intDot_eq_dotProduct {m : ℕ} (u v : Fin m → ℤ) : intDot u v = dotProduct u v := by
  unfold intDot dotProduct
  have huniv : (List.finRange m).toFinset = (Finset.univ : Finset (Fin m)) := by ext j; simp
  rw [← List.sum_toFinset _ (List.nodup_finRange m), huniv]

def intMulVec {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (v : Fin c → ℤ) (i : Fin r) : ℤ :=
  intDot (fun j => M i j) v

private theorem intMulVec_eq_mulVec {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℤ) (v : Fin c → ℤ)
    (i : Fin r) : intMulVec M v i = (M.mulVec v) i := intDot_eq_dotProduct (fun j => M i j) v

/-- Executable division-free `ℤ` verifier for `FHQPB001` (`0` floats, `0` sqrts, `0` divisions). -/
def checkFhqpb001BundleInt {n meq mineq : ℕ} (B : Fhqpb001BundleInt n meq mineq) : Bool :=
  let F := sddFactorMatrixInt B.edges B.diagSlack
  let Gx := intMulVec B.G_int B.x_int
  let gapInt : ℤ :=
    intDot B.mu_int (fun k => B.h_int k - Gx k) +
      intDot B.lamL_int (fun i => B.x_int i - B.l_int i) + intDot B.lamU_int (fun i => B.u_int i - B.x_int i)
  decide (0 < B.scaleDenom) &&
  B.edges.all (fun e => decide (0 ≤ e.weight)) &&
  (List.finRange n).all (fun i => decide (0 ≤ B.diagSlack i)) &&
  (List.finRange n).all (fun i => (List.finRange n).all (fun j => decide (F i j = B.Q_int i j))) &&
  (List.finRange meq).all (fun r => decide (intMulVec B.A_int B.x_int r = B.b_int r)) &&
  (List.finRange mineq).all (fun k => decide (Gx k ≤ B.h_int k)) &&
  (List.finRange n).all (fun i => decide (B.l_int i ≤ B.x_int i && B.x_int i ≤ B.u_int i)) &&
  (List.finRange mineq).all (fun k => decide (0 ≤ B.mu_int k)) &&
  (List.finRange n).all (fun i => decide (0 ≤ B.lamL_int i && 0 ≤ B.lamU_int i)) &&
  (List.finRange n).all (fun i =>
    decide (intMulVec B.Q_int B.x_int i + B.q_int i + intMulVec B.A_intᵀ B.nu_int i +
      intMulVec B.G_intᵀ B.mu_int i - B.lamL_int i + B.lamU_int i = 0)) &&
  decide (gapInt ≤ B.eps_int)

private theorem sddEdgeSum_liftInt {n : ℕ} (S : ℕ) :
    ∀ (edges : List (SddEdgeInt n)) (i j : Fin n),
      sddEdgeSum (edges.map (SddEdgeInt.toRatScaled S)) i j =
        (((edges.map (fun e => e.weight • Matrix.vecMulVec e.vecInt e.vecInt)).sum i j : ℤ) : ℚ) / (S : ℚ)
  | [], _, _ => by simp [sddEdgeSum]
  | e :: rest, i, j => by
      simp only [List.map_cons, sddEdgeSum, List.sum_cons, Matrix.add_apply]
      rw [sddEdgeSum_liftInt S rest i j]
      simp only [SddEdge.outerMatrix, SddEdgeInt.toRatScaled, SddEdge.vec, SddEdgeInt.vecInt,
        Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
      push_cast; split_ifs <;> ring

private theorem sddFactorMatrix_liftInt_eq {n : ℕ} (S : ℕ)
    (edges : List (SddEdgeInt n)) (d : Fin n → ℤ) :
    sddFactorMatrix (edges.map (SddEdgeInt.toRatScaled S)) (liftScaledIntVec (S : ℚ) d) =
      liftScaledIntMat S (sddFactorMatrixInt edges d) := by
  ext i j
  unfold sddFactorMatrix sddFactorMatrixInt liftScaledIntMat liftScaledIntVec
  simp only [Matrix.add_apply, Matrix.of_apply]; rw [sddEdgeSum_liftInt S edges i j]
  by_cases hij : i = j
  · subst hij; simp only [Matrix.diagonal_apply_eq]; push_cast; ring
  · simp only [Matrix.diagonal_apply_ne _ hij]; push_cast; ring

private theorem liftScaledIntMat_transpose {r c : ℕ} (S : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) :
    (liftScaledIntMat S M)ᵀ = liftScaledIntMat S Mᵀ := by ext i j; rfl

private theorem mulVec_liftScaledInt {r c : ℕ} (S : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) (v : Fin c → ℤ) :
    (liftScaledIntMat S M).mulVec (liftScaledIntVec (S : ℚ) v) =
      liftScaledIntVec ((S : ℚ) ^ 2) (M.mulVec v) := by
  funext idx; unfold liftScaledIntMat liftScaledIntVec
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, div_mul_div_comm, ← sq]
  rw [finset_sum_div]; push_cast; rfl

private theorem dot_scale_cube12 {m : ℕ} {S : ℚ} (hS : S ≠ 0) (u v w : Fin m → ℤ) :
    (∑ i : Fin m, ((u i : ℚ) / S) * ((v i : ℚ) / S ^ 2 - (w i : ℚ) / S ^ 2)) =
      (∑ i : Fin m, (u i : ℚ) * ((v i : ℚ) - (w i : ℚ))) / S ^ 3 := by
  rw [← finset_sum_div]; exact Finset.sum_congr rfl fun _ _ => by field_simp [hS]

private theorem dot_scale_cube21 {m : ℕ} {S : ℚ} (hS : S ≠ 0) (u v w : Fin m → ℤ) :
    (∑ i : Fin m, ((u i : ℚ) / S ^ 2) * ((v i : ℚ) / S - (w i : ℚ) / S)) =
      (∑ i : Fin m, (u i : ℚ) * ((v i : ℚ) - (w i : ℚ))) / S ^ 3 := by
  rw [← finset_sum_div]; exact Finset.sum_congr rfl fun _ _ => by field_simp [hS]

/-- **Keystone B3 (`checkFhqpb001BundleInt_sound`)**:
Acceptance by `checkFhqpb001BundleInt` certifies `PsdSymm`, `PrimalFeasible`, `p* - d* ≤ ε`,
and global `ε`-optimality over **every** rational feasible contender `y : Fin n → ℚ`. -/
theorem checkFhqpb001BundleInt_sound {n meq mineq : ℕ} {B : Fhqpb001BundleInt n meq mineq}
    (hchk : checkFhqpb001BundleInt B = true) :
    PsdSymm B.decodeQp.Q ∧
    PrimalFeasible B.decodeQp B.decodePrimal ∧
    primalObj B.decodeQp B.decodePrimal - dualObj B.decodeQp B.decodePrimal B.decodeDual ≤ B.decodeEps ∧
    ∀ y : Fin n → ℚ, PrimalFeasible B.decodeQp y →
      primalObj B.decodeQp B.decodePrimal ≤ primalObj B.decodeQp y + B.decodeEps := by
  unfold checkFhqpb001BundleInt at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hedges⟩, hdiag⟩, hpin⟩, hAeq⟩, hGineq⟩, hbox⟩, hmu⟩, hlam⟩, hstatInt⟩, hgapInt⟩
  have hS_pos : (0 : ℚ) < (B.scaleDenom : ℚ) := Nat.cast_pos.mpr hS
  have hS_ne : (B.scaleDenom : ℚ) ≠ 0 := ne_of_gt hS_pos
  have hS2_pos : (0 : ℚ) < (B.scaleDenom : ℚ) ^ 2 := pow_pos hS_pos 2
  have hS3_pos : (0 : ℚ) < (B.scaleDenom : ℚ) ^ 3 := pow_pos hS_pos 3
  have hFactorValid : SddFactorValid (B.edges.map (SddEdgeInt.toRatScaled B.scaleDenom))
      (liftScaledIntVec (B.scaleDenom : ℚ) B.diagSlack) := by
    refine ⟨fun e he => ?_, fun i => ?_⟩
    · rcases List.mem_map.mp he with ⟨ei, hei, rfl⟩
      exact div_nonneg (by exact_mod_cast hedges ei hei) (le_of_lt hS_pos)
    · exact div_nonneg (by exact_mod_cast hdiag i (List.mem_finRange i)) (le_of_lt hS_pos)
  have hMatEq : sddFactorMatrix (B.edges.map (SddEdgeInt.toRatScaled B.scaleDenom))
      (liftScaledIntVec (B.scaleDenom : ℚ) B.diagSlack) = B.decodeQp.Q := by
    rw [sddFactorMatrix_liftInt_eq]; ext i j
    simp [Fhqpb001BundleInt.decodeQp, liftScaledIntMat, hpin i (List.mem_finRange i) j (List.mem_finRange j)]
  have hPsd : PsdSymm B.decodeQp.Q := hMatEq ▸ sddFactor_implies_psd hFactorValid
  have hFeas : PrimalFeasible B.decodeQp B.decodePrimal := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [Fhqpb001BundleInt.decodeQp, Fhqpb001BundleInt.decodePrimal]
      rw [mulVec_liftScaledInt]; funext r
      have hr := hAeq r (List.mem_finRange r); rw [intMulVec_eq_mulVec] at hr
      simp [liftScaledIntVec, hr]
    · intro k; dsimp only [Fhqpb001BundleInt.decodeQp, Fhqpb001BundleInt.decodePrimal]; rw [mulVec_liftScaledInt]
      have hk := hGineq k (List.mem_finRange k); rw [intMulVec_eq_mulVec] at hk
      exact div_le_div_of_nonneg_right (by exact_mod_cast hk) (le_of_lt hS2_pos)
    · exact fun i => div_le_div_of_nonneg_right (by exact_mod_cast (hbox i (List.mem_finRange i)).1) (le_of_lt hS_pos)
    · exact fun i => div_le_div_of_nonneg_right (by exact_mod_cast (hbox i (List.mem_finRange i)).2) (le_of_lt hS_pos)
  have hDnn : DualNonneg B.decodeDual :=
    ⟨fun k => div_nonneg (by exact_mod_cast hmu k (List.mem_finRange k)) (le_of_lt hS_pos),
     fun i => div_nonneg (by exact_mod_cast (hlam i (List.mem_finRange i)).1) (le_of_lt hS2_pos),
     fun i => div_nonneg (by exact_mod_cast (hlam i (List.mem_finRange i)).2) (le_of_lt hS2_pos)⟩
  have hStat : KktStationary B.decodeQp B.decodePrimal B.decodeDual := by
    intro i
    have hsi0 := hstatInt i (List.mem_finRange i)
    rw [intMulVec_eq_mulVec, intMulVec_eq_mulVec, intMulVec_eq_mulVec] at hsi0
    have hsi : (((B.Q_int.mulVec B.x_int) i : ℚ) + (B.q_int i : ℚ) +
        ((B.A_intᵀ.mulVec B.nu_int) i : ℚ) + ((B.G_intᵀ.mulVec B.mu_int) i : ℚ) -
        (B.lamL_int i : ℚ) + (B.lamU_int i : ℚ)) = 0 := by exact_mod_cast hsi0
    dsimp only [Fhqpb001BundleInt.decodeQp, Fhqpb001BundleInt.decodePrimal, Fhqpb001BundleInt.decodeDual]
    rw [liftScaledIntMat_transpose, liftScaledIntMat_transpose,
        mulVec_liftScaledInt, mulVec_liftScaledInt, mulVec_liftScaledInt]
    unfold liftScaledIntVec; field_simp [hS_ne]; linarith
  have hGap : primalObj B.decodeQp B.decodePrimal -
      dualObj B.decodeQp B.decodePrimal B.decodeDual ≤ B.decodeEps := by
    rw [primal_sub_dual_eq_compGap hFeas.1 hStat]
    have hgapEq : intDot B.mu_int (fun k => B.h_int k - intMulVec B.G_int B.x_int k) +
        intDot B.lamL_int (fun i => B.x_int i - B.l_int i) +
        intDot B.lamU_int (fun i => B.u_int i - B.x_int i) =
        dotProduct B.mu_int (B.h_int - B.G_int.mulVec B.x_int) +
        dotProduct B.lamL_int (B.x_int - B.l_int) +
        dotProduct B.lamU_int (B.u_int - B.x_int) := by
      rw [intDot_eq_dotProduct, intDot_eq_dotProduct, intDot_eq_dotProduct]
      have hfn : (fun k => B.h_int k - intMulVec B.G_int B.x_int k) = B.h_int - B.G_int.mulVec B.x_int := by
        funext k; simp [intMulVec_eq_mulVec]
      rw [hfn]; rfl
    rw [hgapEq] at hgapInt
    have hcg_scale : compGap B.decodeQp B.decodePrimal B.decodeDual =
        ((dotProduct B.mu_int (B.h_int - B.G_int.mulVec B.x_int) +
          dotProduct B.lamL_int (B.x_int - B.l_int) +
          dotProduct B.lamU_int (B.u_int - B.x_int) : ℤ) : ℚ) / ((B.scaleDenom : ℚ) ^ 3) := by
      unfold compGap
      dsimp only [Fhqpb001BundleInt.decodeQp, Fhqpb001BundleInt.decodePrimal, Fhqpb001BundleInt.decodeDual]
      rw [mulVec_liftScaledInt]; unfold liftScaledIntVec; simp only [dotProduct, Pi.sub_apply]
      rw [dot_scale_cube12 hS_ne B.mu_int B.h_int (B.G_int.mulVec B.x_int),
          dot_scale_cube21 hS_ne B.lamL_int B.x_int B.l_int,
          dot_scale_cube21 hS_ne B.lamU_int B.u_int B.x_int]
      push_cast; ring
    rw [hcg_scale]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hgapInt) (le_of_lt hS3_pos)
  exact ⟨hPsd, hFeas, hGap, fun y hy => kkt_bounded_gap_global_optimal hPsd hFeas hDnn hStat hGap hy⟩

/-! ### Part B Falsifier Teeth -/

def baseBundle1D : Fhqpb001BundleInt 1 0 0 :=
  { scaleDenom := 1, edges := [], diagSlack := fun _ => 1,
    Q_int := fun _ _ => 1, q_int := fun _ => -1,
    A_int := fun r => r.elim0, b_int := fun r => r.elim0,
    G_int := fun k => k.elim0, h_int := fun k => k.elim0,
    l_int := fun _ => 0, u_int := fun _ => 2, x_int := fun _ => 1,
    nu_int := fun r => r.elim0, mu_int := fun k => k.elim0,
    lamL_int := fun _ => 0, lamU_int := fun _ => 0, eps_int := 0 }

def unpinnedConcaveBundle : Fhqpb001BundleInt 1 0 0 :=
  { baseBundle1D with Q_int := fun _ _ => -1, q_int := fun _ => 0, x_int := fun _ => 0 }

/-- **Tooth B1 (`tooth_matrix_pin_omitted_unsound`)**: unpinned concave `Q = -1` rejected by Matrix Pin. -/
theorem tooth_matrix_pin_omitted_unsound :
    checkFhqpb001BundleInt unpinnedConcaveBundle = false ∧
    PrimalFeasible unpinnedConcaveBundle.decodeQp (fun _ => 1) ∧
    primalObj unpinnedConcaveBundle.decodeQp (fun _ => 1) <
      primalObj unpinnedConcaveBundle.decodeQp unpinnedConcaveBundle.decodePrimal := by
  have href : checkFhqpb001BundleInt unpinnedConcaveBundle = false := by decide
  refine ⟨href, ⟨by funext r; exact r.elim0, fun k => k.elim0, ?_, ?_⟩, ?_⟩
  · intro i; fin_cases i; norm_num [unpinnedConcaveBundle, baseBundle1D, Fhqpb001BundleInt.decodeQp, liftScaledIntVec]
  · intro i; fin_cases i; norm_num [unpinnedConcaveBundle, baseBundle1D, Fhqpb001BundleInt.decodeQp, liftScaledIntVec]
  · simp [primalObj, quadForm, unpinnedConcaveBundle, baseBundle1D, Fhqpb001BundleInt.decodeQp,
      Fhqpb001BundleInt.decodePrimal, liftScaledIntMat, liftScaledIntVec, dotProduct, Matrix.mulVec]

def forgedWrongSignDualBundle : Fhqpb001BundleInt 1 0 0 :=
  { baseBundle1D with x_int := fun _ => 0, lamL_int := fun _ => -1 }

theorem tooth_wrong_sign_dual_rejected : checkFhqpb001BundleInt forgedWrongSignDualBundle = false := by decide

def suboptimalGapBundle : Fhqpb001BundleInt 1 0 0 :=
  { baseBundle1D with x_int := fun _ => 0, lamU_int := fun _ => 1, eps_int := 0 }

theorem tooth_gap_exceeded_rejected : checkFhqpb001BundleInt suboptimalGapBundle = false := by decide

/-! ## Part C. Multilateral Netting Compression (`∑ net_legs = ∑ gross_legs`, Zero Value Creation) -/

structure SettlementLeg where
  (payer payee asset amount : ℕ)
  deriving DecidableEq, Repr

def SettlementLeg.delta (leg : SettlementLeg) (party asset : ℕ) : ℤ :=
  if asset = leg.asset then
    (if party = leg.payee then (leg.amount : ℤ) else 0) - (if party = leg.payer then (leg.amount : ℤ) else 0)
  else 0

def netBalance (legs : List SettlementLeg) (party asset : ℕ) : ℤ :=
  (legs.map (fun l => l.delta party asset)).sum

def grossVolume (legs : List SettlementLeg) : ℕ := (legs.map (·.amount)).sum

def LegsWellFormed (legs : List SettlementLeg) : Prop := ∀ l ∈ legs, 0 < l.amount ∧ l.payer ≠ l.payee

@[simp] theorem netBalance_nil (party asset : ℕ) : netBalance [] party asset = 0 := rfl

@[simp] theorem netBalance_cons (l : SettlementLeg) (rest : List SettlementLeg) (party asset : ℕ) :
    netBalance (l :: rest) party asset = l.delta party asset + netBalance rest party asset := rfl

private theorem sum_indicator_nodup : ∀ (ps : List ℕ) (target : ℕ) (v : ℤ),
    ps.Nodup → target ∈ ps → (ps.map (fun p => if p = target then v else 0)).sum = v
  | [], _, _, _, hmem => by cases hmem
  | p :: rest, target, v, hnd, hmem => by
      rw [List.nodup_cons] at hnd; simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmem with htp | htail
      · subst target; simp only [↓reduceIte]
        have hzero : (rest.map (fun q => if q = p then v else 0)).sum = 0 := by
          have hnot : p ∉ rest := hnd.1; clear hnd hmem
          induction rest with
          | nil => rfl
          | cons q qs ih =>
              have hne : q ≠ p := fun hqp => hnot (hqp ▸ List.Mem.head qs)
              simp only [List.map_cons, List.sum_cons, hne, ↓reduceIte, zero_add]
              exact ih fun h => hnot (List.Mem.tail q h)
        rw [hzero, add_zero]
      · have hne : p ≠ target := fun hpt => hnd.1 (hpt ▸ htail)
        simp only [hne, ↓reduceIte, zero_add]
        exact sum_indicator_nodup rest target v hnd.2 htail

private theorem delta_sum_eq_zero (leg : SettlementLeg) (parties : List ℕ) (asset : ℕ)
    (hnd : parties.Nodup) (hpayer : leg.payer ∈ parties) (hpayee : leg.payee ∈ parties) :
    (parties.map (fun p => leg.delta p asset)).sum = 0 := by
  unfold SettlementLeg.delta
  by_cases ha : asset = leg.asset
  · subst ha; simp only [↓reduceIte]
    have hsplit : ∀ (ps : List ℕ),
        (ps.map (fun p => (if p = leg.payee then (leg.amount : ℤ) else 0) -
          (if p = leg.payer then (leg.amount : ℤ) else 0))).sum =
        (ps.map (fun p => if p = leg.payee then (leg.amount : ℤ) else 0)).sum -
          (ps.map (fun p => if p = leg.payer then (leg.amount : ℤ) else 0)).sum := by
      intro ps; induction ps with
      | nil => rfl
      | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [hsplit, sum_indicator_nodup parties leg.payee _ hnd hpayee,
        sum_indicator_nodup parties leg.payer _ hnd hpayer, sub_self]
  · simp only [ha, ↓reduceIte]; simp

private theorem list_sum_map_add_int {α : Type} (xs : List α) (f g : α → ℤ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- **Keystone C1 (`sum_netBalance_eq_zero` — Zero Value Creation)**. -/
theorem sum_netBalance_eq_zero (legs : List SettlementLeg) (parties : List ℕ) (asset : ℕ)
    (hnd : parties.Nodup) (hcov : ∀ l ∈ legs, l.payer ∈ parties ∧ l.payee ∈ parties) :
    (parties.map (fun p => netBalance legs p asset)).sum = 0 := by
  induction legs with
  | nil => simp
  | cons l rest ih =>
      have hstep : (parties.map (fun p => netBalance (l :: rest) p asset)).sum =
          (parties.map (fun p => l.delta p asset + netBalance rest p asset)).sum := rfl
      rw [hstep, list_sum_map_add_int]
      have hl := hcov l (List.Mem.head rest)
      rw [delta_sum_eq_zero l parties asset hnd hl.1 hl.2,
          ih (fun l' hl' => hcov l' (List.Mem.tail l hl')), add_zero]

def dedupNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x ∈ xs then dedupNat xs else x :: dedupNat xs

theorem mem_dedupNat {x : ℕ} : ∀ {xs : List ℕ}, x ∈ dedupNat xs ↔ x ∈ xs
  | [] => Iff.rfl
  | y :: ys => by
      unfold dedupNat
      by_cases hy : y ∈ ys
      · simp only [hy, ↓reduceIte, mem_dedupNat]
        exact ⟨List.Mem.tail y, fun h => (List.mem_cons.mp h).elim (fun hxy => hxy ▸ hy) id⟩
      · simp only [hy, ↓reduceIte, List.mem_cons, mem_dedupNat]

theorem nodup_dedupNat : ∀ (xs : List ℕ), (dedupNat xs).Nodup
  | [] => List.nodup_nil
  | y :: ys => by
      unfold dedupNat
      by_cases hy : y ∈ ys
      · simp only [hy, ↓reduceIte]; exact nodup_dedupNat ys
      · rw [ite_eq_right_iff.mpr (fun h => (hy h).elim), List.nodup_cons, mem_dedupNat]
        exact ⟨hy, nodup_dedupNat ys⟩

def touchedParties (gross net : List SettlementLeg) : List ℕ :=
  dedupNat ((gross ++ net).flatMap (fun l => [l.payer, l.payee]))

def touchedAssets (gross net : List SettlementLeg) : List ℕ := dedupNat ((gross ++ net).map (·.asset))

theorem netBalance_zero_of_party_untouched (legs : List SettlementLeg) (party asset : ℕ)
    (hnot : ∀ l ∈ legs, party ≠ l.payer ∧ party ≠ l.payee) : netBalance legs party asset = 0 := by
  induction legs with
  | nil => rfl
  | cons l rest ih =>
      rw [netBalance_cons]; have hl := hnot l (List.Mem.head rest)
      have hd : l.delta party asset = 0 := by unfold SettlementLeg.delta; simp [hl.1, hl.2]
      rw [hd, ih (fun l' hl' => hnot l' (List.Mem.tail l hl')), add_zero]

theorem netBalance_zero_of_asset_untouched (legs : List SettlementLeg) (party asset : ℕ)
    (hnot : ∀ l ∈ legs, asset ≠ l.asset) : netBalance legs party asset = 0 := by
  induction legs with
  | nil => rfl
  | cons l rest ih =>
      rw [netBalance_cons]; have hl := hnot l (List.Mem.head rest)
      have hd : l.delta party asset = 0 := by unfold SettlementLeg.delta; simp [hl]
      rw [hd, ih (fun l' hl' => hnot l' (List.Mem.tail l hl')), add_zero]

/-- Executable multilateral netting verifier (`O(|L_gross| + |L_net|)`). -/
def checkMultilateralNetting (grossLegs netLegs : List SettlementLeg) : Bool :=
  let ps := touchedParties grossLegs netLegs
  let as_ := touchedAssets grossLegs netLegs
  grossLegs.all (fun l => decide (0 < l.amount && l.payer ≠ l.payee)) &&
  netLegs.all (fun l => decide (0 < l.amount && l.payer ≠ l.payee)) &&
  decide (grossVolume netLegs ≤ grossVolume grossLegs) &&
  ps.all (fun p => as_.all (fun a => decide (netBalance netLegs p a = netBalance grossLegs p a)))

/-- **Keystone C2 (`checkMultilateralNetting_sound`)**. -/
theorem checkMultilateralNetting_sound {grossLegs netLegs : List SettlementLeg}
    (hchk : checkMultilateralNetting grossLegs netLegs = true) :
    (∀ party asset : ℕ, netBalance netLegs party asset = netBalance grossLegs party asset) ∧
    grossVolume netLegs ≤ grossVolume grossLegs ∧
    LegsWellFormed grossLegs ∧
    LegsWellFormed netLegs ∧
    (∀ asset : ℕ, ((touchedParties grossLegs netLegs).map (fun p => netBalance netLegs p asset)).sum = 0) := by
  unfold checkMultilateralNetting at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨hgwf, hnwf⟩, hvol⟩, hgrid⟩
  refine ⟨?_, hvol, fun l hl => hgwf l hl, fun l hl => hnwf l hl, ?_⟩
  · intro party asset
    by_cases hp : party ∈ touchedParties grossLegs netLegs
    · by_cases ha : asset ∈ touchedAssets grossLegs netLegs
      · exact hgrid party hp asset ha
      · have hnotA : ∀ l ∈ grossLegs ++ netLegs, asset ≠ l.asset := fun l hl heq =>
          ha (by unfold touchedAssets; rw [mem_dedupNat]; exact List.mem_map.mpr ⟨l, hl, heq.symm⟩)
        rw [netBalance_zero_of_asset_untouched netLegs party asset (fun l hl => hnotA l (List.mem_append_right _ hl)),
            netBalance_zero_of_asset_untouched grossLegs party asset (fun l hl => hnotA l (List.mem_append_left _ hl))]
    · have hnotP : ∀ l ∈ grossLegs ++ netLegs, party ≠ l.payer ∧ party ≠ l.payee := fun l hl =>
        ⟨fun heq => hp (by unfold touchedParties; rw [mem_dedupNat]; exact List.mem_flatMap.mpr ⟨l, hl, by subst heq; simp⟩),
         fun heq => hp (by unfold touchedParties; rw [mem_dedupNat]; exact List.mem_flatMap.mpr ⟨l, hl, by subst heq; simp⟩)⟩
      rw [netBalance_zero_of_party_untouched netLegs party asset (fun l hl => hnotP l (List.mem_append_right _ hl)),
          netBalance_zero_of_party_untouched grossLegs party asset (fun l hl => hnotP l (List.mem_append_left _ hl))]
  · intro asset
    apply sum_netBalance_eq_zero netLegs (touchedParties grossLegs netLegs) asset (nodup_dedupNat _)
    intro l hl; unfold touchedParties; rw [mem_dedupNat, mem_dedupNat]
    have hin : l ∈ grossLegs ++ netLegs := List.mem_append_right _ hl
    exact ⟨List.mem_flatMap.mpr ⟨l, hin, by simp⟩, List.mem_flatMap.mpr ⟨l, hin, by simp⟩⟩

/-- **Top-Level Keystone (`fhqpb001_clearing_and_netting_keystone`)**. -/
theorem fhqpb001_clearing_and_netting_keystone {n meq mineq : ℕ}
    {B : Fhqpb001BundleInt n meq mineq} {grossLegs netLegs : List SettlementLeg}
    (hqp : checkFhqpb001BundleInt B = true)
    (hnet : checkMultilateralNetting grossLegs netLegs = true) :
    PsdSymm B.decodeQp.Q ∧
    PrimalFeasible B.decodeQp B.decodePrimal ∧
    primalObj B.decodeQp B.decodePrimal - dualObj B.decodeQp B.decodePrimal B.decodeDual ≤ B.decodeEps ∧
    (∀ y : Fin n → ℚ, PrimalFeasible B.decodeQp y →
      primalObj B.decodeQp B.decodePrimal ≤ primalObj B.decodeQp y + B.decodeEps) ∧
    (∀ party asset : ℕ, netBalance netLegs party asset = netBalance grossLegs party asset) ∧
    grossVolume netLegs ≤ grossVolume grossLegs ∧
    (∀ asset : ℕ, ((touchedParties grossLegs netLegs).map (fun p => netBalance netLegs p asset)).sum = 0) := by
  obtain ⟨hpsd, hfeas, hgap, hopt⟩ := checkFhqpb001BundleInt_sound hqp
  obtain ⟨hbal, hvol, _, _, hzero⟩ := checkMultilateralNetting_sound hnet
  exact ⟨hpsd, hfeas, hgap, hopt, hbal, hvol, hzero⟩

def auctionQpWitness : Fhqpb001BundleInt 2 1 0 :=
  { scaleDenom := 1, edges := [⟨0, 1, 1, -1, 1⟩], diagSlack := ![1, 1],
    Q_int := ![![2, -1], ![-1, 2]], q_int := ![-12, 6],
    A_int := ![![1, -1]], b_int := ![0],
    G_int := fun k => k.elim0, h_int := fun k => k.elim0,
    l_int := ![0, 0], u_int := ![10, 8], x_int := ![3, 3],
    nu_int := ![9], mu_int := fun k => k.elim0,
    lamL_int := ![0, 0], lamU_int := ![0, 0], eps_int := 0 }

def witnessGrossLegs : List SettlementLeg := [⟨1, 2, 0, 110⟩, ⟨2, 3, 0, 80⟩, ⟨3, 1, 0, 60⟩, ⟨2, 4, 0, 30⟩]
def witnessNetLegs : List SettlementLeg := [⟨1, 3, 0, 20⟩, ⟨1, 4, 0, 30⟩]

/-- **Joint Premise Inhabitation (`clearing_and_netting_joint_witness`)**. -/
theorem clearing_and_netting_joint_witness :
    checkFhqpb001BundleInt auctionQpWitness = true ∧
    checkMultilateralNetting witnessGrossLegs witnessNetLegs = true ∧
    grossVolume witnessNetLegs < grossVolume witnessGrossLegs ∧
    (∀ y : Fin 2 → ℚ, PrimalFeasible auctionQpWitness.decodeQp y →
      primalObj auctionQpWitness.decodeQp auctionQpWitness.decodePrimal ≤
        primalObj auctionQpWitness.decodeQp y) := by
  have hqp : checkFhqpb001BundleInt auctionQpWitness = true := by decide
  have hnet : checkMultilateralNetting witnessGrossLegs witnessNetLegs = true := by decide
  have hvol : grossVolume witnessNetLegs < grossVolume witnessGrossLegs := by decide
  obtain ⟨_, _, _, hopt, _, _, _⟩ := fhqpb001_clearing_and_netting_keystone hqp hnet
  refine ⟨hqp, hnet, hvol, fun y hy => ?_⟩
  have h := hopt y hy
  have heps : auctionQpWitness.decodeEps = 0 := by simp [Fhqpb001BundleInt.decodeEps, auctionQpWitness]
  linarith

theorem tooth_value_creation_leg_refused :
    checkMultilateralNetting witnessGrossLegs [⟨1, 3, 0, 20⟩, ⟨1, 4, 0, 31⟩] = false := by decide

theorem tooth_exposure_inflation_refused :
    checkMultilateralNetting [⟨1, 2, 0, 100⟩] [⟨1, 9, 0, 80⟩, ⟨9, 2, 0, 80⟩, ⟨1, 2, 0, 20⟩] = false := by decide

/-! ## `#guard_msgs`-Pinned `#print axioms` Census -/

/-- info: 'Minidregg.Theory.ExactKktClearingCert.sddFactor_quadForm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sddFactor_quadForm_eq
/-- info: 'Minidregg.Theory.ExactKktClearingCert.sddFactor_implies_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sddFactor_implies_psd
/-- info: 'Minidregg.Theory.ExactKktClearingCert.scaled_dd_implies_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scaled_dd_implies_psd
/-- info: 'Minidregg.Theory.ExactKktClearingCert.checkSddRowDomInt_implies_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkSddRowDomInt_implies_psd
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_negative_edge_weight_not_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_negative_edge_weight_not_psd
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_indefinite2_refused_and_not_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_indefinite2_refused_and_not_psd
/-- info: 'Minidregg.Theory.ExactKktClearingCert.primal_sub_dual_eq_compGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primal_sub_dual_eq_compGap
/-- info: 'Minidregg.Theory.ExactKktClearingCert.lagrangian_weak_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lagrangian_weak_duality
/-- info: 'Minidregg.Theory.ExactKktClearingCert.kkt_bounded_gap_global_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kkt_bounded_gap_global_optimal
/-- info: 'Minidregg.Theory.ExactKktClearingCert.kkt_complementary_slackness_exact_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kkt_complementary_slackness_exact_optimal
/-- info: 'Minidregg.Theory.ExactKktClearingCert.checkFhqpb001BundleInt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkFhqpb001BundleInt_sound
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_matrix_pin_omitted_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_matrix_pin_omitted_unsound
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_wrong_sign_dual_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_wrong_sign_dual_rejected
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_gap_exceeded_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_gap_exceeded_rejected
/-- info: 'Minidregg.Theory.ExactKktClearingCert.sum_netBalance_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sum_netBalance_eq_zero
/-- info: 'Minidregg.Theory.ExactKktClearingCert.checkMultilateralNetting_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkMultilateralNetting_sound
/-- info: 'Minidregg.Theory.ExactKktClearingCert.fhqpb001_clearing_and_netting_keystone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fhqpb001_clearing_and_netting_keystone
/-- info: 'Minidregg.Theory.ExactKktClearingCert.clearing_and_netting_joint_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clearing_and_netting_joint_witness
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_value_creation_leg_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_value_creation_leg_refused
/-- info: 'Minidregg.Theory.ExactKktClearingCert.tooth_exposure_inflation_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_exposure_inflation_refused

end Minidregg.Theory.ExactKktClearingCert
