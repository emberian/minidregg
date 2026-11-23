/-
# `Theory/Tower256TraceBitPacking.lean` — Frigo–shelat (`eprint 2026/2770`) Trace-Duality
`256`-Bit Bijective Packing & Additive Hilbert-90 Single-Mask ZK over Fan–Paar `Tower256`
Formalizes Matteo Frigo & abhi shelat (*Sumcheck Bit Packing*, Nov 4, 2026, `eprint 2026/2770`)
over the Fan–Paar binary tower `T_0 = GF(2)`, `T_{k+1} = T_k[X_k] / (X_k^2 + g_k X_k + 1)`
(`g_0 = 1`, `g_{k+1} = X_k`, `T_8 = Tower256 = GF(2^256)`), reusing `Theory.Tower256EndianBridge`.
Import boundary: `Theory` tier (`Mathlib`, `Lean`, `Std`, `Theory` only).
-/
import Theory.Tower256EndianBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Minidregg.Theory.Tower256TraceBitPacking
open Minidregg.Theory hiding towerMul
open Minidregg.Theory.BinaryTowerFanPaarCodec
open Minidregg.Theory.Tower256EndianBridge
open scoped BigOperators
set_option autoImplicit false

/-! ## §1. Carrier Aliases, Index Helpers, Squaring Bijection, & `towerInvX` -/
abbrev TowerElem := ObendTowerElem
abbrev Tower256Elem := ObendTower256
abbrev towerMul := Minidregg.Theory.Tower256EndianBridge.towerMul
private theorem towerZero_eq_zero (k : Nat) : towerZero k = 0 := rfl
private theorem towerOne_eq_one (k : Nat) : towerOne k = 1 := rfl
private theorem obendFieldEquiv_tMul (k : Nat) (a b : TowerElem k) :
    obendFieldEquiv k (towerMul k a b) = obendFieldEquiv k a * obendFieldEquiv k b := obendFieldEquiv_mul k a b
private theorem lt_pow2_succ {k n : Nat} (h : n < 2 ^ k) : n < 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]; omega
private theorem add_pow2_lt {k n : Nat} (h : n < 2 ^ k) : 2 ^ k + n < 2 ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_two]; omega
private theorem sub_pow2_lt {k n : Nat} (h1 : n < 2 ^ (k + 1)) (h2 : ¬ n < 2 ^ k) : n - 2 ^ k < 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_two] at h1; omega
instance instFintypeTowerElem : (k : Nat) → Fintype (TowerElem k)
  | 0 => inferInstanceAs (Fintype Bool)
  | k + 1 => @instFintypeProd _ _ (instFintypeTowerElem k) (instFintypeTowerElem k)
theorem card_towerElem (k : Nat) : Fintype.card (TowerElem k) = 2 ^ (2 ^ k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    change Fintype.card (TowerElem k × TowerElem k) = 2 ^ (2 ^ (k + 1))
    rw [Fintype.card_prod, ih, ← pow_add, pow_succ, mul_two]
/-- Exact inverse `g_k⁻¹` directly from `X_k^2 + g_{k-1} X_k + 1 = 0 ⟹ X_k⁻¹ = g_{k-1} + X_k`. -/
def towerInvX : (k : Nat) → TowerElem k
  | 0 => true
  | k + 1 => (towerX k, towerOne k)
def sqExec (k : Nat) (a : TowerBitVec k) : TowerBitVec k := mulExec k a a
theorem towerAdd_self_zero (k : Nat) (a : TowerElem k) : towerAdd k a a = towerZero k := neg_add_cancel a
theorem towerElem_two_eq_zero (k : Nat) : (2 : TowerElem k) = 0 := by
  rw [← one_add_one_eq_two]; exact towerAdd_self_zero k (towerOne k)
@[simp] theorem towerX_mul_invX (k : Nat) : towerMul k (towerX k) (towerInvX k) = towerOne k := by
  cases k with
  | zero => rfl
  | succ k =>
    apply (obendFieldEquiv (k + 1)).injective
    have hy := fpGen_quadratic k; have h2 := binaryTower_two_eq_zero (k + 1)
    rw [obendFieldEquiv_tMul, obendFieldEquiv_towerX, towerMulCoeff_succ, towerInvX,
      obendFieldEquiv_mk, obendFieldEquiv_one, obendFieldEquiv_one, obendFieldEquiv_towerX, towerPack, map_one, one_mul]
    linear_combination hy - h2
theorem towerScaleX_eq_mul (k : Nat) (a : TowerElem k) : towerScaleX k a = towerMul k (towerX k) a := by
  apply (obendFieldEquiv k).injective; rw [obendFieldEquiv_scaleX, obendFieldEquiv_tMul, obendFieldEquiv_towerX]
theorem towerSq_add (k : Nat) (a b : TowerElem k) :
    towerSq k (towerAdd k a b) = towerAdd k (towerSq k a) (towerSq k b) := by
  apply (obendFieldEquiv k).injective
  rw [obendFieldEquiv_sq, obendFieldEquiv_add, obendFieldEquiv_add, obendFieldEquiv_sq, obendFieldEquiv_sq]
  linear_combination obendFieldEquiv k a * obendFieldEquiv k b * binaryTower_two_eq_zero k
/-- Characteristic-2 Freshman's Dream: `(a + b)^2 = a^2 + b^2`. -/
theorem frobenius_add (k : Nat) (a b : TowerElem k) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [sq, sq, sq]; exact towerSq_add k a b
theorem towerSq_injective (k : Nat) : Function.Injective (towerSq k) := by
  intro a b h; apply (obendFieldEquiv k).injective
  have hsq : (obendFieldEquiv k a) ^ 2 = (obendFieldEquiv k b) ^ 2 := by
    simpa [obendFieldEquiv_sq] using congrArg (obendFieldEquiv k) h
  have h' : (obendFieldEquiv k a + obendFieldEquiv k b) ^ 2 = 0 := by
    linear_combination hsq + (obendFieldEquiv k a * obendFieldEquiv k b +
      (obendFieldEquiv k b) ^ 2) * binaryTower_two_eq_zero k
  linear_combination sq_eq_zero_iff.mp h' - obendFieldEquiv k b * binaryTower_two_eq_zero k
theorem towerSq_bijective (k : Nat) : Function.Bijective (towerSq k) :=
  (Finite.injective_iff_bijective).mp (towerSq_injective k)

/-! ## §2. Relative & Absolute Field Trace, Parity Bitmask, & Fan–Paar Bit-255 Tooth -/
/-- Relative trace `Tr_{T_{k+1}/T_k}(a_0 + a_1 X_k) = g_k * a_1`. -/
def relTrace (k : Nat) (a : TowerElem (k + 1)) : TowerElem k := towerMul k (towerX k) a.2
/-- Absolute trace `Tr_k : TowerElem k → Bool`, iterating `relTrace` to `GF(2)`. -/
def towerTrace : (k : Nat) → TowerElem k → Bool
  | 0, a => a
  | k + 1, a => towerTrace k (relTrace k a)
@[simp] theorem towerTrace_zero (k : Nat) : towerTrace k (towerZero k) = false := by
  induction k with
  | zero => rfl
  | succ k ih => change towerTrace k (towerX k * 0) = false; rw [mul_zero]; exact ih
theorem towerTrace_add (k : Nat) (a b : TowerElem k) :
    towerTrace k (towerAdd k a b) = (towerTrace k a ^^ towerTrace k b) := by
  induction k with
  | zero => rfl
  | succ k ih => change towerTrace k (towerX k * (a.2 + b.2)) = _; rw [left_distrib]; exact ih _ _
@[simp] theorem towerTrace_X (k : Nat) : towerTrace k (towerX k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => change towerTrace k (towerX k * 1) = true; rw [mul_one]; exact ih
@[simp] theorem towerTrace_invX (k : Nat) : towerTrace k (towerInvX k) = true := by
  cases k with
  | zero => rfl
  | succ k => change towerTrace k (towerX k * 1) = true; rw [mul_one]; exact towerTrace_X k
theorem towerTrace_sq (k : Nat) (a : TowerElem k) : towerTrace k (towerSq k a) = towerTrace k a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih =>
    change towerTrace k (towerX k * ((a.1 * a.2 + a.2 * a.1) + towerX k * (a.2 * a.2))) = towerTrace k (towerX k * a.2)
    have hcancel : a.1 * a.2 + a.2 * a.1 = 0 := by rw [mul_comm a.2 a.1]; exact towerAdd_self_zero k _
    rw [hcancel, zero_add, show towerX k * (towerX k * (a.2 * a.2)) = towerSq k (towerX k * a.2) by
      change towerX k * (towerX k * (a.2 * a.2)) = (towerX k * a.2) * (towerX k * a.2); ring]; exact ih _
private theorem fpGen_frobenius_step (k : Nat) :
    fpGen k ^ (2 ^ 2 ^ k) = binaryTowerEmbed k (towerMulCoeff k) + fpGen k := by
  have h2 := binaryTower_two_eq_zero (k + 1); have hq := fpGen_quadratic k
  have hcq : binaryTowerEmbed k (towerMulCoeff k) ^ (2 ^ 2 ^ k) = binaryTowerEmbed k (towerMulCoeff k) := by
    rw [← map_pow, binaryTower_pow_card]
  have hpowq : (fpGen k ^ 2 + binaryTowerEmbed k (towerMulCoeff k) * fpGen k + 1) ^ (2 ^ 2 ^ k) = 0 := by
    rw [hq, zero_pow (Nat.two_pow_pos _).ne']
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, hcq, one_pow] at hpowq
  have hyy : (fpGen k ^ 2) ^ (2 ^ 2 ^ k) = (fpGen k ^ (2 ^ 2 ^ k)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hyy] at hpowq
  have hfac : (fpGen k ^ (2 ^ 2 ^ k) + fpGen k) *
      (fpGen k ^ (2 ^ 2 ^ k) + (binaryTowerEmbed k (towerMulCoeff k) + fpGen k)) = 0 := by
    linear_combination hpowq + hq + (fpGen k * fpGen k ^ (2 ^ 2 ^ k) - 1) * h2
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · exact absurd (binaryTower_mem_range_of_pow_card (by linear_combination hcase - fpGen k * h2))
      (fpGen_not_mem_range_all k)
  · linear_combination hcase - (binaryTowerEmbed k (towerMulCoeff k) + fpGen k) * h2
/-- **Relative Trace Identity:** `Tr_{T_{k+1}/T_k}(a_0 + a_1 X_k) = a_1 * g_k = u + u^(2^(2^k))`. -/
theorem relTrace_eq_frob_sum (k : Nat) (a : TowerElem (k + 1)) :
    binaryTowerEmbed k (obendFieldEquiv k (relTrace k a)) =
      obendFieldEquiv (k + 1) a + (obendFieldEquiv (k + 1) a) ^ (2 ^ 2 ^ k) := by
  have h2 := binaryTower_two_eq_zero (k + 1)
  have hf1 : binaryTowerEmbed k (obendFieldEquiv k a.1) ^ (2 ^ 2 ^ k) = binaryTowerEmbed k (obendFieldEquiv k a.1) := by
    rw [← map_pow, binaryTower_pow_card]
  have hf2 : binaryTowerEmbed k (obendFieldEquiv k a.2) ^ (2 ^ 2 ^ k) = binaryTowerEmbed k (obendFieldEquiv k a.2) := by
    rw [← map_pow, binaryTower_pow_card]
  simp only [relTrace, obendFieldEquiv_tMul, obendFieldEquiv_towerX, obendFieldEquiv_pair,
    towerPack, map_mul, add_pow_char_pow, mul_pow, hf1, hf2, fpGen_frobenius_step]
  linear_combination -(binaryTowerEmbed k (obendFieldEquiv k a.1) +
    binaryTowerEmbed k (obendFieldEquiv k a.2) * fpGen k) * h2
/-- **Absolute Trace Equivalence:** `towerTrace k a` equals the Galois Frobenius-orbit trace `bTrace k`. -/
theorem towerTrace_eq_bTrace (k : Nat) (a : TowerElem k) :
    (if towerTrace k a then (1 : binaryTower k) else 0) = bTrace k (obendFieldEquiv k a) := by
  induction k with
  | zero =>
    change Bool at a; have h0 : obendFieldEquiv 0 a = if a then 1 else 0 := coordinateFieldEquiv_bit a
    rw [h0]; cases a <;> simp [towerTrace, bTrace]
  | succ k ih =>
    rw [bTrace_succ_eq, ← relTrace_eq_frob_sum k a]; simp only [← map_pow, ← map_sum]
    have hb : (∑ i ∈ Finset.range (2 ^ k), (obendFieldEquiv k (relTrace k a)) ^ 2 ^ i) =
        bTrace k (obendFieldEquiv k (relTrace k a)) := rfl
    rw [hb, ← ih (relTrace k a)]
    change (if towerTrace k (relTrace k a) then (1 : binaryTower (k + 1)) else 0) = _
    cases towerTrace k (relTrace k a) <;> simp
def bitDotAux (w : Nat) (u v : BitVec w) : Nat → Bool
  | 0 => false
  | n + 1 => bitDotAux w u v n ^^ (u.getLsbD n && v.getLsbD n)
def bitDot (w : Nat) (u v : BitVec w) : Bool := bitDotAux w u v w
private theorem bitDotAux_comm (w : Nat) (u v : BitVec w) (n : Nat) : bitDotAux w u v n = bitDotAux w v u n := by
  induction n with | zero => rfl | succ n ih => simp [bitDotAux, ih, Bool.and_comm]
theorem bitDot_comm (w : Nat) (u v : BitVec w) : bitDot w u v = bitDot w v u := bitDotAux_comm w u v w
private theorem bitDotAux_xor_right (w : Nat) (u v₁ v₂ : BitVec w) (n : Nat) :
    bitDotAux w u (v₁ ^^^ v₂) n = (bitDotAux w u v₁ n ^^ bitDotAux w u v₂ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitDotAux, ih, BitVec.getLsbD_xor]
    cases u.getLsbD n <;> cases v₁.getLsbD n <;> cases v₂.getLsbD n <;>
      cases bitDotAux w u v₁ n <;> cases bitDotAux w u v₂ n <;> rfl
theorem bitDot_xor_right (w : Nat) (u v₁ v₂ : BitVec w) :
    bitDot w u (v₁ ^^^ v₂) = (bitDot w u v₁ ^^ bitDot w u v₂) := bitDotAux_xor_right w u v₁ v₂ w
theorem bitDot_xor_left (w : Nat) (u₁ u₂ v : BitVec w) :
    bitDot w (u₁ ^^^ u₂) v = (bitDot w u₁ v ^^ bitDot w u₂ v) := by
  rw [bitDot_comm, bitDot_xor_right, bitDot_comm w v u₁, bitDot_comm w v u₂]
private theorem bitDotAux_zero_left (w : Nat) (v : BitVec w) (n : Nat) : bitDotAux w (0#w) v n = false := by
  induction n with | zero => rfl | succ n ih => simp [bitDotAux, ih]
theorem bitDot_zero_left (w : Nat) (v : BitVec w) : bitDot w (0#w) v = false := bitDotAux_zero_left w v w
private theorem joinBits_getLsbD_low (k : Nat) (lo hi : TowerBitVec k) {n : Nat} (hn : n < 2 ^ k) :
    (joinBits k lo hi).getLsbD n = lo.getLsbD n := by
  simp only [joinBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hn, ↓reduceIte]
private theorem joinBits_getLsbD_high (k : Nat) (lo hi : TowerBitVec k) {n : Nat} :
    (joinBits k lo hi).getLsbD (2 ^ k + n) = hi.getLsbD n := by
  have hge : ¬ (2 ^ k + n < 2 ^ k) := by omega
  simp only [joinBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, hge, ↓reduceIte, Nat.add_sub_cancel_left]
private theorem bitDotAux_join_low (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    ∀ n ≤ 2 ^ k, bitDotAux (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) n = bitDotAux (2 ^ k) u₀ v₀ n
  | 0, _ => rfl
  | n + 1, hn => by
    have hlt : n < 2 ^ k := by omega
    simp only [bitDotAux, bitDotAux_join_low k u₀ u₁ v₀ v₁ n (by omega),
      joinBits_getLsbD_low k u₀ u₁ hlt, joinBits_getLsbD_low k v₀ v₁ hlt]
private theorem bitDotAux_join_high (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    ∀ n ≤ 2 ^ k, bitDotAux (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) (2 ^ k + n) =
      (bitDot (2 ^ k) u₀ v₀ ^^ bitDotAux (2 ^ k) u₁ v₁ n)
  | 0, _ => by simpa [bitDot, bitDotAux] using bitDotAux_join_low k u₀ u₁ v₀ v₁ (2 ^ k) le_rfl
  | n + 1, hn => by
    have ih := bitDotAux_join_high k u₀ u₁ v₀ v₁ n (by omega)
    rw [show 2 ^ k + (n + 1) = (2 ^ k + n) + 1 by omega]
    simp only [bitDotAux, ih, joinBits_getLsbD_high, Bool.xor_assoc]
theorem bitDot_join (k : Nat) (u₀ u₁ v₀ v₁ : TowerBitVec k) :
    bitDot (2 ^ (k + 1)) (joinBits k u₀ u₁) (joinBits k v₀ v₁) = (bitDot (2 ^ k) u₀ v₀ ^^ bitDot (2 ^ k) u₁ v₁) := by
  have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
  unfold bitDot; have haux := bitDotAux_join_high k u₀ u₁ v₀ v₁ (2 ^ k) le_rfl; rw [← h2] at haux; exact haux
/-- Self-adjointness of `scaleXExec` over `GF(2)`: `⟨u, X_k v⟩ = ⟨X_k u, v⟩`. -/
theorem bitDot_scaleXExec (k : Nat) (u v : TowerBitVec k) :
    bitDot (2 ^ k) u (scaleXExec k v) = bitDot (2 ^ k) (scaleXExec k u) v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    conv_lhs => rw [← joinBits_split k u, scaleXExec, bitDot_join, bitDot_xor_right, ih]
    conv_rhs => rw [← joinBits_split k v, scaleXExec, bitDot_join, bitDot_xor_left]
    cases bitDot (2 ^ k) (lowBits k u) (highBits k v) <;>
      cases bitDot (2 ^ k) (highBits k u) (lowBits k v) <;>
      cases bitDot (2 ^ k) (scaleXExec k (highBits k u)) (highBits k v) <;> rfl
def traceMask : (k : Nat) → TowerBitVec k
  | 0 => 1#1
  | k + 1 => joinBits k (0#(2 ^ k)) (scaleXExec k (traceMask k))
def traceExec (k : Nat) (x : TowerBitVec k) : Bool := bitDot (2 ^ k) (traceMask k) x
/-- **Exact Parity-Mask Trace Theorem (`2026/2770` §3):** `Tr_k(a) = parity(traceMask_k & pack(a))`. -/
theorem towerTrace_eq_mask_parity (k : Nat) (a : TowerElem k) :
    towerTrace k a = bitDot (2 ^ k) (traceMask k) (packTower k a) := by
  induction k with
  | zero => cases a <;> decide
  | succ k ih =>
    change towerTrace k (towerMul k (towerX k) a.2) = _
    rw [← towerScaleX_eq_mul, ih, ← scaleXExec_refines, traceMask, packTower, bitDot_join,
      bitDot_zero_left, Bool.false_xor, bitDot_scaleXExec]
theorem traceExec_refines (k : Nat) (a : TowerElem k) : traceExec k (packTower k a) = towerTrace k a :=
  (towerTrace_eq_mask_parity k a).symm
/-- **`#tooth` Refutation of Naive Bit-255 Trace in Fan–Paar Basis:** in `T_8`, `traceMask 8` has
weight 68 in `[128..255]` and bit 255 (`X_0 ... X_7`) has trace **`0`**, while `towerX 8` (`bit 128`) has trace **`1`**. -/
theorem tooth_fanpaar_top_monomial_trace_zero :
    traceMask 8 = 0x26c6636dc63a6da5c63a6da56da5a55700000000000000000000000000000000#256 ∧
    traceExec 8 (1#256 <<< 255) = false ∧ traceExec 8 (1#256 <<< 128) = true := by decide +kernel

/-! ## §3. Canonical Basis `β`, Unique Recursive Dual Basis `α`, & Bijective Packing (§2–§3) -/
def basisElem : (k : Nat) → Fin (2 ^ k) → TowerElem k
  | 0, _ => true
  | k + 1, i =>
    if h : i.val < 2 ^ k then (basisElem k ⟨i.val, h⟩, towerZero k)
    else (towerZero k, basisElem k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩)
def dualBasis : (k : Nat) → Fin (2 ^ k) → TowerElem k
  | 0, _ => true
  | k + 1, i =>
    if h : i.val < 2 ^ k then
      let a := dualBasis k ⟨i.val, h⟩; (a, towerMul k (towerInvX k) a)
    else
      let a := dualBasis k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩; (towerMul k (towerInvX k) a, towerZero k)
def invXExec : (k : Nat) → TowerBitVec k
  | 0 => 1#1
  | k + 1 => joinBits k (packTower k (towerX k)) (packTower k (towerOne k))
theorem invXExec_refines (k : Nat) : invXExec k = packTower k (towerInvX k) := by cases k <;> rfl
def dualBasisExec : (k : Nat) → Array (TowerBitVec k)
  | 0 => #[1#1]
  | k + 1 =>
    let prev := dualBasisExec k; let ix := invXExec k
    prev.map (fun a => joinBits k a (mulExec k ix a)) ++
      prev.map (fun a => joinBits k (mulExec k ix a) (0#(2 ^ k)))
theorem dualBasisExec_size (k : Nat) : (dualBasisExec k).size = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dualBasisExec, Array.size_append, Array.size_map, ih, Nat.pow_succ, Nat.mul_two]
private theorem packTower_zero (k : Nat) : packTower k (towerZero k) = 0#(2 ^ k) := by
  induction k with | zero => rfl | succ m ih => simp [towerZero, packTower, ih, joinBits]
theorem dualBasisExec_refines (k : Nat) (i : Fin (2 ^ k)) :
    (dualBasisExec k)[i.val]'(by rw [dualBasisExec_size]; exact i.isLt) = packTower k (dualBasis k i) := by
  induction k with
  | zero => simp [dualBasisExec, dualBasis, packTower]
  | succ k ih =>
    simp only [dualBasisExec, dualBasis]
    have hsz : ((dualBasisExec k).map fun a => joinBits k a (mulExec k (invXExec k) a)).size = 2 ^ k := by
      simp [dualBasisExec_size]
    by_cases h : i.val < 2 ^ k
    · rw [Array.getElem_append_left (by omega), Array.getElem_map]; simp only [h, ↓reduceDIte]; rw [
        ih ⟨i.val, h⟩, invXExec_refines, mulExec_refines]; rfl
    · rw [Array.getElem_append_right (by omega), Array.getElem_map]; simp only [h, ↓reduceDIte, hsz]; rw [ih ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt h⟩, invXExec_refines, mulExec_refines, ← packTower_zero k]; rfl
/-- **Dual-Basis Biorthogonality (`2026/2770` Lemma 3.1(3)):** `Tr_k(α_i · β_j) = (i == j)`. -/
theorem dual_basis_biorthogonal (k : Nat) (i j : Fin (2 ^ k)) :
    towerTrace k (towerMul k (dualBasis k i) (basisElem k j)) = (i == j) := by
  induction k with
  | zero =>
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega); have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst hi; subst hj; rfl
  | succ k ih =>
    simp only [dualBasis, basisElem]; have hxi : towerX k * towerInvX k = 1 := towerX_mul_invX k
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
    · simp only [hi, hj, ↓reduceDIte]; set a := dualBasis k ⟨i.val, hi⟩; set b := basisElem k ⟨j.val, hj⟩
      have heq : towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k a (towerZero k)) (towerMul k (towerMul k (towerInvX k) a) b)) (towerMul k (towerX k) (towerMul k (towerMul k (towerInvX k) a) (towerZero k)))) = towerMul k a b := by
        change towerX k * ((a * 0 + (towerInvX k * a) * b) + towerX k * ((towerInvX k * a) * 0)) = a * b
        rw [mul_zero, zero_add, mul_zero, mul_zero, add_zero, ← mul_assoc, ← mul_assoc, hxi, one_mul]
      change towerTrace k (towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k a (towerZero k)) (towerMul k (towerMul k (towerInvX k) a) b)) (towerMul k (towerX k) (towerMul k (towerMul k (towerInvX k) a) (towerZero k))))) = _
      rw [heq, ih ⟨i.val, hi⟩ ⟨j.val, hj⟩]; simp [BEq.beq, Fin.ext_iff]
    · simp only [hi, hj, ↓reduceDIte]; set a := dualBasis k ⟨i.val, hi⟩; set b := basisElem k ⟨j.val - 2 ^ k, sub_pow2_lt j.isLt hj⟩
      have hhi : towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k a b) (towerMul k (towerMul k (towerInvX k) a) (towerZero k))) (towerMul k (towerX k) (towerMul k (towerMul k (towerInvX k) a) b))) = towerZero k := by
        change towerX k * ((a * b + (towerInvX k * a) * 0) + towerX k * ((towerInvX k * a) * b)) = 0
        rw [mul_zero, add_zero, ← mul_assoc, ← mul_assoc, hxi, one_mul, show a * b + a * b = 0 from towerAdd_self_zero k _, mul_zero]
      change towerTrace k (towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k a b) (towerMul k (towerMul k (towerInvX k) a) (towerZero k))) (towerMul k (towerX k) (towerMul k (towerMul k (towerInvX k) a) b)))) = _
      rw [hhi, towerTrace_zero]; have hne : i ≠ j := fun h => hj (h ▸ hi); simp [BEq.beq, hne]
    · simp only [hi, hj, ↓reduceDIte]; set a := dualBasis k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt hi⟩; set b := basisElem k ⟨j.val, hj⟩
      have hhi : towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k (towerMul k (towerInvX k) a) (towerZero k)) (towerMul k (towerZero k) b)) (towerMul k (towerX k) (towerMul k (towerZero k) (towerZero k)))) = towerZero k := by
        change towerX k * (((towerInvX k * a) * 0 + 0 * b) + towerX k * (0 * 0)) = 0; ring
      change towerTrace k (towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k (towerMul k (towerInvX k) a) (towerZero k)) (towerMul k (towerZero k) b)) (towerMul k (towerX k) (towerMul k (towerZero k) (towerZero k))))) = _
      rw [hhi, towerTrace_zero]; have hne : i ≠ j := fun h => hi (h ▸ hj); simp [BEq.beq, hne]
    · simp only [hi, hj, ↓reduceDIte]; set a := dualBasis k ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt hi⟩; set b := basisElem k ⟨j.val - 2 ^ k, sub_pow2_lt j.isLt hj⟩
      have hhi : towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k (towerMul k (towerInvX k) a) b) (towerMul k (towerZero k) (towerZero k))) (towerMul k (towerX k) (towerMul k (towerZero k) b))) = towerMul k a b := by
        change towerX k * (((towerInvX k * a) * b + 0 * 0) + towerX k * (0 * b)) = a * b
        rw [zero_mul, add_zero, zero_mul, mul_zero, add_zero, ← mul_assoc, ← mul_assoc, hxi, one_mul]
      change towerTrace k (towerMul k (towerX k) (towerAdd k (towerAdd k (towerMul k (towerMul k (towerInvX k) a) b) (towerMul k (towerZero k) (towerZero k))) (towerMul k (towerX k) (towerMul k (towerZero k) b)))) = _
      rw [hhi, ih ⟨i.val - 2 ^ k, sub_pow2_lt i.isLt hi⟩ ⟨j.val - 2 ^ k, sub_pow2_lt j.isLt hj⟩]
      have hiff : (i.val - 2 ^ k = j.val - 2 ^ k) ↔ (i.val = j.val) := by omega
      simp only [BEq.beq, Fin.ext_iff, decide_eq_decide]; exact hiff
def packBits : (k : Nat) → (Fin (2 ^ k) → Bool) → TowerElem k
  | 0, bits => bits ⟨0, by decide⟩
  | k + 1, bits => (packBits k (fun j => bits ⟨j.val, lt_pow2_succ j.isLt⟩),
                    packBits k (fun j => bits ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩))
def pluckBit (k : Nat) (i : Fin (2 ^ k)) (X : TowerElem k) : Bool := towerTrace k (towerMul k (dualBasis k i) X)
theorem packBits_eq_sum (k : Nat) (bits : Fin (2 ^ k) → Bool) :
    packBits k bits = ∑ j : Fin (2 ^ k), if bits j then basisElem k j else 0 := by
  induction k with
  | zero =>
    change bits 0 = ∑ j : Fin 1, if bits j then basisElem 0 j else 0
    rw [Fin.sum_univ_one]; cases bits 0 <;> rfl
  | succ k ih =>
    let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [Nat.pow_succ, Nat.mul_two]))
    rw [← Fintype.sum_equiv e (fun x => if bits (e x) then basisElem (k + 1) (e x) else 0)
      (fun j => if bits j then basisElem (k + 1) j else 0) (fun _ => rfl), Fintype.sum_sum_type]
    have hpairL : ∀ (s : Finset (Fin (2 ^ k))) (g : Fin (2 ^ k) → TowerElem k),
        (∑ j ∈ s, ((g j, towerZero k) : TowerElem (k + 1))) = (∑ j ∈ s, g j, towerZero k) := fun s g =>
      Finset.induction_on s rfl fun a s ha ihs => by rw [Finset.sum_insert ha, Finset.sum_insert ha, ihs]; exact Prod.ext rfl (towerAdd_self_zero k _)
    have hpairR : ∀ (s : Finset (Fin (2 ^ k))) (g : Fin (2 ^ k) → TowerElem k),
        (∑ j ∈ s, ((towerZero k, g j) : TowerElem (k + 1))) = (towerZero k, ∑ j ∈ s, g j) := fun s g =>
      Finset.induction_on s rfl fun a s ha ihs => by rw [Finset.sum_insert ha, Finset.sum_insert ha, ihs]; exact Prod.ext (towerAdd_self_zero k _) rfl
    have hlo : (∑ j : Fin (2 ^ k), if bits (e (Sum.inl j)) then basisElem (k + 1) (e (Sum.inl j)) else 0) =
        (packBits k (fun j => bits ⟨j.val, lt_pow2_succ j.isLt⟩), towerZero k) := by
      rw [ih, ← hpairL Finset.univ]; refine Finset.sum_congr rfl fun j _ => ?_
      have he : e (Sum.inl j) = ⟨j.val, lt_pow2_succ j.isLt⟩ := rfl
      rw [he]; cases hb : bits ⟨j.val, lt_pow2_succ j.isLt⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [↓reduceIte, basisElem, j.isLt, ↓reduceDIte]; rfl
    have hhi : (∑ j : Fin (2 ^ k), if bits (e (Sum.inr j)) then basisElem (k + 1) (e (Sum.inr j)) else 0) =
        (towerZero k, packBits k (fun j => bits ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩)) := by
      rw [ih, ← hpairR Finset.univ]; refine Finset.sum_congr rfl fun j _ => ?_
      have he : e (Sum.inr j) = ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩ := rfl
      have hge : ¬ (2 ^ k + j.val < 2 ^ k) := by omega
      rw [he]; cases hb : bits ⟨2 ^ k + j.val, add_pow2_lt j.isLt⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [↓reduceIte, basisElem, hge, ↓reduceDIte, Nat.add_sub_cancel_left]; rfl
    rw [hlo, hhi]; exact Prod.ext (add_zero _).symm (zero_add _).symm
private local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
private local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
def xorSum {α : Type} [DecidableEq α] (s : Finset α) (f : α → Bool) : Bool := s.fold Bool.xor false f
theorem xorSum_empty {α : Type} [DecidableEq α] (f : α → Bool) : xorSum ∅ f = false := rfl
theorem xorSum_insert {α : Type} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) (f : α → Bool) :
    xorSum (insert a s) f = (f a ^^ xorSum s f) := Finset.fold_insert ha
theorem towerTrace_sum {α : Type} [DecidableEq α] (k : Nat) (s : Finset α) (f : α → TowerElem k) :
    towerTrace k (∑ x ∈ s, f x) = xorSum s (fun x => towerTrace k (f x)) := by
  refine Finset.induction_on s (by simp only [Finset.sum_empty, xorSum_empty]; exact towerTrace_zero k) fun a s ha ih => ?_
  rw [Finset.sum_insert ha, xorSum_insert ha, ← ih]; exact towerTrace_add k (f a) (∑ x ∈ s, f x)
/-- **Left Inverse (`2026/2770` Lemma 3.2):** `pluckBit k i (packBits k bits) = bits i`. -/
theorem pluckBit_packBits_id (k : Nat) (bits : Fin (2 ^ k) → Bool) (i : Fin (2 ^ k)) :
    pluckBit k i (packBits k bits) = bits i := by
  unfold pluckBit
  rw [packBits_eq_sum, show towerMul k (dualBasis k i) (∑ j, if bits j then basisElem k j else 0) =
    ∑ j, towerMul k (dualBasis k i) (if bits j then basisElem k j else 0) from Finset.mul_sum .., towerTrace_sum]
  have hsingle : ∀ (s : Finset (Fin (2 ^ k))), i ∈ s →
      xorSum s (fun j => towerTrace k (towerMul k (dualBasis k i) (if bits j then basisElem k j else 0))) = bits i := by
    intro s; refine Finset.induction_on s (fun h => by cases h) fun a s ha ih hmem => ?_
    rw [xorSum_insert ha]; by_cases hai : a = i
    · subst hai
      have hz : ∀ (t : Finset (Fin (2 ^ k))), a ∉ t →
          xorSum t (fun j => towerTrace k (towerMul k (dualBasis k a) (if bits j then basisElem k j else 0))) = false := by
        intro t; refine Finset.induction_on t (fun _ => rfl) fun b t hb iht hnt => ?_
        rw [xorSum_insert hb, iht (fun h => hnt (Finset.mem_insert_of_mem h)), Bool.xor_false]
        have hne : a ≠ b := fun h => hnt (h ▸ Finset.mem_insert_self b t)
        cases bits b
        · simp [show towerMul k (dualBasis k a) 0 = towerZero k from mul_zero _]
        · simp [dual_basis_biorthogonal, BEq.beq, hne]
      rw [hz s ha, Bool.xor_false]
      cases bits a
      · simp [show towerMul k (dualBasis k a) 0 = towerZero k from mul_zero _]
      · simp [dual_basis_biorthogonal]
    · rw [ih ((Finset.mem_insert.mp hmem).resolve_left (Ne.symm hai))]
      have ht : towerTrace k (towerMul k (dualBasis k i) (if bits a then basisElem k a else 0)) = false := by
        cases bits a
        · simp [show towerMul k (dualBasis k i) 0 = towerZero k from mul_zero _]
        · simp [dual_basis_biorthogonal, BEq.beq, Ne.symm hai]
      rw [ht, Bool.false_xor]
  exact hsingle Finset.univ (Finset.mem_univ i)
theorem packBits_injective (k : Nat) : Function.Injective (packBits k) := fun b₁ b₂ h => by
  funext i; rw [← pluckBit_packBits_id k b₁ i, ← pluckBit_packBits_id k b₂ i, h]
/-- **Bijective Packing (`2026/2770` Remark 2.1):** `packBits k` is a bijection (`0` bit constraints!). -/
theorem packBits_bijective (k : Nat) : Function.Bijective (packBits k) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨packBits_injective k, by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, card_towerElem]⟩
theorem packBits_pluckBit_id (k : Nat) (X : TowerElem k) : packBits k (fun i => pluckBit k i X) = X := by
  obtain ⟨bits, rfl⟩ := (packBits_bijective k).surjective X
  congr 1; funext i; exact pluckBit_packBits_id k bits i
/-- **Uniqueness of the Dual Basis (`2026/2770` Lemma 3.1(3)).** -/
theorem dual_basis_unique (k : Nat) (i : Fin (2 ^ k)) (α' : TowerElem k)
    (hb : ∀ j : Fin (2 ^ k), towerTrace k (towerMul k α' (basisElem k j)) = (i == j)) :
    α' = dualBasis k i := by
  by_contra hne; let d : TowerElem k := towerAdd k α' (dualBasis k i)
  have hd_ne : d ≠ towerZero k := fun h0 => hne <| by
    have h1 := congrArg (towerAdd k (dualBasis k i)) h0
    change dualBasis k i + (α' + dualBasis k i) = dualBasis k i + 0 at h1
    rw [add_left_comm, show dualBasis k i + dualBasis k i = 0 from towerAdd_self_zero k _, add_zero, add_zero] at h1; exact h1
  have htr_all : ∀ y : TowerElem k, towerTrace k (towerMul k d y) = false := by
    intro y; rw [← packBits_pluckBit_id k y, packBits_eq_sum]
    rw [show towerMul k d (∑ j, if pluckBit k j y then basisElem k j else 0) =
      ∑ j, towerMul k d (if pluckBit k j y then basisElem k j else 0) from Finset.mul_sum .., towerTrace_sum]
    have hz : ∀ (s : Finset (Fin (2 ^ k))),
        xorSum s (fun j => towerTrace k (towerMul k d (if pluckBit k j y then basisElem k j else 0))) = false := by
      intro s; refine Finset.induction_on s rfl fun a s ha ih => ?_
      rw [xorSum_insert ha, ih, Bool.xor_false]
      cases pluckBit k a y
      · simp [show towerMul k d 0 = towerZero k from mul_zero _]
      · simp only [↓reduceIte]; rw [show towerMul k d (basisElem k a) =
          towerAdd k (towerMul k α' (basisElem k a)) (towerMul k (dualBasis k i) (basisElem k a)) from right_distrib ..,
          towerTrace_add, hb a, dual_basis_biorthogonal, Bool.xor_self]
    exact hz Finset.univ
  have hfe_ne : obendFieldEquiv k d ≠ 0 := fun h => hd_ne ((obendFieldEquiv k).injective (by simp [h]))
  let y : TowerElem k := (obendFieldEquiv k).symm ((obendFieldEquiv k d)⁻¹ * obendFieldEquiv k (towerX k))
  have hdy : towerMul k d y = towerX k := (obendFieldEquiv k).injective <| by
    rw [obendFieldEquiv_mul, Equiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ hfe_ne, one_mul]
  have hc := htr_all y; rw [hdy, towerTrace_X] at hc; cases hc
/-- **Lemma 3.3 (`2026/2770`):** single bit-level inner product ↔ single packed trace-zero check. -/
theorem bit_inner_product_iff_trace_zero (k M : Nat)
    (X : Fin M → TowerElem k) (a : Fin M → Fin (2 ^ k) → Bool) (c : Bool) :
    xorSum Finset.univ (fun i : Fin M => xorSum Finset.univ (fun j : Fin (2 ^ k) => a i j && pluckBit k j (X i))) = c ↔
      towerTrace k (towerAdd k (∑ i : Fin M, towerMul k (∑ j : Fin (2 ^ k), if a i j then dualBasis k j else 0) (X i))
        (if c then towerX k else towerZero k)) = false := by
  rw [towerTrace_add, towerTrace_sum]
  have hterm : ∀ i : Fin M, towerTrace k (towerMul k (∑ j : Fin (2 ^ k), if a i j then dualBasis k j else 0) (X i)) =
      xorSum Finset.univ (fun j : Fin (2 ^ k) => a i j && pluckBit k j (X i)) := fun i => by
    rw [show towerMul k (∑ j, if a i j then dualBasis k j else 0) (X i) =
      ∑ j, towerMul k (if a i j then dualBasis k j else 0) (X i) from Finset.sum_mul .., towerTrace_sum]
    have hcongr : ∀ (s : Finset (Fin (2 ^ k))),
        xorSum s (fun j => towerTrace k (towerMul k (if a i j then dualBasis k j else 0) (X i))) =
        xorSum s (fun j => a i j && pluckBit k j (X i)) := fun s =>
      Finset.induction_on s rfl fun b s hb ih => by
        rw [xorSum_insert hb, xorSum_insert hb, ih]
        cases a i b
        · simp [show towerMul k 0 (X i) = towerZero k from zero_mul _]
        · rfl
    exact hcongr Finset.univ
  have houter : ∀ (s : Finset (Fin M)),
      xorSum s (fun i => towerTrace k (towerMul k (∑ j : Fin (2 ^ k), if a i j then dualBasis k j else 0) (X i))) =
      xorSum s (fun i => xorSum Finset.univ (fun j : Fin (2 ^ k) => a i j && pluckBit k j (X i))) := fun s =>
    Finset.induction_on s rfl fun b s hb ih => by rw [xorSum_insert hb, xorSum_insert hb, ih, hterm b]
  rw [houter Finset.univ, show towerTrace k (if c then towerX k else towerZero k) = c by cases c <;> simp]
  cases xorSum Finset.univ (fun i : Fin M => xorSum Finset.univ (fun j : Fin (2 ^ k) => a i j && pluckBit k j (X i))) <;>
    cases c <;> decide
/-- **§3 Eq. (6) Tensor Factorization:** when `R_{i,j} = C_i D_j`, `Q_{i,m} = ∑_ℓ d_ℓ(C_i) μ_{m,ℓ}` (`O(Mm/8)` XORs). -/
theorem tensor_coeff_factorization (k : Nat) (C : TowerElem k) (D : Fin (2 ^ k) → TowerElem k) (m : Fin (2 ^ k)) :
    (∑ j : Fin (2 ^ k), if pluckBit k m (towerMul k C (D j)) then dualBasis k j else 0) =
    ∑ ℓ : Fin (2 ^ k), if pluckBit k ℓ C then
      (∑ j : Fin (2 ^ k), if pluckBit k m (towerMul k (basisElem k ℓ) (D j)) then dualBasis k j else 0) else 0 := by
  have hif : ∀ (s : Finset (Fin (2 ^ k))) (b : Fin (2 ^ k) → Bool) (v : TowerElem k),
      (if xorSum s b then v else 0) = ∑ ℓ ∈ s, if b ℓ then v else 0 := fun s b v =>
    Finset.induction_on s (by simp [xorSum_empty]) fun a s ha ih => by
      rw [xorSum_insert ha, Finset.sum_insert ha, ← ih]
      cases b a <;> cases xorSum s b <;> simp [show v + v = 0 from towerAdd_self_zero k v]
  have hpluck : ∀ j : Fin (2 ^ k), pluckBit k m (towerMul k C (D j)) =
      xorSum Finset.univ (fun ℓ : Fin (2 ^ k) => pluckBit k ℓ C && pluckBit k m (towerMul k (basisElem k ℓ) (D j))) := by
    intro j; conv_lhs => unfold pluckBit; rw [← packBits_pluckBit_id k C, packBits_eq_sum]
    rw [show towerMul k (∑ ℓ, if pluckBit k ℓ C then basisElem k ℓ else 0) (D j) =
      ∑ ℓ, towerMul k (if pluckBit k ℓ C then basisElem k ℓ else 0) (D j) from Finset.sum_mul ..,
      show towerMul k (dualBasis k m) (∑ ℓ, towerMul k (if pluckBit k ℓ C then basisElem k ℓ else 0) (D j)) =
      ∑ ℓ, towerMul k (dualBasis k m) (towerMul k (if pluckBit k ℓ C then basisElem k ℓ else 0) (D j)) from Finset.mul_sum ..,
      towerTrace_sum]
    have hc : ∀ (s : Finset (Fin (2 ^ k))),
        xorSum s (fun ℓ => towerTrace k (towerMul k (dualBasis k m) (towerMul k (if pluckBit k ℓ C then basisElem k ℓ else 0) (D j)))) =
        xorSum s (fun ℓ => pluckBit k ℓ C && pluckBit k m (towerMul k (basisElem k ℓ) (D j))) := fun s =>
      Finset.induction_on s rfl fun a s ha ih => by
        rw [xorSum_insert ha, xorSum_insert ha, ih]
        cases pluckBit k a C
        · simp [show towerMul k 0 (D j) = towerZero k from zero_mul _, show towerMul k (dualBasis k m) (towerZero k) = towerZero k from mul_zero _]
        · rfl
    exact hc Finset.univ
  calc (∑ j : Fin (2 ^ k), if pluckBit k m (towerMul k C (D j)) then dualBasis k j else 0)
      = ∑ j : Fin (2 ^ k), ∑ ℓ : Fin (2 ^ k),
          if (pluckBit k ℓ C && pluckBit k m (towerMul k (basisElem k ℓ) (D j))) then dualBasis k j else 0 :=
        Finset.sum_congr rfl fun j _ => by rw [hpluck j, hif]
    _ = ∑ ℓ : Fin (2 ^ k), ∑ j : Fin (2 ^ k),
          if (pluckBit k ℓ C && pluckBit k m (towerMul k (basisElem k ℓ) (D j))) then dualBasis k j else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ℓ _ => by cases pluckBit k ℓ C <;> simp

/-! ## §4. Constructive Additive Hilbert Theorem 90 (`solveArtinSchreier`) & Trace-1 Tooth -/
def artinSchreier (k : Nat) (t : TowerElem k) : TowerElem k := towerAdd k (towerSq k t) t
theorem artinSchreier_add (k : Nat) (u v : TowerElem k) :
    artinSchreier k (towerAdd k u v) = towerAdd k (artinSchreier k u) (artinSchreier k v) := by
  unfold artinSchreier; rw [towerSq_add]
  change (towerSq k u + towerSq k v) + (u + v) = (towerSq k u + u) + (towerSq k v + v); ring
theorem towerTrace_artinSchreier (k : Nat) (t : TowerElem k) : towerTrace k (artinSchreier k t) = false := by
  unfold artinSchreier; rw [towerTrace_add, towerTrace_sq, Bool.xor_self]
theorem artinSchreier_eq_zero_iff (k : Nat) (t : TowerElem k) :
    artinSchreier k t = towerZero k ↔ t = towerZero k ∨ t = towerOne k := by
  constructor
  · intro h
    have hf : obendFieldEquiv k t * (obendFieldEquiv k t + 1) = 0 := by
      have h' := congrArg (obendFieldEquiv k) h
      simp only [artinSchreier, obendFieldEquiv_add, obendFieldEquiv_sq, obendFieldEquiv_zero] at h'; linear_combination h'
    rcases mul_eq_zero.mp hf with hz | h1
    · left; exact (obendFieldEquiv k).injective (by simp [hz])
    · right; exact (obendFieldEquiv k).injective (by rw [obendFieldEquiv_one]; linear_combination h1 - binaryTower_two_eq_zero k)
  · rintro (rfl | rfl)
    · apply (obendFieldEquiv k).injective; simp [artinSchreier, obendFieldEquiv_add, obendFieldEquiv_sq]
    · apply (obendFieldEquiv k).injective; simp [artinSchreier, obendFieldEquiv_add, obendFieldEquiv_sq, one_add_one_eq_two, binaryTower_two_eq_zero]
private def towerMk {k : Nat} (lo hi : TowerElem k) : TowerElem (k + 1) := (lo, hi)
private def towerLo {k : Nat} (z : TowerElem (k + 1)) : TowerElem k := z.1
private def towerHi {k : Nat} (z : TowerElem (k + 1)) : TowerElem k := z.2
private theorem towerTrace_succ_snd (k : Nat) (z : TowerElem (k + 1))
    (hz : towerTrace (k + 1) z = false) : towerTrace k (towerMul k (towerX k) (towerHi z)) = false := hz
private theorem solveAS_flip_trace (k : Nat) (z0 t1₀ : TowerElem k)
    (htr : ¬ towerTrace k (towerAdd k z0 (towerSq k t1₀)) = false) :
    towerTrace k (towerAdd k z0 (towerSq k (towerAdd k t1₀ (towerInvX k)))) = false := by
  have htr0 : towerTrace k (towerAdd k z0 (towerSq k t1₀)) = true := Bool.eq_true_of_not_eq_false htr
  have heq : towerAdd k z0 (towerSq k (towerAdd k t1₀ (towerInvX k))) =
      towerAdd k (towerAdd k z0 (towerSq k t1₀)) (towerSq k (towerInvX k)) := by
    rw [towerSq_add]; change z0 + (towerSq k t1₀ + towerSq k (towerInvX k)) = (z0 + towerSq k t1₀) + towerSq k (towerInvX k); ring
  rw [heq, towerTrace_add, htr0, towerTrace_sq, towerTrace_invX]; rfl
/-- Constructive Artin–Schreier solver (`0 Classical.choice`) by Fan–Paar tower induction. -/
def solveArtinSchreier : (k : Nat) → (z : TowerElem k) → towerTrace k z = false → TowerElem k
  | 0, _, _ => false
  | k + 1, z, hz =>
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u
    if htr : towerTrace k (towerAdd k (towerLo z) (towerSq k t1₀)) = false then
      towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k t1₀)) htr) t1₀
    else
      towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k))))
        (solveAS_flip_trace k (towerLo z) t1₀ htr)) (towerAdd k t1₀ (towerInvX k))
theorem solveArtinSchreier_spec :
    ∀ (k : Nat) (z : TowerElem k) (hz : towerTrace k z = false), artinSchreier k (solveArtinSchreier k z hz) = z
  | 0, false, _ => rfl
  | 0, true, hz => by cases hz
  | k + 1, z, hz => by
    have step : ∀ (t0 t1 : TowerElem k), artinSchreier k t0 = towerAdd k (towerLo z) (towerSq k t1) →
        artinSchreier k (towerMul k (towerX k) t1) = towerMul k (towerX k) (towerHi z) →
        artinSchreier (k + 1) (towerMk t0 t1) = z := by
      intro t0 t1 h0 h1; have hxi : towerX k * towerInvX k = 1 := towerX_mul_invX k
      have h2 := towerElem_two_eq_zero k; apply Prod.ext
      · change (t0 * t0 + t1 * t1) + t0 = towerLo z; have h0' : t0 * t0 + t0 = towerLo z + t1 * t1 := h0; linear_combination h0' + (t1 * t1) * h2
      · change ((t0 * t1 + t1 * t0) + towerX k * (t1 * t1)) + t1 = towerHi z
        have h1' : (towerX k * t1) * (towerX k * t1) + (towerX k * t1) = towerX k * towerHi z := h1
        have hmul := congrArg (towerMul k (towerInvX k)) h1'
        change towerInvX k * ((towerX k * t1) * (towerX k * t1) + towerX k * t1) = towerInvX k * (towerX k * towerHi z) at hmul
        linear_combination hmul + (t0 * t1) * h2 - (towerX k * t1 * t1 + t1 - towerHi z) * hxi
    simp only [solveArtinSchreier]
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    have hu : artinSchreier k u = towerMul k (towerX k) (towerHi z) := solveArtinSchreier_spec k _ (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u; have hxi : towerX k * towerInvX k = 1 := towerX_mul_invX k
    have hxt0 : towerMul k (towerX k) t1₀ = u := by change towerX k * (towerInvX k * u) = u; rw [← mul_assoc, hxi, one_mul]
    split
    · rename_i htr; exact step _ t1₀ (solveArtinSchreier_spec k _ htr) (by rw [hxt0]; exact hu)
    · rename_i htr
      have hxt1 : towerMul k (towerX k) (towerAdd k t1₀ (towerInvX k)) = towerAdd k u (towerOne k) := by
        change towerX k * (t1₀ + towerInvX k) = u + 1; rw [left_distrib, show towerX k * t1₀ = u from hxt0, hxi]
      have hu1 : artinSchreier k (towerAdd k u (towerOne k)) = towerMul k (towerX k) (towerHi z) := by
        rw [artinSchreier_add, hu, (artinSchreier_eq_zero_iff k (towerOne k)).mpr (Or.inr rfl)]; exact add_zero _
      exact step _ _ (solveArtinSchreier_spec k _ _) (by rw [hxt1]; exact hu1)
/-- **Additive Hilbert Theorem 90 (`2026/2770` Lemma 4.1):** `Tr_k(z) = 0 ↔ ∃ t, t^2 + t = z`. -/
theorem trace_eq_zero_iff_artin_schreier (k : Nat) (z : TowerElem k) :
    towerTrace k z = false ↔ ∃ t : TowerElem k, artinSchreier k t = z :=
  ⟨fun hz => ⟨solveArtinSchreier k z hz, solveArtinSchreier_spec k z hz⟩, fun ⟨t, ht⟩ => ht ▸ towerTrace_artinSchreier k t⟩
/-- **`#tooth` Falsifier:** any trace-1 mask `z` has no `t^2 + t` root and flips `Tr_k(Z + z)` to `true`. -/
theorem tooth_trace_one_no_artin_schreier_root (k : Nat) (z : TowerElem k) (hz : towerTrace k z = true) :
    (∀ t : TowerElem k, artinSchreier k t ≠ z) ∧
    (∀ Z : TowerElem k, towerTrace k Z = false → towerTrace k (towerAdd k Z z) = true) := by
  refine ⟨fun t ht => ?_, fun Z hZ => by rw [towerTrace_add, hZ, hz]; rfl⟩
  have h0 := towerTrace_artinSchreier k t; rw [ht, hz] at h0; cases h0
def solveArtinSchreierExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, _ => 0#1
  | k + 1, z =>
    let z0 := lowBits k z; let z1 := highBits k z
    let u := solveArtinSchreierExec k (scaleXExec k z1); let ix := invXExec k
    let t1₀ := mulExec k ix u; let rhs₀ := z0 ^^^ sqExec k t1₀
    if traceExec k rhs₀ then let t1₁ := t1₀ ^^^ ix; joinBits k (solveArtinSchreierExec k (z0 ^^^ sqExec k t1₁)) t1₁
    else joinBits k (solveArtinSchreierExec k rhs₀) t1₀
theorem solveArtinSchreierExec_refines (k : Nat) (z : TowerElem k) (hz : towerTrace k z = false) :
    solveArtinSchreierExec k (packTower k z) = packTower k (solveArtinSchreier k z hz) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let u := solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz)
    let t1₀ := towerMul k (towerInvX k) u; let rhs₀ := towerAdd k (towerLo z) (towerSq k t1₀)
    have hpk : packTower (k + 1) z = joinBits k (packTower k (towerLo z)) (packTower k (towerHi z)) := rfl
    have hmk : ∀ a b : TowerElem k, packTower (k + 1) (towerMk a b) = joinBits k (packTower k a) (packTower k b) := fun _ _ => rfl
    have huE : solveArtinSchreierExec k (scaleXExec k (packTower k (towerHi z))) = packTower k u := by
      rw [scaleXExec_refines, towerScaleX_eq_mul]; exact ih _ (towerTrace_succ_snd k z hz)
    have ht1E : mulExec k (invXExec k) (packTower k u) = packTower k t1₀ := by rw [invXExec_refines, mulExec_refines]
    have hrhsE : packTower k (towerLo z) ^^^ sqExec k (packTower k t1₀) = packTower k rhs₀ := by
      rw [sqExec, mulExec_refines, ← packTower_add]; rfl
    rw [hpk]; unfold solveArtinSchreierExec; simp only [lowBits_join, highBits_join]; rw [huE, ht1E, hrhsE, traceExec_refines]
    cases htr : towerTrace k rhs₀
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have htr' : towerTrace k (towerAdd k (towerLo z) (towerSq k (towerMul k (towerInvX k) (solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz))))) = false := htr
      have hR : solveArtinSchreier (k + 1) z hz = towerMk (solveArtinSchreier k rhs₀ htr) t1₀ := by
        conv_lhs => unfold solveArtinSchreier
        dsimp only; rw [dite_eq_left_of_eq_true (eq_true htr')]
      rw [hR, hmk]; congr 1; exact ih rhs₀ htr
    · simp only [↓reduceIte]; have htrF : ¬ (towerTrace k rhs₀ = false) := by rw [htr]; decide
      have htrF' : ¬ (towerTrace k (towerAdd k (towerLo z) (towerSq k (towerMul k (towerInvX k) (solveArtinSchreier k (towerMul k (towerX k) (towerHi z)) (towerTrace_succ_snd k z hz))))) = false) := htrF
      have hR : solveArtinSchreier (k + 1) z hz = towerMk (solveArtinSchreier k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k)))) (solveAS_flip_trace k (towerLo z) t1₀ htrF)) (towerAdd k t1₀ (towerInvX k)) := by
        conv_lhs => unfold solveArtinSchreier
        dsimp only; rw [dite_eq_right_of_eq_false (eq_false htrF')]
      rw [hR, hmk]
      have ht11 : packTower k t1₀ ^^^ invXExec k = packTower k (towerAdd k t1₀ (towerInvX k)) := by rw [invXExec_refines, ← packTower_add]
      have hrhs1 : packTower k (towerLo z) ^^^ sqExec k (packTower k (towerAdd k t1₀ (towerInvX k))) = packTower k (towerAdd k (towerLo z) (towerSq k (towerAdd k t1₀ (towerInvX k)))) := by
        rw [sqExec, mulExec_refines, ← packTower_add]; rfl
      rw [ht11, hrhs1]; congr 1; exact ih _ (solveAS_flip_trace k (towerLo z) t1₀ htrF)

/-! ## §5. Frigo–shelat §4 Frobenius Folding, Lemma 4.2 Bijection, & Soundness (Thm 3.4 / 4.3) -/
/-- **Frigo–shelat §4 Frobenius Folding:** `∑_j δ_j^2 t_j^2 = (∑_j δ_j t_j)^2`. -/
theorem frobenius_weighted_sum_sq {α : Type} [DecidableEq α] (k : Nat) (s : Finset α) (δ t : α → TowerElem k) :
    (∑ j ∈ s, (δ j) ^ 2 * (t j) ^ 2) = (∑ j ∈ s, δ j * t j) ^ 2 :=
  Finset.induction_on s (by simp) fun a s ha ih => by rw [Finset.sum_insert ha, Finset.sum_insert ha, frobenius_add, ← ih, mul_pow]
/-- **Fig. 2 Single-Mask ZK Completeness (`0` quadratic PCS constraints).** -/
theorem zk_single_mask_completeness (k M R : Nat) (X : Fin M → TowerElem k) (Q : Fin M → Fin R → TowerElem k)
    (c : Fin R → Bool) (t δ : Fin R → TowerElem k) (r : TowerElem k) :
    let ρ := towerX k
    let Z : Fin R → TowerElem k := fun j => (∑ i : Fin M, Q i j * X i) + (if c j then ρ else 0)
    let U : Fin R → TowerElem k := fun j => Z j + artinSchreier k (t j)
    let γ : Fin R → TowerElem k := fun j => (δ j) ^ 2
    let A : TowerElem k := r + ∑ j : Fin R, δ j * t j; let b : TowerElem k := r ^ 2
    let r' : Fin M → TowerElem k := fun i => ∑ j : Fin R, γ j * Q i j
    (∑ j : Fin R, γ j * (U j + (if c j then ρ else 0))) + A ^ 2 =
      (∑ i : Fin M, r' i * X i) + (∑ j : Fin R, γ j * t j) + b := by
  intro ρ Z U γ A b r'; have h2 := towerElem_two_eq_zero k
  have hA2 : A ^ 2 = b + ∑ j : Fin R, γ j * (t j) ^ 2 := by simp only [A, b, γ]; rw [frobenius_add, frobenius_weighted_sum_sq]
  have hU : ∀ j : Fin R, U j + (if c j then ρ else 0) = (∑ i : Fin M, Q i j * X i) + (t j) ^ 2 + t j := fun j => by
    have has : artinSchreier k (t j) = (t j) ^ 2 + t j := by rw [sq]; rfl
    simp only [U, Z, has]; linear_combination (if c j then ρ else 0) * h2
  have hsum : (∑ j : Fin R, γ j * (U j + (if c j then ρ else 0))) =
      (∑ i : Fin M, r' i * X i) + (∑ j : Fin R, γ j * (t j) ^ 2) + (∑ j : Fin R, γ j * t j) := by
    calc (∑ j : Fin R, γ j * (U j + (if c j then ρ else 0)))
        = ∑ j : Fin R, (γ j * (∑ i : Fin M, Q i j * X i) + γ j * (t j) ^ 2 + γ j * t j) :=
          Finset.sum_congr rfl fun j _ => by rw [hU j]; ring
      _ = (∑ j : Fin R, γ j * (∑ i : Fin M, Q i j * X i)) + (∑ j : Fin R, γ j * (t j) ^ 2) + (∑ j : Fin R, γ j * t j) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ i : Fin M, r' i * X i) + (∑ j : Fin R, γ j * (t j) ^ 2) + (∑ j : Fin R, γ j * t j) := by
          congr 2; calc (∑ j : Fin R, γ j * (∑ i : Fin M, Q i j * X i))
              = ∑ j : Fin R, ∑ i : Fin M, γ j * (Q i j * X i) := Finset.sum_congr rfl fun j _ => Finset.mul_sum ..
            _ = ∑ i : Fin M, ∑ j : Fin R, (γ j * Q i j) * X i := by
                rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
            _ = ∑ i : Fin M, r' i * X i := Finset.sum_congr rfl fun i _ => (Finset.sum_mul ..).symm
  rw [hsum, hA2]; linear_combination (∑ j : Fin R, γ j * (t j) ^ 2) * h2
theorem basisElem_zero_eq_one (k : Nat) : basisElem k ⟨0, Nat.two_pow_pos k⟩ = towerOne k := by
  induction k with | zero => rfl | succ k ih => simp only [basisElem, Nat.two_pow_pos k, ↓reduceDIte, towerOne, ih]; rfl
def implicitT0 (k : Nat) (tTail : Fin (2 ^ k - 1) → TowerElem k) : TowerElem k :=
  ∑ j : Fin (2 ^ k - 1), basisElem k ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩ * tTail j
def implicitPhi (k : Nat) (tTail : Fin (2 ^ k - 1) → TowerElem k) :
    Fin (2 ^ k) → { z : TowerElem k // towerTrace k z = false } := fun i =>
  if h : i.val = 0 then ⟨artinSchreier k (implicitT0 k tTail), towerTrace_artinSchreier k _⟩
  else ⟨artinSchreier k (tTail ⟨i.val - 1, by have := i.isLt; omega⟩), towerTrace_artinSchreier k _⟩
/-- **Frigo–shelat Lemma 4.2:** implicit-`t_0` mask map `Φ : F^{2^k-1} → (ker Tr)^{2^k}` is injective (hence bijective!). -/
theorem implicit_t0_phi_injective (k : Nat) : Function.Injective (implicitPhi k) := by
  intro t₁ t₂ hEq; let d : Fin (2 ^ k - 1) → TowerElem k := fun j => towerAdd k (t₁ j) (t₂ j)
  have hbits : ∀ j : Fin (2 ^ k - 1), d j = towerZero k ∨ d j = towerOne k := fun j => by
    have hi : j.val + 1 < 2 ^ k := by have := j.isLt; have := Nat.two_pow_pos k; omega
    have hval := congrArg Subtype.val (congrFun hEq ⟨j.val + 1, hi⟩)
    simp only [implicitPhi, show ¬ (j.val + 1 = 0) by omega, ↓reduceDIte, Nat.add_sub_cancel] at hval
    exact (artinSchreier_eq_zero_iff k (d j)).mp <| by
      rw [show artinSchreier k (d j) = towerAdd k (artinSchreier k (t₁ j)) (artinSchreier k (t₂ j))
        from artinSchreier_add k _ _, hval, towerAdd_self_zero]
  have hd0 : implicitT0 k d = towerZero k ∨ implicitT0 k d = towerOne k := by
    have hval := congrArg Subtype.val (congrFun hEq ⟨0, Nat.two_pow_pos k⟩)
    simp only [implicitPhi, ↓reduceDIte] at hval
    have hlin : implicitT0 k d = towerAdd k (implicitT0 k t₁) (implicitT0 k t₂) := by
      change (∑ j : Fin (2 ^ k - 1), basisElem k _ * (t₁ j + t₂ j)) =
        (∑ j : Fin (2 ^ k - 1), basisElem k _ * t₁ j) + (∑ j : Fin (2 ^ k - 1), basisElem k _ * t₂ j)
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => left_distrib ..
    exact (artinSchreier_eq_zero_iff k _).mp (by rw [hlin, artinSchreier_add, hval, towerAdd_self_zero])
  let bits : Fin (2 ^ k) → Bool := fun i =>
    if h : i.val = 0 then false else decide (d ⟨i.val - 1, by have := i.isLt; omega⟩ = towerOne k)
  have hpack : implicitT0 k d = packBits k bits := by
    rw [packBits_eq_sum]
    let e : Option (Fin (2 ^ k - 1)) ≃ Fin (2 ^ k) :=
      { toFun := fun o => match o with | none => ⟨0, Nat.two_pow_pos k⟩ | some j => ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩
        invFun := fun i => if h : i.val = 0 then none else some ⟨i.val - 1, by have := i.isLt; omega⟩
        left_inv := fun o => by cases o <;> simp
        right_inv := fun i => by by_cases h : i.val = 0 <;> ext <;> simp [h]; omega }
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_option]
    simp only [e, Equiv.coe_fn_mk, bits, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, zero_add]
    unfold implicitT0; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [show ¬ (j.val + 1 = 0) by omega, ↓reduceDIte, Nat.add_sub_cancel]
    rcases hbits j with hz | ho
    · have hne : (towerZero k : TowerElem k) ≠ towerOne k := fun hc =>
        zero_ne_one ((obendFieldEquiv_zero k).symm.trans ((congrArg (obendFieldEquiv k) hc).trans (obendFieldEquiv_one k)))
      rw [hz, decide_eq_false hne, towerZero_eq_zero, mul_zero]; rfl
    · rw [ho, towerOne_eq_one, mul_one, decide_eq_true rfl]; rfl
  have hzero_bits : ∀ i : Fin (2 ^ k), bits i = false := by
    rcases hd0 with hz | ho
    · intro i; rw [← pluckBit_packBits_id k bits i, ← hpack, hz]
      simp [pluckBit, show towerMul k (dualBasis k i) (towerZero k) = towerZero k from mul_zero _]
    · exfalso; have h0b := pluckBit_packBits_id k bits ⟨0, Nat.two_pow_pos k⟩
      rw [← hpack, ho, ← basisElem_zero_eq_one k] at h0b
      have h1 : pluckBit k ⟨0, Nat.two_pow_pos k⟩ (basisElem k ⟨0, Nat.two_pow_pos k⟩) = true := by
        unfold pluckBit; rw [dual_basis_biorthogonal]; rfl
      rw [h1] at h0b; simp [bits] at h0b
  funext j; have hbj := hzero_bits ⟨j.val + 1, by have := j.isLt; have := Nat.two_pow_pos k; omega⟩
  simp only [bits, show ¬ (j.val + 1 = 0) by omega, ↓reduceDIte, Nat.add_sub_cancel, decide_eq_false_iff_not] at hbj
  have h1 := congrArg (towerAdd k (t₂ j)) ((hbits j).resolve_right hbj)
  change t₂ j + (t₁ j + t₂ j) = t₂ j + 0 at h1
  rw [add_left_comm, show t₂ j + t₂ j = 0 from towerAdd_self_zero k _, add_zero, add_zero] at h1; exact h1
/-- **Theorem 4.3 Soundness Reduction:** even for forged `b ≠ r^2`, eq. (9) forces `∑ δ_j^2 E_j = r^2 + b`. -/
theorem zk_soundness_reduction (k M R : Nat) (X : Fin M → TowerElem k) (Q : Fin M → Fin R → TowerElem k)
    (c : Fin R → Bool) (t Utilde δ : Fin R → TowerElem k) (r b : TowerElem k)
    (hEq9 : let ρ := towerX k; let γ : Fin R → TowerElem k := fun j => (δ j) ^ 2
      let A : TowerElem k := r + ∑ j : Fin R, δ j * t j; let r' : Fin M → TowerElem k := fun i => ∑ j : Fin R, γ j * Q i j
      (∑ j : Fin R, γ j * (Utilde j + (if c j then ρ else 0))) + A ^ 2 = (∑ i : Fin M, r' i * X i) + (∑ j : Fin R, γ j * t j) + b) :
    let ρ := towerX k; let Z : Fin R → TowerElem k := fun j => (∑ i : Fin M, Q i j * X i) + (if c j then ρ else 0)
    (∑ j : Fin R, (δ j) ^ 2 * (Utilde j + Z j + artinSchreier k (t j))) = r ^ 2 + b := by
  intro ρ Z; have hcomp := zk_single_mask_completeness k M R X Q c t δ r
  dsimp only at hcomp hEq9; have h2 := towerElem_two_eq_zero k
  have hdiff : (∑ j : Fin R, (δ j) ^ 2 * (Utilde j + Z j + artinSchreier k (t j))) =
      (∑ j : Fin R, (δ j) ^ 2 * (Utilde j + (if c j then ρ else 0))) +
      (∑ j : Fin R, (δ j) ^ 2 * ((Z j + artinSchreier k (t j)) + (if c j then ρ else 0))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by linear_combination -((δ j) ^ 2 * (if c j then ρ else 0)) * h2
  rw [hdiff]; linear_combination hEq9 + hcomp +
    ((∑ i : Fin M, (∑ j : Fin R, (δ j) ^ 2 * Q i j) * X i) + (∑ j : Fin R, (δ j) ^ 2 * t j) -
      (r + ∑ j : Fin R, δ j * t j) ^ 2) * h2
/-- **Lemma 2.3 & Theorem 3.4 Exact Linear Batching Count (`1 / 2^(2^k)` = `2^{-256}` at `k = 8`).** -/
theorem linear_batching_false_accept_count (k N : Nat) (E : Fin N → TowerElem k)
    (kStar : Fin N) (hNe : E kStar ≠ towerZero k) (E_star : TowerElem k) :
    (Finset.univ.filter fun γ : Fin N → TowerElem k => (∑ j : Fin N, γ j * E j) = E_star).card *
      (2 ^ (2 ^ k)) = Fintype.card (Fin N → TowerElem k) := by
  have hfe_ne : obendFieldEquiv k (E kStar) ≠ 0 := fun h => hNe ((obendFieldEquiv k).injective (by simp [h]))
  let invE : TowerElem k := (obendFieldEquiv k).symm (obendFieldEquiv k (E kStar))⁻¹
  have hinv : invE * E kStar = 1 := (obendFieldEquiv k).injective <| by
    change obendFieldEquiv k (towerMul k invE (E kStar)) = obendFieldEquiv k (towerOne k)
    rw [obendFieldEquiv_tMul, Equiv.apply_symm_apply, inv_mul_cancel₀ hfe_ne, obendFieldEquiv_one]
  let rest := { j : Fin N // j ≠ kStar }
  let S := Finset.univ.filter fun γ : Fin N → TowerElem k => (∑ j : Fin N, γ j * E j) = E_star
  have hsum_erase : ∀ (γ : Fin N → TowerElem k),
      (∑ j : Fin N, γ j * E j) = γ kStar * E kStar + ∑ j ∈ Finset.univ.erase kStar, γ j * E j :=
    fun γ => (Finset.add_sum_erase Finset.univ (fun j => γ j * E j) (Finset.mem_univ kStar)).symm
  let e : S ≃ (rest → TowerElem k) :=
    { toFun := fun γ r => γ.1 r.1
      invFun := fun f =>
        ⟨fun j => if h : j = kStar then invE * (E_star + ∑ r : rest, f r * E r.1) else f ⟨j, h⟩, by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hsum_erase]; simp only [↓reduceDIte]
          have hsub : (∑ j ∈ Finset.univ.erase kStar,
              (if h : j = kStar then invE * (E_star + ∑ r : rest, f r * E r.1) else f ⟨j, h⟩) * E j) =
              ∑ r : rest, f r * E r.1 :=
            Finset.sum_bij (fun j hj => ⟨j, (Finset.mem_erase.mp hj).1⟩) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun r _ => ⟨r.1, Finset.mem_erase.mpr ⟨r.2, Finset.mem_univ _⟩, rfl⟩)
              (fun j hj => by simp [(Finset.mem_erase.mp hj).1])
          rw [hsub, show invE * (E_star + ∑ r : rest, f r * E r.1) * E kStar =
            (invE * E kStar) * (E_star + ∑ r : rest, f r * E r.1) by ring, hinv, one_mul]
          linear_combination (∑ r : rest, f r * E r.1) * towerElem_two_eq_zero k⟩
      left_inv := fun ⟨γ, hγ⟩ => by
        apply Subtype.ext; funext j; by_cases hj : j = kStar
        · rw [hj]; simp only [↓reduceDIte]; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
          have hsub : (∑ r : rest, γ r.1 * E r.1) = ∑ i ∈ Finset.univ.erase kStar, γ i * E i :=
            (Finset.sum_bij (fun i hi => ⟨i, (Finset.mem_erase.mp hi).1⟩) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun r _ => ⟨r.1, Finset.mem_erase.mpr ⟨r.2, Finset.mem_univ _⟩, rfl⟩)
              (fun _ _ => rfl)).symm
          rw [hsum_erase] at hγ; rw [hsub]
          have hrel : γ kStar * E kStar = E_star + ∑ i ∈ Finset.univ.erase kStar, γ i * E i := by
            linear_combination hγ - (∑ i ∈ Finset.univ.erase kStar, γ i * E i) * towerElem_two_eq_zero k
          rw [← hrel, show invE * (γ kStar * E kStar) = (invE * E kStar) * γ kStar by ring, hinv, one_mul]
        · simp [hj]
      right_inv := fun f => by funext r; simp [r.2] }
  have hcardS : S.card = Fintype.card (rest → TowerElem k) := by rw [← Fintype.card_coe]; exact Fintype.card_congr e
  have hrest : Fintype.card rest + 1 = N := by
    have h1 := Fintype.card_subtype_compl (fun j : Fin N => j = kStar)
    have h2 : Fintype.card { j : Fin N // j = kStar } = 1 := Fintype.card_unique
    have hN : 1 ≤ N := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 kStar)
    change Fintype.card { j : Fin N // ¬ j = kStar } + 1 = N; rw [h1, h2, Fintype.card_fin]; omega
  rw [hcardS, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, card_towerElem, ← pow_succ, hrest]
/-- **Theorem 4.3 Squared-Challenge Batching Count (`γ_j = δ_j^2`, exact `1 / 2^(2^k)`).** -/
theorem squared_batching_false_accept_count (k N : Nat) (E : Fin N → TowerElem k)
    (kStar : Fin N) (hNe : E kStar ≠ towerZero k) (E_star : TowerElem k) :
    (Finset.univ.filter fun δ : Fin N → TowerElem k => (∑ j : Fin N, (δ j) ^ 2 * E j) = E_star).card *
      (2 ^ (2 ^ k)) = Fintype.card (Fin N → TowerElem k) := by
  let sqEquiv : (Fin N → TowerElem k) ≃ (Fin N → TowerElem k) :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.ofBijective (towerSq k) (towerSq_bijective k))
  have hsq_app : ∀ (δ : Fin N → TowerElem k) (j : Fin N), sqEquiv δ j = (δ j) ^ 2 := fun δ j => by
    change towerSq k (δ j) = (δ j) ^ 2; rw [sq]; rfl
  have hcard : (Finset.univ.filter fun δ : Fin N → TowerElem k => (∑ j : Fin N, (δ j) ^ 2 * E j) = E_star).card =
      (Finset.univ.filter fun γ : Fin N → TowerElem k => (∑ j : Fin N, γ j * E j) = E_star).card := by
    refine Finset.card_bij (fun δ _ => sqEquiv δ)
      (fun δ hδ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢; simpa [hsq_app] using hδ)
      (fun _ _ _ _ h => sqEquiv.injective h) (fun γ hγ => ⟨sqEquiv.symm γ, ?_, sqEquiv.apply_symm_apply γ⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
    have hsq : ∀ j, (sqEquiv.symm γ j) ^ 2 = γ j := fun j => by
      rw [← hsq_app]; exact congrFun (sqEquiv.apply_symm_apply γ) j
    simpa [hsq] using hγ
  rw [hcard]; exact linear_batching_false_accept_count k N E kStar hNe E_star
open Classical in
/-- **Single-Challenge Vandermonde Power-Batching Soundness (`≤ (N - 1) / 2^(2^k)` = `≤ 255 / 2^{256}`).** -/
theorem power_batching_roots_le (k N : Nat) (E : Fin N → TowerElem k)
    (kStar : Fin N) (hNe : E kStar ≠ towerZero k) :
    (Finset.univ.filter fun δ : TowerElem k => (∑ j : Fin N, δ ^ j.val * E j) = towerZero k).card ≤ N - 1 := by
  let p : Polynomial (binaryTower k) := ∑ j : Fin N, Polynomial.C (obendFieldEquiv k (E j)) * Polynomial.X ^ j.val
  have hp_coeff : ∀ m : Nat, p.coeff m = if h : m < N then obendFieldEquiv k (E ⟨m, h⟩) else 0 := by
    intro m; simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hm : m < N
    · simp only [hm, ↓reduceDIte]; rw [Finset.sum_eq_single ⟨m, hm⟩]
      · simp
      · intro j _ hj; simp [show m ≠ j.val from fun h => hj (Fin.ext h.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hm, ↓reduceDIte]; exact Finset.sum_eq_zero fun j _ => by simp [show m ≠ j.val by omega]
  have hp_ne : p ≠ 0 := fun h0 => by
    have hc := hp_coeff kStar.val; simp only [h0, Polynomial.coeff_zero, kStar.isLt, ↓reduceDIte] at hc
    exact hNe ((obendFieldEquiv k).injective (by simp [hc.symm]))
  have hp_deg : p.natDegree ≤ N - 1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
    rw [hp_coeff]; have hN : 1 ≤ N := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Fin.elim0 kStar)
    simp only [show ¬ (m < N) by omega, ↓reduceDIte]
  have hsub : (Finset.univ.filter fun δ : TowerElem k => (∑ j : Fin N, δ ^ j.val * E j) = towerZero k).image
      (obendFieldEquiv k) ⊆ p.roots.toFinset := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨δ, hδ, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def]
    have hev : Polynomial.eval (obendFieldEquiv k δ) p = obendFieldEquiv k (∑ j : Fin N, δ ^ j.val * E j) := by
      change Polynomial.eval (obendFieldEquiv k δ) p = obendRingEquiv k (∑ j : Fin N, δ ^ j.val * E j)
      simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_pow, mul_comm]; rfl
    rw [hev, hδ, obendFieldEquiv_zero]
  calc (Finset.univ.filter fun δ : TowerElem k => (∑ j : Fin N, δ ^ j.val * E j) = towerZero k).card
      = ((Finset.univ.filter fun δ : TowerElem k => (∑ j : Fin N, δ ^ j.val * E j) = towerZero k).image
          (obendFieldEquiv k)).card := (Finset.card_image_of_injective _ (obendFieldEquiv k).injective).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ N - 1 := hp_deg

/-! ## §6. Conformance Vector Emitter & `#guard_msgs`-Pinned `#print axioms` -/
private def hexByte (b : Nat) : String :=
  let d := "0123456789abcdef".toList; String.ofList [d[(b / 16) % 16]!, d[b % 16]!]
private def bv256ToLeHex (x : BitVec 256) : String :=
  String.join ((List.range 32).map fun i => hexByte ((x.toNat / (256 ^ i)) % 256))
private def jBool (b : Bool) : String := if b then "true" else "false"
private def jStrs (xs : List String) : String := "[" ++ String.intercalate ", " (xs.map fun s => "\"" ++ s ++ "\"") ++ "]"
private def emitTracePackConformance (path : System.FilePath) : IO Unit := do
  let tmask := traceMask 8; let rho : BitVec 256 := 1#256 <<< 128; let topMono : BitVec 256 := 1#256 <<< 255
  let dual := dualBasisExec 8
  let okMask := tmask == 0x26c6636dc63a6da5c63a6da56da5a55700000000000000000000000000000000#256
  let okRho := traceExec 8 rho == true; let okTopZero := traceExec 8 topMono == false
  let mut okDualDiag := dual.size == 256
  for i in [0, 1, 7, 8, 63, 64, 127, 128, 129, 191, 254, 255] do
    let ai := dual[i]!
    if traceExec 8 (mulExec 8 ai (1#256 <<< i)) != true ||
       traceExec 8 (mulExec 8 ai (1#256 <<< ((i + 1) % 256))) != false then okDualDiag := false
  let rawSeeds : List (BitVec 256) := [0#256, 1#256,
    0x0123456789abcdef0fedcba9876543210f0ff0f055aaaa558000000000000001#256,
    0xdeadbeefcafebabe1122334455667788aaaa5555ffff00000102030405060708#256,
    0x201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201#256, topMono]
  let mut okAS := true; let mut asJson : List String := []
  for raw in rawSeeds do
    let z := if traceExec 8 raw then raw ^^^ rho else raw; let t := solveArtinSchreierExec 8 z
    if traceExec 8 z != false || (sqExec 8 t ^^^ t) != z then okAS := false
    asJson := asJson ++ [s!"    \{\"z_hex\": \"{bv256ToLeHex z}\", \"trace\": false, \"t_hex\": \"{bv256ToLeHex t}\"}"]
  let s2 : BitVec 256 := 0x0123456789abcdef0fedcba9876543210f0ff0f055aaaa558000000000000001#256
  for z in [rho, if traceExec 8 s2 then s2 else s2 ^^^ rho] do
    if traceExec 8 z != true then okAS := false
    asJson := asJson ++ [s!"    \{\"z_hex\": \"{bv256ToLeHex z}\", \"trace\": true, \"t_hex\": null}"]
  let xs : List (BitVec 256) := [0x00112233445566778899aabbccddeeff0123456789abcdef1032547698badcfe#256,
    0xfedcba9876543210ffeeddccbbaa99887766554433221100a5a55a5a3c3cc3c3#256,
    0x13579bdf2468ace0ffff0000ffff000031415926535897932718281828459045#256,
    0x80000000000000010f0ff0f055aaaa55fedcba98765432100123456789abcdef#256]
  let cs : List (BitVec 256) := [0x111122223333444455556666777788889999aaaabbbbccccddddeeeeffff0001#256,
    0x020406080a0c0e10121416181a1c1e20222426282a2c2e30323436383a3c3e40#256,
    0xdead0001beef0002cafe0003babe0004feed0005face0006bead0007deed0008#256,
    0x7777666655554444333322221111000088889999aaaabbbbccccddddeeeeffff#256]
  let dSeed : BitVec 256 := 0x0f1e2d3c4b5a69788796a5b4c3d2e1f00123456789abcdef1122334455667788#256
  let mut yVal : BitVec 256 := 0#256
  for i in List.range 4 do yVal := yVal ^^^ mulExec 8 cs[i]! (mulExec 8 xs[i]! dSeed)
  let checkBit (bitK : Nat) : BitVec 256 × Bool := Id.run do
    let mut zAcc : BitVec 256 := if yVal.getLsbD bitK then rho else 0#256
    for i in List.range 4 do zAcc := zAcc ^^^ mulExec 8 (mulExec 8 dual[bitK]! (mulExec 8 cs[i]! dSeed)) xs[i]!
    return (zAcc, traceExec 8 zAcc == false)
  let (z0, okZ0) := checkBit 0; let (z128, okZ128) := checkBit 128
  unless okMask && okRho && okTopZero && okDualDiag && okAS && okZ0 && okZ128 do
    throw (IO.userError "Tower256TraceBitPacking self-check failed")
  let json :=
    "{\n  \"schema\": \"minidregg.tower256_trace_pack_conformance.v1\", \"source\": \"Theory/Tower256TraceBitPacking.lean\",\n" ++
    s!"  \"trace_mask_hex\": \"{bv256ToLeHex tmask}\", \"rho_hex\": \"{bv256ToLeHex rho}\",\n" ++
    s!"  \"top_monomial_hex\": \"{bv256ToLeHex topMono}\", \"top_monomial_trace\": false,\n" ++
    s!"  \"dual_basis_hex\": {jStrs (dual.toList.map bv256ToLeHex)},\n" ++
    "  \"artin_schreier_vectors\": [\n" ++ String.intercalate ",\n" asJson ++ "\n  ],\n" ++
    s!"  \"packed_tensor_claim\": \{\"x_hex\": {jStrs (xs.map bv256ToLeHex)}, \"c_hex\": {jStrs (cs.map bv256ToLeHex)}, " ++
    s!"\"d_seed_hex\": \"{bv256ToLeHex dSeed}\", \"y_hex\": \"{bv256ToLeHex yVal}\", " ++
    s!"\"z_bit0_hex\": \"{bv256ToLeHex z0}\", \"z_bit128_hex\": \"{bv256ToLeHex z128}\"},\n" ++
    s!"  \"lean_self_checks\": \{\"trace_mask_ok\": {jBool okMask}, \"rho_trace_one\": {jBool okRho}, " ++
    s!"\"top_monomial_trace_zero\": {jBool okTopZero}, \"dual_basis_ok\": {jBool okDualDiag}, " ++
    s!"\"artin_schreier_ok\": {jBool okAS}, \"tensor_z0_ok\": {jBool okZ0}, \"tensor_z128_ok\": {jBool okZ128}}\n}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json
#eval emitTracePackConformance "prover/testdata/tower256_trace_pack_conformance.json"
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.relTrace_eq_frob_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relTrace_eq_frob_sum
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.towerTrace_eq_bTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerTrace_eq_bTrace
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.towerTrace_eq_mask_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerTrace_eq_mask_parity
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.tooth_fanpaar_top_monomial_trace_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_fanpaar_top_monomial_trace_zero
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.dual_basis_biorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dual_basis_biorthogonal
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.dual_basis_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dual_basis_unique
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.pluckBit_packBits_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pluckBit_packBits_id
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.packBits_pluckBit_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packBits_pluckBit_id
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.bit_inner_product_iff_trace_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bit_inner_product_iff_trace_zero
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.tensor_coeff_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tensor_coeff_factorization
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.solveArtinSchreier_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms solveArtinSchreier_spec
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.trace_eq_zero_iff_artin_schreier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trace_eq_zero_iff_artin_schreier
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.tooth_trace_one_no_artin_schreier_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_trace_one_no_artin_schreier_root
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.frobenius_weighted_sum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frobenius_weighted_sum_sq
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.zk_single_mask_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zk_single_mask_completeness
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.implicit_t0_phi_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms implicit_t0_phi_injective
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.zk_soundness_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zk_soundness_reduction
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.linear_batching_false_accept_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linear_batching_false_accept_count
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.squared_batching_false_accept_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms squared_batching_false_accept_count
/-- info: 'Minidregg.Theory.Tower256TraceBitPacking.power_batching_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms power_batching_roots_le

end Minidregg.Theory.Tower256TraceBitPacking
