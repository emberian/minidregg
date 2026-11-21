/-
# `Theory/Tower256EndianBridge.lean` — Cross-Tree Gate `G4`:
32-Byte Little-Endian vs Big-Endian Fan–Paar `Tower256` (`GF(2^256)`) Wire Isomorphism
& Conformance Bridge

Closes Cross-Tree Gate `G4` (`MASTER_REVIVAL_ALIGNMENT.md` §2.5.1 & §4.1) between:
- `obend/lean/Obend/Crypto/BinaryTower256.lean:11-560` + `Obend/Digest/HashBytes.lean:24-30`
  (`TowerElem k`, `packTower : TowerElem k → BitVec (2^k)`, Big-Endian 32-byte `toBytes32`/`ofBytes32`)
- `minidregg/Theory/BinaryTowerFanPaarCodec.lean:55-348` + `Theory/BinaryTowerCoordinateArith.lean`
  (`Coordinate k`, `coordinateFieldEquiv`, `coordinateFinEquiv`, Little-Endian 32-byte `encode`/`decode`)
- `zkml-research/native/qwen35audit/src/bpe_bridge.rs:78-361` &
  `minidregg/prover/src/binary_tower_256.rs:70-190` (`[u64; 4]` LE limbs `to_le_bytes`/`from_le_bytes`).

Import boundary: `Theory/` tier (`Mathlib.*` + `Theory.*` only).
-/

import Theory.BinaryTowerCoordinateArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace Minidregg.Theory.Tower256EndianBridge

open Minidregg.Theory
open Minidregg.Theory.BinaryTowerFanPaarCodec

set_option autoImplicit false

private theorem pow_256_32_eq : 256 ^ 32 = 2 ^ 256 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul]; rfl

private theorem pow_256_8_eq : 256 ^ 8 = 2 ^ 64 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_mul]

/-! ## §1. Verbatim Mirror of `Obend.Crypto.BinaryTower256` & `Obend.Digest.HashBytes` -/

def ObendTowerElem : Nat → Type
  | 0 => Bool
  | k + 1 => ObendTowerElem k × ObendTowerElem k

abbrev ObendTower128 := ObendTowerElem 7
abbrev ObendTower256 := ObendTowerElem 8
abbrev TowerBitVec (k : Nat) := BitVec (2 ^ k)
abbrev Tower256Exec := BitVec 256

def towerZero : (k : Nat) → ObendTowerElem k
  | 0 => false | k + 1 => (towerZero k, towerZero k)
def towerOne : (k : Nat) → ObendTowerElem k
  | 0 => true | k + 1 => (towerOne k, towerZero k)
def towerX : (k : Nat) → ObendTowerElem k
  | 0 => true | k + 1 => (towerZero k, towerOne k)
def towerAdd : (k : Nat) → ObendTowerElem k → ObendTowerElem k → ObendTowerElem k
  | 0, a, b => a ^^ b | k + 1, a, b => (towerAdd k a.1 b.1, towerAdd k a.2 b.2)
def towerMul : (k : Nat) → ObendTowerElem k → ObendTowerElem k → ObendTowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2),
     towerAdd k (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
       (towerMul k (towerX k) (towerMul k a.2 b.2)))
def towerScaleX : (k : Nat) → ObendTowerElem k → ObendTowerElem k
  | 0, a => a | k + 1, a => (a.2, towerAdd k a.1 (towerScaleX k a.2))
def towerNorm (k : Nat) (a : ObendTowerElem (k + 1)) : ObendTowerElem k :=
  towerAdd k (towerAdd k (towerMul k a.1 a.1)
    (towerMul k (towerX k) (towerMul k a.1 a.2))) (towerMul k a.2 a.2)
def towerInv : (k : Nat) → ObendTowerElem k → ObendTowerElem k
  | 0, a => a
  | k + 1, a =>
    let ni := towerInv k (towerNorm k a)
    (towerMul k (towerAdd k a.1 (towerMul k (towerX k) a.2)) ni, towerMul k a.2 ni)
def towerSq (k : Nat) (a : ObendTowerElem k) : ObendTowerElem k := towerMul k a a
def towerFrob (k : Nat) : Nat → ObendTowerElem k → ObendTowerElem k
  | 0, a => a | n + 1, a => towerSq k (towerFrob k n a)
instance obendTowerDecidableEq : (k : Nat) → DecidableEq (ObendTowerElem k)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | k + 1 => @instDecidableEqProd _ _ (obendTowerDecidableEq k) (obendTowerDecidableEq k)
def joinBits (k : Nat) (lo hi : TowerBitVec k) : TowerBitVec (k + 1) :=
  (hi ++ lo).cast (by simp [Nat.pow_succ, Nat.mul_two])
def lowBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' 0 (2 ^ k)
def highBits (k : Nat) (a : TowerBitVec (k + 1)) : TowerBitVec k := a.extractLsb' (2 ^ k) (2 ^ k)
def packTower : (k : Nat) → ObendTowerElem k → TowerBitVec k
  | 0, a => BitVec.ofBool a | k + 1, a => joinBits k (packTower k a.1) (packTower k a.2)
def unpackTower : (k : Nat) → TowerBitVec k → ObendTowerElem k
  | 0, a => a.getLsbD 0 | k + 1, a => (unpackTower k (lowBits k a), unpackTower k (highBits k a))
def scaleXExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, a => a | k + 1, a => joinBits k (highBits k a) (lowBits k a ^^^ scaleXExec k (highBits k a))

def mulExec : (k : Nat) → TowerBitVec k → TowerBitVec k → TowerBitVec k
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let al := lowBits k a; let ah := highBits k a
    let bl := lowBits k b; let bh := highBits k b
    let p := mulExec k al bl; let q := mulExec k ah bh
    let r := mulExec k (al ^^^ ah) (bl ^^^ bh)
    joinBits k (p ^^^ q) (r ^^^ (p ^^^ q) ^^^ scaleXExec k q)

def invExec : (k : Nat) → TowerBitVec k → TowerBitVec k
  | 0, a => a
  | k + 1, a =>
    let lo := lowBits k a; let hi := highBits k a
    let norm := mulExec k lo lo ^^^ scaleXExec k (mulExec k lo hi) ^^^ mulExec k hi hi
    let ni := invExec k norm
    joinBits k (mulExec k (lo ^^^ scaleXExec k hi) ni) (mulExec k hi ni)

def obendBE : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => obendBE w (n / 256) ++ [UInt8.ofNat (n % 256)]

def obendOfBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

def obendToBytes32 (a : Tower256Exec) : List UInt8 := obendBE 32 a.toNat
def obendOfBytes32 (bs : List UInt8) : Option Tower256Exec :=
  if bs.length = 32 then some (BitVec.ofNat 256 (obendOfBE bs)) else none
def obendToBytes32BA (a : Tower256Exec) : ByteArray := ⟨(obendBE 32 a.toNat).toArray⟩
def obendOfBytes32BA (bs : ByteArray) : Option Tower256Exec :=
  if bs.size = 32 then some (BitVec.ofNat 256 (obendOfBE bs.data.toList)) else none
def obendToBytes32LE (a : Tower256Exec) : List UInt8 := (obendBE 32 a.toNat).reverse
def obendOfBytes32LE (bs : List UInt8) : Option Tower256Exec :=
  if bs.length = 32 then some (BitVec.ofNat 256 (obendOfBE bs.reverse)) else none
def obendToBytes32LEBA (a : Tower256Exec) : ByteArray := ⟨(obendBE 32 a.toNat).reverse.toArray⟩
def obendOfBytes32LEBA (bs : ByteArray) : Option Tower256Exec :=
  if bs.size = 32 then some (BitVec.ofNat 256 (obendOfBE bs.data.toList.reverse)) else none

/-! ## §2. Exact Coordinate, Ring, Inverse, and Frobenius Isomorphism -/

def obendToCoord : (k : Nat) → ObendTowerElem k → Coordinate k
  | 0, b => .bit b | k + 1, a => .pair (obendToCoord k a.1) (obendToCoord k a.2)
def coordToObend : {k : Nat} → Coordinate k → ObendTowerElem k
  | 0, .bit b => b | _ + 1, .pair l h => (coordToObend l, coordToObend h)
@[simp] theorem coordToObend_obendToCoord (k : Nat) (a : ObendTowerElem k) :
    coordToObend (obendToCoord k a) = a := by
  induction k with | zero => rfl | succ k ih => exact Prod.ext (ih a.1) (ih a.2)
@[simp] theorem obendToCoord_coordToObend {k : Nat} (c : Coordinate k) :
    obendToCoord k (coordToObend c) = c := by
  induction c with | bit _ => rfl | pair _ _ ihl ihh => exact congrArg₂ Coordinate.pair ihl ihh
def obendCoordEquiv (k : Nat) : ObendTowerElem k ≃ Coordinate k where
  toFun := obendToCoord k; invFun := coordToObend
  left_inv := coordToObend_obendToCoord k; right_inv := obendToCoord_coordToObend
@[simp] theorem obendToCoord_zero (k : Nat) : obendToCoord k (towerZero k) = Coordinate.zero k := by
  induction k with | zero => rfl | succ k ih => simp [towerZero, obendToCoord, Coordinate.zero, ih]
@[simp] theorem obendToCoord_one (k : Nat) : obendToCoord k (towerOne k) = Coordinate.one k := by
  induction k with | zero => rfl | succ k ih => simp [towerOne, obendToCoord, Coordinate.one, ih, obendToCoord_zero]
@[simp] theorem obendToCoord_towerX (k : Nat) : obendToCoord k (towerX k) = Coordinate.mulCoeff k := by
  cases k with
  | zero => rfl
  | succ k => simp [towerX, obendToCoord, Coordinate.mulCoeff, Coordinate.topGenerator, obendToCoord_zero, obendToCoord_one]
noncomputable def obendFieldEquiv (k : Nat) : ObendTowerElem k ≃ binaryTower k :=
  (obendCoordEquiv k).trans (coordinateFieldEquiv k)
@[simp] theorem obendFieldEquiv_pair {k : Nat} (a : ObendTowerElem (k + 1)) :
    obendFieldEquiv (k + 1) a = towerPack k (obendFieldEquiv k a.1, obendFieldEquiv k a.2) := rfl
@[simp] theorem obendFieldEquiv_mk {k : Nat} (l h : ObendTowerElem k) :
    obendFieldEquiv (k + 1) (l, h) = towerPack k (obendFieldEquiv k l, obendFieldEquiv k h) := rfl
@[simp] theorem obendFieldEquiv_zero (k : Nat) : obendFieldEquiv k (towerZero k) = 0 := by
  simp [obendFieldEquiv, obendCoordEquiv]
@[simp] theorem obendFieldEquiv_one (k : Nat) : obendFieldEquiv k (towerOne k) = 1 := by
  simp [obendFieldEquiv, obendCoordEquiv]
@[simp] theorem obendFieldEquiv_towerX (k : Nat) : obendFieldEquiv k (towerX k) = towerMulCoeff k := by
  simp [obendFieldEquiv, obendCoordEquiv, coordinateFieldEquiv_mulCoeff]

theorem obendFieldEquiv_add (k : Nat) (a b : ObendTowerElem k) :
    obendFieldEquiv k (towerAdd k a b) = obendFieldEquiv k a + obendFieldEquiv k b := by
  induction k with
  | zero =>
    change Bool at a b
    have h0 : ∀ x : Bool, obendFieldEquiv 0 x = if x then 1 else 0 := coordinateFieldEquiv_bit
    change obendFieldEquiv 0 (a ^^ b) = obendFieldEquiv 0 a + obendFieldEquiv 0 b
    rw [h0, h0, h0]
    cases a <;> cases b <;> simp [one_add_one_eq_two, binaryTower_two_eq_zero 0]
  | succ k ih =>
    simp only [towerAdd, obendFieldEquiv_mk, obendFieldEquiv_pair, ih, towerPack, map_add]
    ring

theorem obendFieldEquiv_mul (k : Nat) (a b : ObendTowerElem k) :
    obendFieldEquiv k (towerMul k a b) = obendFieldEquiv k a * obendFieldEquiv k b := by
  induction k with
  | zero =>
    change Bool at a b
    have h0 : ∀ x : Bool, obendFieldEquiv 0 x = if x then 1 else 0 := coordinateFieldEquiv_bit
    change obendFieldEquiv 0 (a && b) = obendFieldEquiv 0 a * obendFieldEquiv 0 b
    rw [h0, h0, h0]
    cases a <;> cases b <;> simp
  | succ k ih =>
    have h2 : (2 : binaryTower k) = 0 := binaryTower_two_eq_zero k
    rw [obendFieldEquiv_pair, obendFieldEquiv_pair a, obendFieldEquiv_pair b,
      ← towerPack_towerMulStep]
    congr 1
    simp only [towerMul, obendFieldEquiv_add, ih, obendFieldEquiv_towerX, towerMulStep]
    apply Prod.ext
    · rfl
    · linear_combination
        -(obendFieldEquiv k a.1 * obendFieldEquiv k b.1 +
          obendFieldEquiv k a.2 * obendFieldEquiv k b.2) * h2

theorem obendFieldEquiv_scaleX (k : Nat) (a : ObendTowerElem k) :
    obendFieldEquiv k (towerScaleX k a) = towerMulCoeff k * obendFieldEquiv k a := by
  induction k with
  | zero => simp [towerScaleX, towerMulCoeff]
  | succ k ih =>
    have hy := fpGen_quadratic k
    have h2 : (2 : binaryTower (k + 1)) = 0 := binaryTower_two_eq_zero (k + 1)
    simp only [towerScaleX, obendFieldEquiv_mk, obendFieldEquiv_pair, obendFieldEquiv_add, ih,
      towerMulCoeff_succ, towerPack, map_add, map_mul]
    linear_combination -(binaryTowerEmbed k (obendFieldEquiv k a.2)) * hy +
      (binaryTowerEmbed k (obendFieldEquiv k a.2) * fpGen k *
        binaryTowerEmbed k (towerMulCoeff k) +
        binaryTowerEmbed k (obendFieldEquiv k a.2)) * h2

theorem obendToCoord_add (k : Nat) (a b : ObendTowerElem k) :
    obendToCoord k (towerAdd k a b) = Coordinate.add k (obendToCoord k a) (obendToCoord k b) := by
  apply (coordinateFieldEquiv k).injective
  rw [coordinateFieldEquiv_add]
  exact obendFieldEquiv_add k a b

theorem obendToCoord_mul (k : Nat) (a b : ObendTowerElem k) :
    obendToCoord k (towerMul k a b) = Coordinate.mul k (obendToCoord k a) (obendToCoord k b) := by
  apply (coordinateFieldEquiv k).injective
  rw [coordinateFieldEquiv_mul]
  exact obendFieldEquiv_mul k a b

instance instZeroObendTowerElem (k : Nat) : Zero (ObendTowerElem k) := ⟨towerZero k⟩
instance instOneObendTowerElem (k : Nat) : One (ObendTowerElem k) := ⟨towerOne k⟩
instance instAddObendTowerElem (k : Nat) : Add (ObendTowerElem k) := ⟨towerAdd k⟩
instance instMulObendTowerElem (k : Nat) : Mul (ObendTowerElem k) := ⟨towerMul k⟩
instance instNegObendTowerElem (k : Nat) : Neg (ObendTowerElem k) := ⟨id⟩
instance instSubObendTowerElem (k : Nat) : Sub (ObendTowerElem k) := ⟨towerAdd k⟩

/-- `CommRing` on `ObendTowerElem k` with definitional Obend operations `0, 1, +, *`. -/
instance instCommRingObendTowerElem (k : Nat) : CommRing (ObendTowerElem k) where
  zero := towerZero k; one := towerOne k; add := towerAdd k; mul := towerMul k
  neg := id; sub := towerAdd k; nsmul := nsmulRec; zsmul := zsmulRec; npow := npowRec
  sub_eq_add_neg _ _ := rfl
  add_assoc a b c := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerAdd k (towerAdd k a b) c) = obendFieldEquiv k (towerAdd k a (towerAdd k b c))
    simp [obendFieldEquiv_add, add_assoc])
  zero_add a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerAdd k (towerZero k) a) = obendFieldEquiv k a; simp [obendFieldEquiv_add])
  add_zero a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerAdd k a (towerZero k)) = obendFieldEquiv k a; simp [obendFieldEquiv_add])
  add_comm a b := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerAdd k a b) = obendFieldEquiv k (towerAdd k b a); simp [obendFieldEquiv_add, add_comm])
  neg_add_cancel a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerAdd k a a) = obendFieldEquiv k (towerZero k)
    rw [obendFieldEquiv_add, obendFieldEquiv_zero]; linear_combination obendFieldEquiv k a * binaryTower_two_eq_zero k)
  mul_assoc a b c := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k (towerMul k a b) c) = obendFieldEquiv k (towerMul k a (towerMul k b c))
    simp [obendFieldEquiv_mul, mul_assoc])
  one_mul a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k (towerOne k) a) = obendFieldEquiv k a; simp [obendFieldEquiv_mul])
  mul_one a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k a (towerOne k)) = obendFieldEquiv k a; simp [obendFieldEquiv_mul])
  mul_comm a b := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k a b) = obendFieldEquiv k (towerMul k b a); simp [obendFieldEquiv_mul, mul_comm])
  left_distrib a b c := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k a (towerAdd k b c)) = obendFieldEquiv k (towerAdd k (towerMul k a b) (towerMul k a c))
    simp [obendFieldEquiv_mul, obendFieldEquiv_add, mul_add])
  right_distrib a b c := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k (towerAdd k a b) c) = obendFieldEquiv k (towerAdd k (towerMul k a c) (towerMul k b c))
    simp [obendFieldEquiv_mul, obendFieldEquiv_add, add_mul])
  zero_mul a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k (towerZero k) a) = obendFieldEquiv k (towerZero k); simp [obendFieldEquiv_mul])
  mul_zero a := (obendFieldEquiv k).injective (by
    show obendFieldEquiv k (towerMul k a (towerZero k)) = obendFieldEquiv k (towerZero k); simp [obendFieldEquiv_mul])

/-- **Ring isomorphism `ObendTowerElem k ≃+* binaryTower k`** for every level `k`. -/
noncomputable def obendRingEquiv (k : Nat) : ObendTowerElem k ≃+* binaryTower k where
  toEquiv := obendFieldEquiv k
  map_mul' := obendFieldEquiv_mul k
  map_add' := obendFieldEquiv_add k

private theorem obendFieldEquiv_mul_conjugate (k : Nat) (a : ObendTowerElem (k + 1)) :
    obendFieldEquiv (k + 1) a *
      towerPack k (obendFieldEquiv k a.1 + towerMulCoeff k * obendFieldEquiv k a.2,
        obendFieldEquiv k a.2) =
      binaryTowerEmbed k (obendFieldEquiv k (towerNorm k a)) := by
  have hy := fpGen_quadratic k
  have h2 : (2 : binaryTower (k + 1)) = 0 := binaryTower_two_eq_zero (k + 1)
  simp only [obendFieldEquiv_pair, towerNorm, obendFieldEquiv_add, obendFieldEquiv_mul,
    obendFieldEquiv_towerX, towerPack, map_add, map_mul]
  linear_combination
    (binaryTowerEmbed k (obendFieldEquiv k a.2) *
      binaryTowerEmbed k (obendFieldEquiv k a.2)) * hy +
    (binaryTowerEmbed k (obendFieldEquiv k a.1) *
      binaryTowerEmbed k (obendFieldEquiv k a.2) * fpGen k -
      binaryTowerEmbed k (obendFieldEquiv k a.2) *
      binaryTowerEmbed k (obendFieldEquiv k a.2)) * h2

/-- **Field inversion isomorphism**: `towerInv k a ↦ (obendFieldEquiv k a)⁻¹` (including `0⁻¹ = 0`). -/
theorem obendFieldEquiv_inv (k : Nat) (a : ObendTowerElem k) :
    obendFieldEquiv k (towerInv k a) = (obendFieldEquiv k a)⁻¹ := by
  induction k with
  | zero =>
    change Bool at a
    have h0 : ∀ x : Bool, obendFieldEquiv 0 x = if x then 1 else 0 := coordinateFieldEquiv_bit
    change obendFieldEquiv 0 a = (obendFieldEquiv 0 a)⁻¹
    rw [h0]; cases a <;> simp
  | succ k ih =>
    by_cases ha : obendFieldEquiv (k + 1) a = 0
    · have ha0 : a = towerZero (k + 1) :=
        (obendFieldEquiv (k + 1)).injective (by rw [ha, obendFieldEquiv_zero])
      subst ha0
      have hnorm0 : towerNorm k (towerZero (k + 1)) = towerZero k :=
        (obendFieldEquiv k).injective (by
          simp [towerNorm, towerZero, obendFieldEquiv_add, obendFieldEquiv_mul])
      have hinv0 : obendFieldEquiv k (towerInv k (towerZero k)) = 0 := by
        rw [ih, obendFieldEquiv_zero, inv_zero]
      rw [ha, inv_zero]
      simp only [towerInv, hnorm0, obendFieldEquiv_mk, obendFieldEquiv_mul, hinv0,
        mul_zero, towerPack, map_zero, zero_mul, add_zero]
    · have hconj_ne :
          towerPack k (obendFieldEquiv k a.1 + towerMulCoeff k * obendFieldEquiv k a.2,
            obendFieldEquiv k a.2) ≠ 0 := by
        intro hzc
        have hzp : (obendFieldEquiv k a.1 + towerMulCoeff k * obendFieldEquiv k a.2,
            obendFieldEquiv k a.2) = (0, 0) :=
          (towerPack_bijective (fpGen_not_mem_range_all k)).injective (by simpa [towerPack] using hzc)
        have ha2 : obendFieldEquiv k a.2 = 0 := congrArg Prod.snd hzp
        have ha1 : obendFieldEquiv k a.1 = 0 := by simpa [ha2] using congrArg Prod.fst hzp
        exact ha (by simp [obendFieldEquiv_pair, towerPack, ha1, ha2])
      have hprod := obendFieldEquiv_mul_conjugate k a
      have hnorm_ne : obendFieldEquiv k (towerNorm k a) ≠ 0 := fun hzn =>
        mul_ne_zero ha hconj_ne (by rw [hzn, map_zero] at hprod; exact hprod)
      apply eq_inv_of_mul_eq_one_right
      have hstep : obendFieldEquiv (k + 1) (towerInv (k + 1) a) =
          towerPack k (obendFieldEquiv k a.1 + towerMulCoeff k * obendFieldEquiv k a.2,
            obendFieldEquiv k a.2) *
            binaryTowerEmbed k (obendFieldEquiv k (towerNorm k a))⁻¹ := by
        simp only [towerInv, obendFieldEquiv_mk, obendFieldEquiv_mul, obendFieldEquiv_add,
          obendFieldEquiv_towerX, ih, towerPack, map_add, map_mul]
        ring
      rw [hstep, ← mul_assoc, hprod, ← map_mul, mul_inv_cancel₀ hnorm_ne, map_one]

/-- **Squaring & Iterated Frobenius isomorphisms**: `towerSq` and `towerFrob`. -/
theorem obendFieldEquiv_sq (k : Nat) (a : ObendTowerElem k) :
    obendFieldEquiv k (towerSq k a) = (obendFieldEquiv k a) ^ 2 := by
  rw [towerSq, obendFieldEquiv_mul, sq]

theorem obendFieldEquiv_frob (k n : Nat) (a : ObendTowerElem k) :
    obendFieldEquiv k (towerFrob k n a) = (obendFieldEquiv k a) ^ (2 ^ n) := by
  induction n with
  | zero => simp [towerFrob]
  | succ n ih => rw [towerFrob, obendFieldEquiv_sq, ih, ← pow_mul, ← pow_succ]

theorem towerFrob_add (k n : Nat) (a b : ObendTowerElem k) :
    towerFrob k n (towerAdd k a b) = towerAdd k (towerFrob k n a) (towerFrob k n b) := by
  apply (obendFieldEquiv k).injective
  rw [obendFieldEquiv_frob, obendFieldEquiv_add, obendFieldEquiv_add,
    obendFieldEquiv_frob, obendFieldEquiv_frob, add_pow_char_pow _ _ 2 n]

theorem towerFrob_mul (k n : Nat) (a b : ObendTowerElem k) :
    towerFrob k n (towerMul k a b) = towerMul k (towerFrob k n a) (towerFrob k n b) := by
  apply (obendFieldEquiv k).injective
  rw [obendFieldEquiv_frob, obendFieldEquiv_mul, obendFieldEquiv_mul,
    obendFieldEquiv_frob, obendFieldEquiv_frob, mul_pow]

theorem towerFrob_full_fixed (k : Nat) (a : ObendTowerElem k) :
    towerFrob k (2 ^ k) a = a := by
  apply (obendFieldEquiv k).injective
  rw [obendFieldEquiv_frob]
  exact binaryTower_pow_card k (obendFieldEquiv k a)

/-! ## §3. Exact Bit-Packing Identity (`packTower` = `coordinateFinEquiv`) -/

@[simp] theorem lowBits_join (k : Nat) (lo hi : TowerBitVec k) :
    lowBits k (joinBits k lo hi) = lo := by
  simp [lowBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]

@[simp] theorem highBits_join (k : Nat) (lo hi : TowerBitVec k) :
    highBits k (joinBits k lo hi) = hi := by
  simp [highBits, joinBits, BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_left]

@[simp] theorem joinBits_split (k : Nat) (a : TowerBitVec (k + 1)) :
    joinBits k (lowBits k a) (highBits k a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [joinBits, lowBits, highBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  split
  · simp_all [Nat.pow_succ, Nat.mul_two]
  · simp_all [Nat.pow_succ, Nat.mul_two]; omega

@[simp] theorem unpackTower_packTower (k : Nat) (a : ObendTowerElem k) :
    unpackTower k (packTower k a) = a := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => cases a; simp only [packTower, unpackTower, lowBits_join, highBits_join, ih]; rfl

@[simp] theorem packTower_unpackTower (k : Nat) (a : TowerBitVec k) :
    packTower k (unpackTower k a) = a := by
  induction k with
  | zero => exact (BitVec.setWidth_one (x := a)).symm.trans (BitVec.setWidth_eq _)
  | succ k ih => simp only [packTower, unpackTower, ih, joinBits_split]

theorem joinBits_xor (k : Nat) (a b c d : TowerBitVec k) :
    joinBits k (a ^^^ b) (c ^^^ d) = joinBits k a c ^^^ joinBits k b d := by
  simp [joinBits, BitVec.xor_append]

theorem packTower_add (k : Nat) (a b : ObendTowerElem k) :
    packTower k (towerAdd k a b) = packTower k a ^^^ packTower k b := by
  induction k with
  | zero => exact BitVec.ofBool_xor_ofBool.symm
  | succ k ih => simp only [packTower, towerAdd, ih, joinBits_xor]

theorem scaleXExec_refines (k : Nat) (a : ObendTowerElem k) :
    scaleXExec k (packTower k a) = packTower k (towerScaleX k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [scaleXExec, packTower, lowBits_join, highBits_join, ih, towerScaleX, packTower_add]

theorem mulExec_refines (k : Nat) (a b : ObendTowerElem k) :
    mulExec k (packTower k a) (packTower k b) = packTower k (towerMul k a b) := by
  induction k with
  | zero => exact BitVec.ofBool_and_ofBool
  | succ k ih =>
    simp only [mulExec, packTower, lowBits_join, highBits_join, ← packTower_add,
      ih, scaleXExec_refines]
    congr 1; congr 1
    apply (obendFieldEquiv k).injective
    have h2 : (2 : binaryTower k) = 0 := binaryTower_two_eq_zero k
    simp only [towerMul, obendFieldEquiv_add, obendFieldEquiv_mul,
      obendFieldEquiv_scaleX, obendFieldEquiv_towerX]
    linear_combination
      (obendFieldEquiv k a.1 * obendFieldEquiv k b.1 +
        obendFieldEquiv k a.2 * obendFieldEquiv k b.2) * h2

theorem invExec_refines (k : Nat) (a : ObendTowerElem k) :
    invExec k (packTower k a) = packTower k (towerInv k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hnorm :
        mulExec k (packTower k a.1) (packTower k a.1) ^^^
          scaleXExec k (mulExec k (packTower k a.1) (packTower k a.2)) ^^^
          mulExec k (packTower k a.2) (packTower k a.2) =
        packTower k (towerNorm k a) := by
      rw [mulExec_refines, mulExec_refines, mulExec_refines, scaleXExec_refines,
        ← packTower_add, ← packTower_add]
      congr 1; apply (obendFieldEquiv k).injective
      simp [towerNorm, obendFieldEquiv_add, obendFieldEquiv_mul,
        obendFieldEquiv_scaleX, obendFieldEquiv_towerX]
    have hconj :
        packTower k a.1 ^^^ scaleXExec k (packTower k a.2) =
        packTower k (towerAdd k a.1 (towerMul k (towerX k) a.2)) := by
      rw [scaleXExec_refines, ← packTower_add]
      congr 1; apply (obendFieldEquiv k).injective
      simp [obendFieldEquiv_add, obendFieldEquiv_mul,
        obendFieldEquiv_scaleX, obendFieldEquiv_towerX]
    simp only [invExec, packTower, lowBits_join, highBits_join]
    rw [hnorm, hconj, ih, mulExec_refines, mulExec_refines]; rfl

theorem joinBits_toNat (k : Nat) (lo hi : TowerBitVec k) :
    (joinBits k lo hi).toNat = lo.toNat + capacity k * hi.toNat := by
  have hcast : (joinBits k lo hi).toNat = (hi ++ lo).toNat := by simp [joinBits]
  rw [hcast, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt hi.toNat,
    Nat.shiftLeft_eq, capacity, Nat.add_comm, Nat.mul_comm]

/-- **Exact bit-packing identity at every level `k`**: Obend's `packTower` and Minidregg's
`coordinateFinEquiv` assign the exact same integer `< 2^(2^k)`. -/
theorem packTower_toNat_eq_coordinateFinEquiv (k : Nat) (a : ObendTowerElem k) :
    (packTower k a).toNat = (coordinateFinEquiv k (obendToCoord k a)).val := by
  induction k with
  | zero => cases a <;> rfl
  | succ k ih => simp only [packTower, joinBits_toNat, obendToCoord, coordinateFinEquiv_pair_val, ih]

theorem packTower8_toNat_eq_toFin (a : ObendTower256) :
    (packTower 8 a).toNat = (toFin (obendFieldEquiv 8 a)).val := by
  simpa [toFin, fieldFinEquiv, obendFieldEquiv, obendCoordEquiv] using
    packTower_toNat_eq_coordinateFinEquiv 8 a

theorem packTower8_fin_eq_toFin (a : ObendTower256) :
    (⟨(packTower 8 a).toNat, (packTower 8 a).isLt⟩ : Fin (2 ^ 256)) =
      toFin (obendFieldEquiv 8 a) :=
  Fin.ext (packTower8_toNat_eq_toFin a)

theorem unpackTower8_eq_ofFin (x : Fin (2 ^ 256)) :
    obendFieldEquiv 8 (unpackTower 8 (BitVec.ofNat 256 x.val)) = ofFin x := by
  apply (fieldFinEquiv 8).injective
  have h1 : fieldFinEquiv 8 (obendFieldEquiv 8 (unpackTower 8 (BitVec.ofNat 256 x.val))) =
      toFin (obendFieldEquiv 8 (unpackTower 8 (BitVec.ofNat 256 x.val))) := rfl
  rw [h1, ← packTower8_fin_eq_toFin, packTower_unpackTower]
  ext
  change (BitVec.ofNat 256 x.val).toNat = (toFin (ofFin x)).val
  rw [toFin_ofFin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-! ## §4. Pure 32-Byte Reversal Bijection (`List.reverse` / `i ↦ 31 - i`) & Wire Commutation -/

private theorem byteOfDigit_eq_ofNat (d : Nat) (hd : d < 256) :
    byteOfDigit ⟨d, hd⟩ = UInt8.ofNat d := by
  apply UInt8.toNat_inj.mp
  change d = d % 2 ^ 8
  exact (Nat.mod_eq_of_lt hd).symm

/-- **Core byte-order theorem**: Obend BE `obendBE w n` = `(digitsLE 256 w n).reverse`. -/
theorem obendBE_eq_reverse_digitsLE (w n : Nat) :
    obendBE w n =
      (bytesOfDigits (Bignum.digitsLE 256 w n)
        (fun d hd => Bignum.digitsLE_ranged (by norm_num) w n d hd)).reverse := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    have hmod : n % 256 < 256 := Nat.mod_lt n (by norm_num)
    simp only [obendBE, Bignum.digitsLE, bytesOfDigits, List.attach_cons, List.map_cons,
      List.reverse_cons]
    have htail :
        List.map (fun digit : { x // x ∈ n % 256 :: Bignum.digitsLE 256 w (n / 256) } =>
          byteOfDigit ⟨digit.1, Bignum.digitsLE_ranged (by norm_num) (w + 1) n digit.1 digit.2⟩)
          (List.map (fun x => ⟨x.1, List.mem_cons_of_mem _ x.2⟩)
            (Bignum.digitsLE 256 w (n / 256)).attach) =
        bytesOfDigits (Bignum.digitsLE 256 w (n / 256))
          (fun d hd => Bignum.digitsLE_ranged (by norm_num) w (n / 256) d hd) := by
      simp [bytesOfDigits, List.map_map, Function.comp]
    rw [htail, ← ih (n / 256), byteOfDigit_eq_ofNat (n % 256) hmod]

theorem obendToBytes32_eq_reverse_encodeFin (a : Tower256Exec) :
    obendToBytes32 a = (encodeFin ⟨a.toNat, a.isLt⟩).reverse :=
  obendBE_eq_reverse_digitsLE 32 a.toNat

/-- **Main Gate `G4` Serializer Bijection**: Obend BE 32B = `(Minidregg LE 32B).reverse`. -/
theorem obendToBytes32_eq_reverse_encode (a : ObendTower256) :
    obendToBytes32 (packTower 8 a) = (encode (obendFieldEquiv 8 a)).reverse := by
  rw [obendToBytes32_eq_reverse_encodeFin, packTower8_fin_eq_toFin, encode]

theorem encode_eq_reverse_obendToBytes32 (a : ObendTower256) :
    encode (obendFieldEquiv 8 a) = (obendToBytes32 (packTower 8 a)).reverse := by
  rw [obendToBytes32_eq_reverse_encode, List.reverse_reverse]

theorem obendBE_length (w n : Nat) : (obendBE w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [obendBE, ih]

/-- **Pointwise index characterization (`i ↦ 31 - i`)**: pure byte reversal, zero bit reflection. -/
theorem obendToBytes32_index_reversal (a : ObendTower256) (i : Fin 32) :
    (obendToBytes32 (packTower 8 a))[i.val]'(by
      rw [obendToBytes32, obendBE_length]; exact i.isLt) =
    (encode (obendFieldEquiv 8 a))[31 - i.val]'(by
      rw [encode, encodeFin_length]; omega) := by
  have hlen : (encode (obendFieldEquiv 8 a)).length = 32 := by rw [encode, encodeFin_length]
  have hrev := obendToBytes32_eq_reverse_encode a
  have hget := List.getElem_reverse (l := encode (obendFieldEquiv 8 a)) (i := i.val)
    (h := by rw [List.length_reverse, hlen]; exact i.isLt)
  have hidx : (encode (obendFieldEquiv 8 a)).length - 1 - i.val = 31 - i.val := by omega
  calc
    (obendToBytes32 (packTower 8 a))[i.val]'(by rw [obendToBytes32, obendBE_length]; exact i.isLt)
        = (encode (obendFieldEquiv 8 a)).reverse[i.val]'(by rw [List.length_reverse, hlen]; exact i.isLt) := by
          congr 1
    _ = (encode (obendFieldEquiv 8 a))[(encode (obendFieldEquiv 8 a)).length - 1 - i.val]'(by omega) := hget
    _ = (encode (obendFieldEquiv 8 a))[31 - i.val]'(by rw [hlen]; omega) := by congr 1

theorem obendOfBE_eq_denoteNat_reverse (bs : List UInt8) :
    obendOfBE bs = Bignum.denoteNat 256 (bs.reverse.map UInt8.toNat) := by
  suffices h : ∀ ys : List UInt8,
      obendOfBE ys.reverse = Bignum.denoteNat 256 (ys.map UInt8.toNat) by
    simpa only [List.reverse_reverse] using h bs.reverse
  intro ys
  induction ys with
  | nil => rfl
  | cons b ys ih =>
    rw [List.reverse_cons]
    simp only [obendOfBE, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_cons, Bignum.denoteNat_cons]
    change obendOfBE ys.reverse * 256 + b.toNat =
      b.toNat + 256 * Bignum.denoteNat 256 (ys.map UInt8.toNat)
    rw [ih]; ring

private theorem obendOfBE_lt (bs : List UInt8) : obendOfBE bs < 256 ^ bs.length := by
  rw [obendOfBE_eq_denoteNat_reverse]
  have hr : Bignum.Ranged 256 (bs.reverse.map UInt8.toNat) := by
    intro d hd; rcases List.mem_map.mp hd with ⟨b, _, rfl⟩; exact b.toNat_lt
  simpa using Bignum.denoteNat_lt_pow (bs.reverse.map UInt8.toNat) hr

/-- **Main Gate `G4` Deserializer Bijection**: Obend BE decode matches Minidregg `decode bs.reverse`. -/
theorem obendOfBytes32_eq_decode_reverse (bs : List UInt8) :
    (obendOfBytes32 bs).map (fun x => obendFieldEquiv 8 (unpackTower 8 x)) =
      decode bs.reverse := by
  unfold obendOfBytes32 decode decodeFin
  by_cases hlen : bs.length = 32
  · have hlenR : bs.reverse.length = 32 := by simpa using hlen
    have hlt : Bignum.denoteNat 256 (bs.reverse.map UInt8.toNat) < 2 ^ 256 := by
      have h1 := obendOfBE_lt bs
      rw [obendOfBE_eq_denoteNat_reverse, hlen, pow_256_32_eq] at h1; exact h1
    rw [ite_eq_left hlen, ite_eq_left hlenR, dite_eq_left hlt]
    simp only [Option.map_some, obendOfBE_eq_denoteNat_reverse]
    exact congrArg some (unpackTower8_eq_ofFin ⟨Bignum.denoteNat 256 (bs.reverse.map UInt8.toNat), hlt⟩)
  · have hlenR : bs.reverse.length ≠ 32 := by simpa using hlen
    rw [ite_eq_right hlen, ite_eq_right hlenR]; rfl

theorem decode_eq_obendOfBytes32_reverse (bs : List UInt8) :
    decode bs = (obendOfBytes32 bs.reverse).map (fun x => obendFieldEquiv 8 (unpackTower 8 x)) := by
  have h := (obendOfBytes32_eq_decode_reverse bs.reverse).symm
  rw [List.reverse_reverse] at h; exact h

theorem obendToBytes32LE_eq_encode (a : ObendTower256) :
    obendToBytes32LE (packTower 8 a) = encode (obendFieldEquiv 8 a) :=
  (encode_eq_reverse_obendToBytes32 a).symm

theorem obendOfBytes32LE_eq_decode (bs : List UInt8) :
    (obendOfBytes32LE bs).map (fun x => obendFieldEquiv 8 (unpackTower 8 x)) = decode bs := by
  rw [decode_eq_obendOfBytes32_reverse]
  congr 1; unfold obendOfBytes32LE obendOfBytes32; rw [List.length_reverse]

theorem obendToBytes32LEBA_size (a : Tower256Exec) : (obendToBytes32LEBA a).size = 32 := by
  change (obendBE 32 a.toNat).reverse.toArray.size = 32; simp [obendBE_length]

theorem obendOfBytes32LEBA_toBytes32LEBA (a : Tower256Exec) :
    obendOfBytes32LEBA (obendToBytes32LEBA a) = some a := by
  unfold obendOfBytes32LEBA
  rw [obendToBytes32LEBA_size, ite_eq_left rfl]
  change some (BitVec.ofNat 256 (obendOfBE (obendBE 32 a.toNat).reverse.toArray.toList.reverse)) = some a
  rw [List.toList_toArray, List.reverse_reverse, obendOfBE_eq_denoteNat_reverse,
    obendBE_eq_reverse_digitsLE, List.reverse_reverse, bytesOfDigits_toNats]
  have hlt : a.toNat < 256 ^ 32 := by rw [pow_256_32_eq]; exact a.isLt
  rw [Bignum.denoteNat_digitsLE (by norm_num) 32 a.toNat hlt]
  exact congrArg some ((BitVec.ofNat_toNat 256 a).trans (BitVec.setWidth_eq a))

/-! ### Rust `[u64; 4]` LE Limb Conformance (`bpe_bridge.rs:345-360` & `binary_tower_256.rs:166-181`) -/

def u64ToLEBytes (x : UInt64) : List UInt8 :=
  bytesOfDigits (Bignum.digitsLE 256 8 x.toNat)
    (fun d hd => Bignum.digitsLE_ranged (by norm_num) 8 x.toNat d hd)

def rustLimbsToLEBytes (l0 l1 l2 l3 : UInt64) : List UInt8 :=
  u64ToLEBytes l0 ++ u64ToLEBytes l1 ++ u64ToLEBytes l2 ++ u64ToLEBytes l3

def rustLimbsNat (l0 l1 l2 l3 : UInt64) : Nat :=
  l0.toNat + 2 ^ 64 * (l1.toNat + 2 ^ 64 * (l2.toNat + 2 ^ 64 * l3.toNat))

theorem rustLimbsNat_lt (l0 l1 l2 l3 : UInt64) : rustLimbsNat l0 l1 l2 l3 < 2 ^ 256 := by
  have h0 : l0.toNat < 2 ^ 64 := l0.toBitVec.isLt
  have h1 : l1.toNat < 2 ^ 64 := l1.toBitVec.isLt
  have h2 : l2.toNat < 2 ^ 64 := l2.toBitVec.isLt
  have h3 : l3.toNat < 2 ^ 64 := l3.toBitVec.isLt
  unfold rustLimbsNat; omega

private theorem digitsLE_append_chunk (w m n : Nat) :
    Bignum.digitsLE 256 (w + m) n =
      Bignum.digitsLE 256 w n ++ Bignum.digitsLE 256 m (n / 256 ^ w) := by
  induction w generalizing n with
  | zero => simp [Bignum.digitsLE]
  | succ w ih =>
    rw [Nat.succ_add, Bignum.digitsLE, Bignum.digitsLE, List.cons_append, ih (n / 256),
      Nat.div_div_eq_div_mul, pow_succ']

private theorem digitsLE_mod_eq (w a b : Nat) (ha : a < 256 ^ w) :
    Bignum.digitsLE 256 w (a + 256 ^ w * b) = Bignum.digitsLE 256 w a := by
  induction w generalizing a b with
  | zero => rfl
  | succ w ih =>
    have hpow : 256 ^ (w + 1) = 256 * 256 ^ w := by rw [pow_succ']
    have hmod : (a + 256 ^ (w + 1) * b) % 256 = a % 256 := by
      rw [hpow, mul_assoc, Nat.add_mul_mod_self_left]
    have hdiv : (a + 256 ^ (w + 1) * b) / 256 = a / 256 + 256 ^ w * b := by
      rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (by norm_num)]
    have ha' : a / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; simpa [pow_succ] using ha
    simp only [Bignum.digitsLE, hmod, hdiv, ih (a / 256) b ha']

private theorem rustLimbs_digitsLE (l0 l1 l2 l3 : UInt64) :
    Bignum.digitsLE 256 32 (rustLimbsNat l0 l1 l2 l3) =
      Bignum.digitsLE 256 8 l0.toNat ++ Bignum.digitsLE 256 8 l1.toNat ++
      Bignum.digitsLE 256 8 l2.toNat ++ Bignum.digitsLE 256 8 l3.toNat := by
  have hsplit : ∀ (x : UInt64) (r m : Nat),
      Bignum.digitsLE 256 (8 + m) (x.toNat + 2 ^ 64 * r) =
        Bignum.digitsLE 256 8 x.toNat ++ Bignum.digitsLE 256 m r := by
    intro x r m
    have hx : x.toNat < 256 ^ 8 := by rw [pow_256_8_eq]; exact x.toBitVec.isLt
    rw [digitsLE_append_chunk 8 m, ← pow_256_8_eq, digitsLE_mod_eq 8 x.toNat r hx,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]
  unfold rustLimbsNat
  rw [show (32 : Nat) = 8 + 24 from rfl, hsplit l0 _ 24,
      show (24 : Nat) = 8 + 16 from rfl, hsplit l1 _ 16,
      show (16 : Nat) = 8 + 8 from rfl, hsplit l2 _ 8]
  simp [List.append_assoc]

/-- **Rust `[u64; 4]` LE Limb Conformance (`bpe_bridge.rs:345-351`)**: matches `encodeFin`
and `(obendToBytes32 _).reverse` byte-for-byte. -/
theorem rustLimbsToLEBytes_eq_encodeFin (l0 l1 l2 l3 : UInt64) :
    rustLimbsToLEBytes l0 l1 l2 l3 =
      encodeFin ⟨rustLimbsNat l0 l1 l2 l3, rustLimbsNat_lt l0 l1 l2 l3⟩ := by
  apply List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h)
  simp only [rustLimbsToLEBytes, u64ToLEBytes, List.map_append, bytesOfDigits_toNats,
    encodeFin_toNats, rustLimbs_digitsLE]

theorem rustLimbsToLEBytes_eq_reverse_obendToBytes32 (l0 l1 l2 l3 : UInt64) :
    rustLimbsToLEBytes l0 l1 l2 l3 =
      (obendToBytes32 (BitVec.ofNat 256 (rustLimbsNat l0 l1 l2 l3))).reverse := by
  rw [rustLimbsToLEBytes_eq_encodeFin, obendToBytes32_eq_reverse_encodeFin, List.reverse_reverse]
  congr 1; apply Fin.ext
  change rustLimbsNat l0 l1 l2 l3 = (BitVec.ofNat 256 (rustLimbsNat l0 l1 l2 l3)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rustLimbsNat_lt l0 l1 l2 l3)]

/-! ### Wire-Level Ring, Inverse, and Frobenius Commutation Theorems -/

theorem wire_zero_commutes :
    (obendToBytes32 (packTower 8 (towerZero 8))).reverse = encode (0 : Tower256) := by
  rw [← obendFieldEquiv_zero 8, ← encode_eq_reverse_obendToBytes32]
theorem wire_one_commutes :
    (obendToBytes32 (packTower 8 (towerOne 8))).reverse = encode (1 : Tower256) := by
  rw [← obendFieldEquiv_one 8, ← encode_eq_reverse_obendToBytes32]
theorem wire_fpGen7_commutes :
    (obendToBytes32 (packTower 8 (towerX 8))).reverse = encode (fpGen 7) := by
  have h : obendFieldEquiv 8 (towerX 8) = fpGen 7 := obendFieldEquiv_towerX 8
  rw [← h, ← encode_eq_reverse_obendToBytes32]
theorem wire_add_commutes (a b : ObendTower256) :
    (obendToBytes32 (packTower 8 (towerAdd 8 a b))).reverse =
      encode (obendFieldEquiv 8 a + obendFieldEquiv 8 b) := by
  rw [← obendFieldEquiv_add 8 a b, ← encode_eq_reverse_obendToBytes32]
theorem wire_mul_commutes (a b : ObendTower256) :
    (obendToBytes32 (packTower 8 (towerMul 8 a b))).reverse =
      encode (obendFieldEquiv 8 a * obendFieldEquiv 8 b) := by
  rw [← obendFieldEquiv_mul 8 a b, ← encode_eq_reverse_obendToBytes32]
theorem wire_inv_commutes (a : ObendTower256) :
    (obendToBytes32 (packTower 8 (towerInv 8 a))).reverse = encode ((obendFieldEquiv 8 a)⁻¹) := by
  rw [← obendFieldEquiv_inv 8 a, ← encode_eq_reverse_obendToBytes32]
theorem wire_sq_commutes (a : ObendTower256) :
    (obendToBytes32 (packTower 8 (towerSq 8 a))).reverse = encode ((obendFieldEquiv 8 a) ^ 2) := by
  rw [← obendFieldEquiv_sq 8 a, ← encode_eq_reverse_obendToBytes32]
theorem wire_frob_commutes (n : Nat) (a : ObendTower256) :
    (obendToBytes32 (packTower 8 (towerFrob 8 n a))).reverse =
      encode ((obendFieldEquiv 8 a) ^ (2 ^ n)) := by
  rw [← obendFieldEquiv_frob 8 n a, ← encode_eq_reverse_obendToBytes32]

/-! ## §5. `#tooth` Falsifiers on Asymmetric Non-Palindromic Vectors & Golden Vectors -/

def vecRustSmokeA : Tower256Exec :=
  BitVec.ofNat 256 (rustLimbsNat
    0x0123456789abcdef 0xfedcba9876543210 0x0f0ff0f055aaaa55 0x8000000000000001)
def vecRustSmokeB : Tower256Exec :=
  BitVec.ofNat 256 (rustLimbsNat
    0xdeadbeefcafebabe 0x1122334455667788 0xaaaa5555ffff0000 0x0102030405060708)
def vecRamp : Tower256Exec :=
  BitVec.ofNat 256 0x201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201
def vecOne : Tower256Exec := BitVec.ofNat 256 1
def vecFpGen6 : Tower256Exec := BitVec.ofNat 256 (2 ^ 64)
def vecFpGen7 : Tower256Exec := BitVec.ofNat 256 (2 ^ 128)

def swapU64LimbsOnly (bs : List UInt8) : List UInt8 :=
  (bs.drop 24).take 8 ++ (bs.drop 16).take 8 ++ (bs.drop 8).take 8 ++ bs.take 8
def reverseWithinU64Limbs (bs : List UInt8) : List UInt8 :=
  (bs.take 8).reverse ++ ((bs.drop 8).take 8).reverse ++
  ((bs.drop 16).take 8).reverse ++ ((bs.drop 24).take 8).reverse
def swapTowerHalvesOnly (bs : List UInt8) : List UInt8 := bs.drop 16 ++ bs.take 16
def reverseWithinTowerHalves (bs : List UInt8) : List UInt8 :=
  (bs.take 16).reverse ++ (bs.drop 16).reverse
def reverseAllBits32 (bs : List UInt8) : List UInt8 :=
  bs.reverse.map (fun b => UInt8.ofBitVec b.toBitVec.reverse)

/-- **TOOTH 1–2**: Identity (`id`) fails — BE ≠ LE on `fpGen 7` and `vecRustSmokeA`. -/
theorem tooth_be_ne_le_on_fpGen7 :
    obendToBytes32 vecFpGen7 ≠ encodeFin ⟨vecFpGen7.toNat, vecFpGen7.isLt⟩ := by decide
theorem tooth_be_ne_le_on_asymmetric_vecA :
    obendToBytes32 vecRustSmokeA ≠ encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ := by decide

/-- **TOOTH 3**: 4×`u64` limb-only swap fails on `vecRustSmokeA` and `vecRamp`. -/
theorem tooth_swapU64LimbsOnly_fails :
    swapU64LimbsOnly (obendToBytes32 vecRustSmokeA) ≠
      encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ ∧
    swapU64LimbsOnly (obendToBytes32 vecRamp) ≠
      encodeFin ⟨vecRamp.toNat, vecRamp.isLt⟩ := by decide

/-- **TOOTH 4**: Within-`u64` byte reversal fails on `vecRustSmokeA` and `vecOne`. -/
theorem tooth_reverseWithinU64Limbs_fails :
    reverseWithinU64Limbs (obendToBytes32 vecRustSmokeA) ≠
      encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ ∧
    reverseWithinU64Limbs (obendToBytes32 vecOne) ≠
      encodeFin ⟨vecOne.toNat, vecOne.isLt⟩ := by decide

/-- **TOOTH 5**: 16B `T_7` half-swap fails on `vecRustSmokeA` and `vecFpGen7`. -/
theorem tooth_swapTowerHalvesOnly_fails :
    swapTowerHalvesOnly (obendToBytes32 vecRustSmokeA) ≠
      encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ ∧
    swapTowerHalvesOnly (obendToBytes32 vecFpGen7) ≠
      encodeFin ⟨vecFpGen7.toNat, vecFpGen7.isLt⟩ := by decide

/-- **TOOTH 6**: Within-`T_7`-half byte reversal fails on `vecRustSmokeA` and `vecFpGen7`. -/
theorem tooth_reverseWithinTowerHalves_fails :
    reverseWithinTowerHalves (obendToBytes32 vecRustSmokeA) ≠
      encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ ∧
    reverseWithinTowerHalves (obendToBytes32 vecFpGen7) ≠
      encodeFin ⟨vecFpGen7.toNat, vecFpGen7.isLt⟩ := by decide

/-- **TOOTH 7**: NIST-style bit-within-byte reflection fails on `vecOne` and `vecRustSmokeA`. -/
theorem tooth_bitReversedBytes_fails :
    reverseAllBits32 (obendToBytes32 vecOne) ≠ encodeFin ⟨vecOne.toNat, vecOne.isLt⟩ ∧
    reverseAllBits32 (obendToBytes32 vecRustSmokeA) ≠
      encodeFin ⟨vecRustSmokeA.toNat, vecRustSmokeA.isLt⟩ := by decide

/-- **TOOTH 8**: Missing byte reversal breaks `1² = 1` (Obend BE `1` read as LE is `2^248`). -/
theorem tooth_missing_reversal_breaks_one_idempotent :
    decodeFin (obendToBytes32 vecOne) = some ⟨2 ^ 248, by decide +kernel⟩ ∧
    mulExec 8 (BitVec.ofNat 256 (2 ^ 248)) (BitVec.ofNat 256 (2 ^ 248)) ≠
      BitVec.ofNat 256 (2 ^ 248) := by decide +kernel

/-- **TOOTH 9**: Missing byte reversal breaks `y_7² + y_6 y_7 + 1 = 0` (`2^120` is not a root). -/
theorem tooth_missing_reversal_breaks_fpGen7_quadratic :
    decodeFin (obendToBytes32 vecFpGen7) = some ⟨2 ^ 120, by decide +kernel⟩ ∧
    mulExec 8 (BitVec.ofNat 256 (2 ^ 120)) (BitVec.ofNat 256 (2 ^ 120)) ^^^
      mulExec 8 vecFpGen6 (BitVec.ofNat 256 (2 ^ 120)) ^^^ vecOne ≠ BitVec.ofNat 256 0 := by
  decide +kernel

/-- **TOOTH 10 (Coordinate basis is load-bearing)**: on identical LE byte `0x02`, AES poly basis
gives `0x02 * 0x02 = 0x04`, whereas Fan–Paar `T_3` gives `y_0² = y_0 + 1 = 0x03 ≠ 0x04`. -/
theorem tooth_wrong_basis_aes_gf256_breaks_mul :
    mulExec 3 (BitVec.ofNat 8 0x02) (BitVec.ofNat 8 0x02) = BitVec.ofNat 8 0x03 ∧
    mulExec 3 (BitVec.ofNat 8 0x02) (BitVec.ofNat 8 0x02) ≠ BitVec.ofNat 8 0x04 := by decide

/-- **TOOTH 11**: Non-canonical 31-byte and 33-byte payloads return `none` on both codecs. -/
theorem tooth_noncanonical_length_rejected :
    obendOfBytes32 (List.replicate 31 0) = none ∧ obendOfBytes32 (List.replicate 33 0) = none ∧
    decodeFin (List.replicate 31 0) = none ∧ decodeFin (List.replicate 33 0) = none := by decide

/-- Kernel-verified golden vector product `A * B`, inverse `A⁻¹`, `A * A⁻¹ = 1`, and
`y_7² = y_6 y_7 + 1` in `T_8`, matching `golden_vectors.json` byte-for-byte. -/
theorem golden_vecA_mul_vecB_and_inv :
    mulExec 8 vecRustSmokeA vecRustSmokeB =
      BitVec.ofNat 256 0xbc34b99b865dbfd3efc1d145035df65692d8d39380691deba31bf1bf79a7c6a5 ∧
    invExec 8 vecRustSmokeA =
      BitVec.ofNat 256 0xd58bdb96e156956ca475ac4208f6d502e1a95645c40069e0d358cf0ae52c7e4b ∧
    mulExec 8 vecRustSmokeA (invExec 8 vecRustSmokeA) = vecOne ∧
    mulExec 8 vecFpGen7 vecFpGen7 = (mulExec 8 vecFpGen6 vecFpGen7 ^^^ vecOne) := by
  decide +kernel

/-! ## §6. `#guard_msgs`-Pinned `#print axioms` -/

/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendRingEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendRingEquiv
/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendFieldEquiv_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendFieldEquiv_inv
/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendFieldEquiv_frob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendFieldEquiv_frob
/-- info: 'Minidregg.Theory.Tower256EndianBridge.packTower_toNat_eq_coordinateFinEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packTower_toNat_eq_coordinateFinEquiv
/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendToBytes32_eq_reverse_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendToBytes32_eq_reverse_encode
/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendToBytes32_index_reversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendToBytes32_index_reversal
/-- info: 'Minidregg.Theory.Tower256EndianBridge.obendOfBytes32_eq_decode_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms obendOfBytes32_eq_decode_reverse
/-- info: 'Minidregg.Theory.Tower256EndianBridge.rustLimbsToLEBytes_eq_encodeFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rustLimbsToLEBytes_eq_encodeFin
/-- info: 'Minidregg.Theory.Tower256EndianBridge.wire_mul_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wire_mul_commutes
/-- info: 'Minidregg.Theory.Tower256EndianBridge.wire_inv_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wire_inv_commutes
/-- info: 'Minidregg.Theory.Tower256EndianBridge.wire_frob_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wire_frob_commutes
/-- info: 'Minidregg.Theory.Tower256EndianBridge.tooth_swapU64LimbsOnly_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_swapU64LimbsOnly_fails
/-- info: 'Minidregg.Theory.Tower256EndianBridge.tooth_missing_reversal_breaks_fpGen7_quadratic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_missing_reversal_breaks_fpGen7_quadratic
/-- info: 'Minidregg.Theory.Tower256EndianBridge.golden_vecA_mul_vecB_and_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms golden_vecA_mul_vecB_and_inv

end Minidregg.Theory.Tower256EndianBridge
