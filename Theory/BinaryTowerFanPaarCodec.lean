/-
# Theory.BinaryTowerFanPaarCodec -- canonical recursive coordinates for GF(2^256)

This is the representation promised by the Tower256 manifest: recursively,
`T_(k+1)` is encoded as `(low, high)` with value

`embed low + embed high * fpGen k`.

The low coordinate occupies the low half of the little-endian bit string.  At
level eight this gives exactly 256 bits / 32 bytes, and `fpGen 7` occupies bit
128.  Unlike a generic `Fintype.equivFin`, this codec is induced by the proved
Fan--Paar basis at every level.

This is still a Lean mathematical representation.  It does not prove that a
handwritten native four-u64 routine implements the same operations; opaque
native replies must be decoded and checked against this representation.
-/

import Theory.BinaryTowerTrace
import Theory.Bignum
import Theory.IndexedProgram
import Mathlib.Logic.Equiv.Fin.Basic

namespace Minidregg.Theory.BinaryTowerFanPaarCodec

open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

abbrev Tower256 := binaryTower 8

/-! ## Recursive coordinate carrier -/

/-- Recursive little-endian Fan--Paar coordinates.  The first child is the
constant/low coordinate and the second child multiplies `fpGen k`. -/
inductive Coordinate : Nat -> Type
  | bit : Bool -> Coordinate 0
  | pair : {k : Nat} -> Coordinate k -> Coordinate k -> Coordinate (k + 1)
  deriving DecidableEq, Repr

namespace Coordinate

/-- Expose one recursive level as its ordered low/high pair. -/
def pairEquiv (k : Nat) : Coordinate (k + 1) ≃ Coordinate k × Coordinate k where
  toFun := fun coordinate => match coordinate with
    | .pair low high => (low, high)
  invFun := fun pair => .pair pair.1 pair.2
  left_inv := by intro coordinate; cases coordinate; rfl
  right_inv := by intro pair; cases pair; rfl

/-- The base coordinate is literally one Boolean bit. -/
def bitEquiv : Coordinate 0 ≃ Bool where
  toFun := fun coordinate => match coordinate with
    | .bit value => value
  invFun := .bit
  left_inv := by intro coordinate; cases coordinate; rfl
  right_inv := by intro; rfl

/-- All-zero recursive coordinate. -/
def zero : (k : Nat) -> Coordinate k
  | 0 => .bit false
  | k + 1 => .pair (zero k) (zero k)

/-- Multiplicative-one coordinate: one in the low branch, zero in the high. -/
def one : (k : Nat) -> Coordinate k
  | 0 => .bit true
  | k + 1 => .pair (one k) (zero k)

/-- Coordinate of the generator introduced at this recursive level. -/
def topGenerator (k : Nat) : Coordinate (k + 1) :=
  .pair (zero k) (one k)

end Coordinate

/-! ## Exact recursive equivalence to Lean's field -/

/-- The base field coordinate: false ↦ 0, true ↦ 1. -/
noncomputable def baseFieldEquiv : Coordinate 0 ≃ binaryTower 0 := by
  classical
  refine
    { toFun := fun coordinate => match coordinate with
        | .bit false => 0
        | .bit true => 1
      invFun := fun value => if value = 0 then .bit false else .bit true
      left_inv := ?_
      right_inv := ?_ }
  · intro coordinate
    cases coordinate with
    | bit value => cases value <;> simp
  · intro value
    rcases binaryTower_zero_eq_zero_or_one value with equal | equal
    · subst value
      simp
    · subst value
      simp

/-- The canonical recursive Fan--Paar coordinate equivalence. -/
noncomputable def coordinateFieldEquiv :
    (k : Nat) -> Coordinate k ≃ binaryTower k
  | 0 => baseFieldEquiv
  | k + 1 =>
      (Coordinate.pairEquiv k).trans <|
        (Equiv.prodCongr (coordinateFieldEquiv k)
          (coordinateFieldEquiv k)).trans <|
            Equiv.ofBijective (towerPack k)
              (towerPack_bijective (fpGen_not_mem_range_all k))

@[simp] theorem coordinateFieldEquiv_pair
    {k : Nat} (low high : Coordinate k) :
    coordinateFieldEquiv (k + 1) (.pair low high) =
      towerPack k
        (coordinateFieldEquiv k low, coordinateFieldEquiv k high) :=
  rfl

@[simp] theorem coordinateFieldEquiv_zero (k : Nat) :
    coordinateFieldEquiv k (Coordinate.zero k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Coordinate.zero, coordinateFieldEquiv_pair, ih]
      simp [towerPack]

@[simp] theorem coordinateFieldEquiv_one (k : Nat) :
    coordinateFieldEquiv k (Coordinate.one k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Coordinate.one, coordinateFieldEquiv_pair, ih,
        coordinateFieldEquiv_zero]
      simp [towerPack]

@[simp] theorem coordinateFieldEquiv_topGenerator (k : Nat) :
    coordinateFieldEquiv (k + 1) (Coordinate.topGenerator k) = fpGen k := by
  simp [Coordinate.topGenerator, towerPack]

@[simp] theorem coordinateFieldEquiv_symm_zero (k : Nat) :
    (coordinateFieldEquiv k).symm 0 = Coordinate.zero k := by
  apply (coordinateFieldEquiv k).injective
  simp

@[simp] theorem coordinateFieldEquiv_symm_one (k : Nat) :
    (coordinateFieldEquiv k).symm 1 = Coordinate.one k := by
  apply (coordinateFieldEquiv k).injective
  simp

@[simp] theorem coordinateFieldEquiv_symm_topGenerator (k : Nat) :
    (coordinateFieldEquiv (k + 1)).symm (fpGen k) =
      Coordinate.topGenerator k := by
  apply (coordinateFieldEquiv (k + 1)).injective
  simp

/-! ## Exact little-endian finite index -/

/-- Number of coordinate strings at level `k`. -/
def capacity (k : Nat) : Nat := 2 ^ (2 ^ k)

@[simp] theorem capacity_zero : capacity 0 = 2 := by
  norm_num [capacity]

theorem capacity_succ (k : Nat) :
    capacity k * capacity k = capacity (k + 1) := by
  calc
    capacity k * capacity k = 2 ^ (2 ^ k + 2 ^ k) := by
      simp only [capacity, pow_add]
    _ = 2 ^ (2 ^ k * 2) := by rw [Nat.mul_two]
    _ = capacity (k + 1) := by rw [capacity, pow_succ]

/-- Recursive coordinates as a finite little-endian integer.  The explicit
product swap is load-bearing: `finProdFinEquiv` places its second component in
the low radix digit, so we feed it `(high, low)`. -/
noncomputable def coordinateFinEquiv :
    (k : Nat) -> Coordinate k ≃ Fin (capacity k)
  | 0 => Coordinate.bitEquiv.trans <|
      finTwoEquiv.symm.trans (finCongr capacity_zero.symm)
  | k + 1 =>
      (Coordinate.pairEquiv k).trans <|
        (Equiv.prodCongr (coordinateFinEquiv k)
          (coordinateFinEquiv k)).trans <|
            Equiv.prodComm _ _ |>.trans <|
              finProdFinEquiv.trans (finCongr (capacity_succ k))

@[simp] theorem coordinateFinEquiv_pair_val
    {k : Nat} (low high : Coordinate k) :
    (coordinateFinEquiv (k + 1) (.pair low high)).val =
      (coordinateFinEquiv k low).val +
        capacity k * (coordinateFinEquiv k high).val :=
  rfl

@[simp] theorem coordinateFinEquiv_zero_val (k : Nat) :
    (coordinateFinEquiv k (Coordinate.zero k)).val = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Coordinate.zero, coordinateFinEquiv_pair_val, ih]

@[simp] theorem coordinateFinEquiv_one_val (k : Nat) :
    (coordinateFinEquiv k (Coordinate.one k)).val = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [Coordinate.one, coordinateFinEquiv_pair_val, ih,
        coordinateFinEquiv_zero_val]

@[simp] theorem coordinateFinEquiv_topGenerator_val (k : Nat) :
    (coordinateFinEquiv (k + 1) (Coordinate.topGenerator k)).val = capacity k := by
  simp [Coordinate.topGenerator, coordinateFinEquiv_pair_val]

/-- The field-to-index map is induced by the same recursive basis. -/
noncomputable def fieldFinEquiv (k : Nat) :
    binaryTower k ≃ Fin (capacity k) :=
  (coordinateFieldEquiv k).symm.trans (coordinateFinEquiv k)

@[simp] theorem fieldFinEquiv_topGenerator_val (k : Nat) :
    (fieldFinEquiv (k + 1) (fpGen k)).val = capacity k := by
  rw [← coordinateFieldEquiv_topGenerator k]
  simp [fieldFinEquiv]

/-! ## Exact 32-byte codec -/

def byteOfDigit (digit : { value : Nat // value < 256 }) : UInt8 :=
  UInt8.ofNatLT digit.1 (by simpa [UInt8.size] using digit.2)

def bytesOfDigits (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) : List UInt8 :=
  digits.attach.map fun digit =>
    byteOfDigit ⟨digit.1, ranged digit.1 digit.2⟩

@[simp] theorem bytesOfDigits_length (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) :
    (bytesOfDigits digits ranged).length = digits.length := by
  simp [bytesOfDigits]

@[simp] theorem bytesOfDigits_toNats (digits : List Nat)
    (ranged : ∀ digit ∈ digits, digit < 256) :
    (bytesOfDigits digits ranged).map UInt8.toNat = digits := by
  simp [bytesOfDigits, byteOfDigit]

def encodeFin (value : Fin (2 ^ 256)) : List UInt8 :=
  bytesOfDigits (Bignum.digitsLE 256 32 value.val)
    (Bignum.digitsLE_ranged (by norm_num) 32 value.val)

@[simp] theorem encodeFin_length (value : Fin (2 ^ 256)) :
    (encodeFin value).length = 32 := by
  simp [encodeFin, Bignum.digitsLE_length]

@[simp] theorem encodeFin_toNats (value : Fin (2 ^ 256)) :
    (encodeFin value).map UInt8.toNat =
      Bignum.digitsLE 256 32 value.val := by
  simp [encodeFin]

def decodeFin (bytes : List UInt8) : Option (Fin (2 ^ 256)) :=
  if bytes.length = 32 then
    let value := Bignum.denoteNat 256 (bytes.map UInt8.toNat)
    if bounded : value < 2 ^ 256 then some ⟨value, bounded⟩ else none
  else none

@[simp] theorem decodeFin_encodeFin (value : Fin (2 ^ 256)) :
    decodeFin (encodeFin value) = some value := by
  have denoted : Bignum.denoteNat 256
      (Bignum.digitsLE 256 32 value.val) = value.val :=
    Bignum.denoteNat_digitsLE (by norm_num) 32 value.val value.isLt
  simp [decodeFin, encodeFin_length, encodeFin_toNats, denoted]

noncomputable def toFin (value : Tower256) : Fin (2 ^ 256) :=
  fieldFinEquiv 8 value

noncomputable def ofFin (value : Fin (2 ^ 256)) : Tower256 :=
  (fieldFinEquiv 8).symm value

@[simp] theorem ofFin_toFin (value : Tower256) :
    ofFin (toFin value) = value := by
  simp [ofFin, toFin]

@[simp] theorem toFin_ofFin (value : Fin (2 ^ 256)) :
    toFin (ofFin value) = value := by
  simp [ofFin, toFin]

/-- Basis tooth: zero occupies the all-zero 256-bit coordinate. -/
theorem toFin_zero : (toFin (0 : Tower256)).val = 0 := by
  rw [← coordinateFieldEquiv_zero 8]
  simp [toFin, fieldFinEquiv]

/-- Basis tooth: one occupies the least-significant coordinate bit. -/
theorem toFin_one : (toFin (1 : Tower256)).val = 1 := by
  rw [← coordinateFieldEquiv_one 8]
  simp [toFin, fieldFinEquiv]

/-- Basis tooth: the top recursive generator `fpGen 7` is bit 128, matching
the low/high `T₇ × T₇` split rather than an arbitrary enumeration. -/
theorem toFin_fpGen_seven : (toFin (fpGen 7)).val = 2 ^ 128 := by
  change (fieldFinEquiv (7 + 1) (fpGen 7)).val = 2 ^ 128
  rw [fieldFinEquiv_topGenerator_val]
  rfl

noncomputable def encode (value : Tower256) : List UInt8 :=
  encodeFin (toFin value)

noncomputable def decode (bytes : List UInt8) : Option Tower256 :=
  (decodeFin bytes).map ofFin

@[simp] theorem decode_encode (value : Tower256) :
    decode (encode value) = some value := by
  simp [decode, encode]

noncomputable def codec : LawfulCodec Tower256 where
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_length (value : Tower256) :
    (codec.encode value).length = 32 := by
  simp [codec, encode]

theorem encode_injective : Function.Injective codec.encode := by
  exact fun left right equal => by
    have decoded := congrArg codec.decode equal
    simpa [codec.decode_encode] using decoded

theorem cardinality : Nat.card Tower256 = 2 ^ 256 := by
  simpa [Tower256] using binaryTower_card 8

theorem characteristic : CharP Tower256 2 :=
  binaryTower_char_two 8

#print axioms coordinateFieldEquiv
#print axioms decode_encode
#print axioms encode_injective

end Minidregg.Theory.BinaryTowerFanPaarCodec
