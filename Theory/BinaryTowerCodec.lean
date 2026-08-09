/-
# Theory.BinaryTowerCodec -- exact 32-byte codec for the abstract GF(2^256)

The codec uses the finite carrier's canonical Lean enumeration and fixed-width
base-256 digits.  It is injective and round-trips in Lean and therefore can
instantiate a semantic Tower256 profile.  It intentionally does not claim the
enumeration is Rust's four-little-endian-u64 Fan--Paar representation; that
separate representation equality must be generated and checked explicitly.
-/

import Theory.BinaryTower
import Theory.Bignum
import Theory.IndexedProgram

namespace Minidregg.Theory.BinaryTowerCodec

open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

abbrev Tower256 := binaryTower 8

noncomputable local instance tower256Fintype : Fintype Tower256 :=
  Fintype.ofFinite Tower256

theorem tower256_fintype_card : Fintype.card Tower256 = 2 ^ 256 := by
  rw [← Nat.card_eq_fintype_card, binaryTower_card]
  norm_num

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
  Fin.cast tower256_fintype_card
    (Fintype.equivFin Tower256 value)

noncomputable def ofFin (value : Fin (2 ^ 256)) : Tower256 :=
  (Fintype.equivFin Tower256).symm
    (Fin.cast tower256_fintype_card.symm value)

@[simp] theorem ofFin_toFin (value : Tower256) : ofFin (toFin value) = value := by
  simp [ofFin, toFin]

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

theorem encode_length (value : Tower256) : (codec.encode value).length = 32 := by
  simp [codec, encode]

theorem encode_injective : Function.Injective codec.encode := by
  exact fun left right equal => by
    have decoded := congrArg codec.decode equal
    simpa [codec.decode_encode] using decoded

theorem cardinality : Nat.card Tower256 = 2 ^ 256 := by
  simpa [Tower256] using binaryTower_card 8

theorem characteristic : CharP Tower256 2 :=
  binaryTower_char_two 8

#print axioms decode_encode
#print axioms encode_injective
#print axioms cardinality

end Minidregg.Theory.BinaryTowerCodec
