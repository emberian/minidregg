/-
# Theory.BinaryTowerCodec -- compatibility name for the canonical Fan--Paar codec

The former implementation used `Fintype.equivFin`, which gave an exact
32-byte bijection but did not justify the manifest's recursive-basis claim.
The authoritative implementation now lives in
`Theory.BinaryTowerFanPaarCodec` and is induced level-by-level by the proved
Fan--Paar packing.  This namespace re-exports that surface without retaining
the arbitrary enumeration.
-/

import Theory.BinaryTowerFanPaarCodec

namespace Minidregg.Theory.BinaryTowerCodec

open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

abbrev Tower256 := BinaryTowerFanPaarCodec.Tower256
abbrev Coordinate := BinaryTowerFanPaarCodec.Coordinate

noncomputable abbrev coordinateFieldEquiv :=
  BinaryTowerFanPaarCodec.coordinateFieldEquiv
noncomputable abbrev coordinateFinEquiv :=
  BinaryTowerFanPaarCodec.coordinateFinEquiv
noncomputable abbrev fieldFinEquiv := BinaryTowerFanPaarCodec.fieldFinEquiv

abbrev encodeFin := BinaryTowerFanPaarCodec.encodeFin
abbrev decodeFin := BinaryTowerFanPaarCodec.decodeFin
noncomputable abbrev toFin := BinaryTowerFanPaarCodec.toFin
noncomputable abbrev ofFin := BinaryTowerFanPaarCodec.ofFin
noncomputable abbrev encode := BinaryTowerFanPaarCodec.encode
noncomputable abbrev decode := BinaryTowerFanPaarCodec.decode
noncomputable abbrev codec := BinaryTowerFanPaarCodec.codec

theorem decode_encode (value : Tower256) :
    decode (encode value) = some value :=
  BinaryTowerFanPaarCodec.decode_encode value

theorem encode_length (value : Tower256) :
    (codec.encode value).length = 32 :=
  BinaryTowerFanPaarCodec.encode_length value

theorem encode_injective : Function.Injective codec.encode :=
  BinaryTowerFanPaarCodec.encode_injective

theorem cardinality : Nat.card Tower256 = 2 ^ 256 :=
  BinaryTowerFanPaarCodec.cardinality

theorem characteristic : CharP Tower256 2 :=
  BinaryTowerFanPaarCodec.characteristic

theorem toFin_zero : (toFin (0 : Tower256)).val = 0 :=
  BinaryTowerFanPaarCodec.toFin_zero

theorem toFin_one : (toFin (1 : Tower256)).val = 1 :=
  BinaryTowerFanPaarCodec.toFin_one

theorem toFin_fpGen_seven :
    (toFin (Minidregg.Theory.fpGen 7)).val = 2 ^ 128 :=
  BinaryTowerFanPaarCodec.toFin_fpGen_seven

end Minidregg.Theory.BinaryTowerCodec
