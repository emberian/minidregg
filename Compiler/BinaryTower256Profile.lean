/-
# Compiler.BinaryTower256Profile -- inhabited semantic Tower256 backend profile

This instantiates the controller's abstract Tower256 profile with Lean's
`binaryTower 8` and the exact 32-byte finite-carrier codec.  It closes profile
inhabitation and the characteristic/cardinality/width obligations.  It still
does not identify that codec with a native four-u64 layout.
-/

import Theory.BinaryTowerCodec
import Compiler.Tower256CshakeMerkleController
import Compiler.MinidreggV1Artifact

namespace Minidregg.Compiler.BinaryTower256Profile

open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController

set_option autoImplicit false

abbrev Tower256 := Minidregg.Theory.BinaryTowerCodec.Tower256

noncomputable def profile : Tower256Profile Tower256 where
  carrier := MinidreggV1Artifact.gf2Tower256Carrier
  profileId := MinidreggV1Artifact.id 205
  towerId := MinidreggV1Artifact.fanPaarTowerId
  basisId := MinidreggV1Artifact.fanPaarRecursiveBasisId
  representationId := MinidreggV1Artifact.tower256ValueCodec.codecId
  carrierExact := rfl
  characteristic := Minidregg.Theory.BinaryTowerCodec.characteristic
  cardinality := Minidregg.Theory.BinaryTowerCodec.cardinality
  valueCodecPin := MinidreggV1Artifact.tower256ValueCodec
  valueCodec := Minidregg.Theory.BinaryTowerCodec.codec
  valueWidthExact := Minidregg.Theory.BinaryTowerCodec.encode_length

theorem profile_carrier_exact :
    profile.carrier = MinidreggV1Artifact.gf2Tower256Carrier := rfl

theorem profile_codec_exact :
    profile.valueCodec = Minidregg.Theory.BinaryTowerCodec.codec := rfl

theorem profile_width_exact (value : Tower256) :
    (profile.valueCodec.encode value).length = 32 :=
  profile.valueWidthExact value

theorem profile_cardinality : Nat.card Tower256 = 2 ^ 256 :=
  profile.cardinality

#print axioms profile_width_exact
#print axioms profile_cardinality

end Minidregg.Compiler.BinaryTower256Profile
