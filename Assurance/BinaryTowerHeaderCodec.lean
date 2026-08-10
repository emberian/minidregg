/-
# Assurance.BinaryTowerHeaderCodec -- exact 32-byte binding cells in GF(2^256)

This is the concrete characteristic-two instance required by
`DeclaredHyperedgeHistoryBinding`.  Each adjacent byte pair is the existing
little-endian u16 cell, mapped bijectively into `binaryTower 4 = GF(2^16)`,
then embedded into `binaryTower 8 = GF(2^256)` through the proved tower chain.

It is a Lean mathematical codec.  It does not identify this value with the
four-u64 Rust representation; that remains a generated representation/ABI
obligation for opaque native compute.
-/

import Assurance.DeclaredHyperedgeHistoryBinding
import Theory.BinaryTower

namespace Minidregg.Assurance.BinaryTowerHeaderCodec

open Minidregg.Theory
open Minidregg.Compiler.NextgenLightClientPublicInputs
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.DeclaredHyperedgeHistoryBinding

set_option autoImplicit false

abbrev Tower256 := binaryTower 8

noncomputable local instance tower4Fintype : Fintype (binaryTower 4) :=
  Fintype.ofFinite (binaryTower 4)

theorem tower4_card : Fintype.card (binaryTower 4) = 2 ^ 16 := by
  rw [← Nat.card_eq_fintype_card, binaryTower_card]
  norm_num

noncomputable def u16ToTower4 (value : Fin (2 ^ 16)) : binaryTower 4 :=
  (Fintype.equivFin (binaryTower 4)).symm
    ⟨value.val, by simpa [tower4_card] using value.isLt⟩

theorem u16ToTower4_injective : Function.Injective u16ToTower4 := by
  intro left right equal
  apply Fin.ext
  have mapped := congrArg (Fintype.equivFin (binaryTower 4)) equal
  simpa [u16ToTower4] using congrArg Fin.val mapped

def packedNat (bytes : HeaderBytes.FixedBytes32) (index : BindingIx) : Nat :=
  (HeaderBytes.bindingNatCells bytes).1.get
    ⟨index.val, by simpa [(HeaderBytes.bindingNatCells bytes).2] using index.isLt⟩

theorem packedNat_lt (bytes : HeaderBytes.FixedBytes32) (index : BindingIx) :
    packedNat bytes index < 2 ^ 16 := by
  have member : packedNat bytes index ∈
      (HeaderBytes.bindingNatCells bytes).1 := by
    exact List.get_mem _ _
  simpa [u16Base] using HeaderBytes.bindingNatCells_ranged bytes
    (packedNat bytes index) member

def packedFin (bytes : HeaderBytes.FixedBytes32) (index : BindingIx) :
    Fin (2 ^ 16) :=
  ⟨packedNat bytes index, packedNat_lt bytes index⟩

noncomputable def encodeCell
    (bytes : HeaderBytes.FixedBytes32) (index : BindingIx) : Tower256 :=
  binaryTowerEmbedChain 4 4 (u16ToTower4 (packedFin bytes index))

theorem encodeCell_injective : Function.Injective encodeCell := by
  intro left right equal
  apply HeaderBytes.bindingNatCells_injective
  apply Subtype.ext
  apply List.ext_get
  · exact (HeaderBytes.bindingNatCells left).2.trans
      (HeaderBytes.bindingNatCells right).2.symm
  · intro n leftBound rightBound
    let index : BindingIx := ⟨n, by
      simpa [(HeaderBytes.bindingNatCells left).2] using leftBound⟩
    have cellEqual := congrFun equal index
    have tower4Equal : u16ToTower4 (packedFin left index) =
        u16ToTower4 (packedFin right index) :=
      binaryTowerEmbedChain_injective 4 4 cellEqual
    have finEqual : packedFin left index = packedFin right index :=
      u16ToTower4_injective tower4Equal
    exact congrArg Fin.val finEqual

/-- Concrete injective binary-tower header cell codec. -/
noncomputable def codec : HeaderCellCodec Tower256 where
  encode := encodeCell
  injective := encodeCell_injective

theorem codec_is_injective : Function.Injective codec.encode :=
  codec.injective

theorem tower256_card : Nat.card Tower256 = 2 ^ 256 := by
  simpa [Tower256] using binaryTower_card 8

theorem tower256_char_two : CharP Tower256 2 :=
  binaryTower_char_two 8

/-- info: 'Minidregg.Assurance.BinaryTowerHeaderCodec.encodeCell_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeCell_injective
/-- info: 'Minidregg.Assurance.BinaryTowerHeaderCodec.codec_is_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms codec_is_injective
/-- info: 'Minidregg.Assurance.BinaryTowerHeaderCodec.tower256_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tower256_card

end Minidregg.Assurance.BinaryTowerHeaderCodec
