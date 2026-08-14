/-
# Assurance.Tower256MerkleCardinalityCore -- the binding-closed PCS is empty

`Tower256AdditiveFriController.MerklePcs` asks the concrete cSHAKE256 Merkle
commitment to be *unconditionally* position binding.  Completeness plus position
binding makes the whole-word commitment injective.  But every concrete Merkle
root is a 256-bit cSHAKE digest, while a positive-height Tower256 column has
strictly more than `2 ^ 256` possible words.  Pigeonhole therefore refutes the
carrier itself: `MerklePcs ell` is EMPTY for every `0 < ell`.

This module holds only that cardinality argument, and it sits directly above
`Compiler.Tower256AdditiveFriController` **so that every module quantified over
`MerklePcs` can import it and carry its own machine-checked retraction.**  The
argument used to live in `Assurance.Tower256MerkleBindingCardinality`, which
also imports the semantic-history checkpoint game and is therefore *downstream*
of the admission modules it refutes — the refutation could not be stated in the
files that needed it.  `Tower256MerkleBindingCardinality` now imports this file
and keeps the `JointGameFamily` consequence.

⚑ What this does NOT say: nothing here rules out `MerklePcs 0`.  At height zero
the level-zero word space is a single `Tower256` element, exactly `2 ^ 256`
words against `2 ^ 256` roots, so the pigeonhole has no room to fire.  A
height-zero additive FRI performs no folds; no witness has ever been built for
it either (the carrier census reports `MerklePcs` unwitnessed).  So a theorem
quantified over `MerklePcs ell` is VACUOUS at every positive height and
UNWITNESSED at height zero.
-/

import Compiler.Sp800185Cshake256
import Compiler.Tower256AdditiveFriController

namespace Minidregg.Assurance.Tower256MerkleCardinalityCore

open Minidregg.Compiler
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Selvage
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

abbrev TowerField := Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : Fintype TowerField := Fintype.ofFinite _
local instance : DecidableEq TowerField := Classical.decEq _

/-- Every use of the PCS backend's cSHAKE function lands in the literal
256-bit range fixed by the selected controller. -/
theorem xofDigest_value_lt {ell : Nat} (pcs : MerklePcs ell)
    (customization input : List UInt8) :
    (pcs.backend.cshake.xofDigest customization input).value < 2 ^ 256 := by
  rw [pcs.cshakeExact, controller_xofDigest]
  exact hash_digest_lt_two_pow_256 customization input

/-- A perfect-tree root is one outer cSHAKE call, whether it is a leaf or an
internal node, so its range is also strictly below `2 ^ 256`. -/
theorem cubeRoot_value_lt {ell : Nat} (pcs : MerklePcs ell)
    {Representation : Type}
    (codec : Minidregg.Theory.IndexedProgram.LawfulCodec Representation)
    {k : Nat} (column : (Fin k → Bool) → Representation) :
    (cubeRoot pcs.backend.merkle codec column).value < 2 ^ 256 := by
  cases k with
  | zero =>
      change (pcs.backend.cshake.xofDigest _ _).value < 2 ^ 256
      exact xofDigest_value_lt pcs _ _
  | succ k =>
      change (pcs.backend.cshake.xofDigest _ _).value < 2 ^ 256
      exact xofDigest_value_lt pcs _ _

/-- In particular, every level-zero concrete PCS commitment is a 256-bit
root. -/
theorem finiteCommitment_value_lt {ell : Nat} (pcs : MerklePcs ell)
    (word : PowerTwoFriLevels ell 0 → TowerField) :
    ((pcs.finiteCommitment 0).commit word).value < 2 ^ 256 := by
  change (cubeRoot pcs.backend.merkle
    (pcs.level 0).port.representationCodec
    (fun address => word (binaryCubeIndexEquiv (ell - 0) address))).value <
      2 ^ 256
  exact cubeRoot_value_lt pcs _ _

/-- Binding would embed every level-zero word into `Fin (2 ^ 256)`. -/
def rootFin {ell : Nat} (pcs : MerklePcs ell)
    (word : PowerTwoFriLevels ell 0 → TowerField) : Fin (2 ^ 256) :=
  ⟨((pcs.finiteCommitment 0).commit word).value,
    finiteCommitment_value_lt pcs word⟩

theorem rootFin_injective {ell : Nat} (pcs : MerklePcs ell) :
    Function.Injective (rootFin pcs) := by
  intro left right rootsEqual
  apply (pcs.finiteCommitment 0).commit_injective
  have valuesEqual := congrArg Fin.val rootsEqual
  simp only [rootFin] at valuesEqual
  cases leftRoot : (pcs.finiteCommitment 0).commit left
  cases rightRoot : (pcs.finiteCommitment 0).commit right
  simp only [leftRoot, rightRoot] at valuesEqual ⊢
  simpa only [Digest.mk.injEq] using valuesEqual

/-- The finite word-space cardinal forced by a hypothetical binding PCS is at
most the number of 256-bit roots. -/
theorem word_card_le_root_card {ell : Nat} (pcs : MerklePcs ell) :
    Fintype.card (PowerTwoFriLevels ell 0 → TowerField) ≤ 2 ^ 256 := by
  simpa using Fintype.card_le_of_injective (rootFin pcs) (rootFin_injective pcs)

/-- No binding-closed concrete Tower256 Merkle PCS exists at positive height.
This is a cardinality theorem, not a cryptographic assumption. -/
theorem merklePcs_empty_of_positive {ell : Nat} (positive : 0 < ell) :
    ¬Nonempty (MerklePcs ell) := by
  rintro ⟨pcs⟩
  have bounded := word_card_le_root_card pcs
  have towerCard : Fintype.card TowerField = 2 ^ 256 := by
    rw [← Nat.card_eq_fintype_card]
    exact Minidregg.Compiler.BinaryTower256Profile.profile_cardinality
  have two_le_index : 2 ≤ 2 ^ ell := by
    exact (Nat.succ_le_iff).2 (Nat.one_lt_two_pow (Nat.ne_of_gt positive))
  have base_gt_one : 1 < 2 ^ 256 := Nat.one_lt_two_pow (by decide)
  have square_le_words : (2 ^ 256) ^ 2 ≤ (2 ^ 256) ^ (2 ^ ell) :=
    Nat.pow_le_pow_right (Nat.zero_lt_of_lt base_gt_one) two_le_index
  have root_lt_square : 2 ^ 256 < (2 ^ 256) ^ 2 := by
    nlinarith [Nat.one_lt_two_pow (by decide : 256 ≠ 0)]
  have root_lt_words : 2 ^ 256 < (2 ^ 256) ^ (2 ^ ell) :=
    lt_of_lt_of_le root_lt_square square_le_words
  have words_le_root : (2 ^ 256) ^ (2 ^ ell) ≤ 2 ^ 256 := by
    simpa [PowerTwoFriLevels, Fintype.card_fun, towerCard] using bounded
  exact (Nat.not_lt_of_ge words_le_root) root_lt_words

/-- **The vacuity, named.**  At positive height every statement whatsoever
about a `MerklePcs ell` holds, including `False`.  A module quantified over
this carrier proves nothing at any height that folds. -/
theorem merklePcs_vacuous_of_positive {ell : Nat} (positive : 0 < ell)
    (P : MerklePcs ell → Prop) (pcs : MerklePcs ell) : P pcs :=
  absurd ⟨pcs⟩ (merklePcs_empty_of_positive positive)

/-- The carrier is empty as an instance, so `exact absurd pcs (by infer)` and
`simp` can both discharge a positive-height goal on sight. -/
theorem merklePcs_isEmpty_of_positive {ell : Nat} (positive : 0 < ell) :
    IsEmpty (MerklePcs ell) :=
  not_nonempty_iff.mp (merklePcs_empty_of_positive positive)

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256MerkleCardinalityCore.merklePcs_empty_of_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePcs_empty_of_positive
/-- info: 'Minidregg.Assurance.Tower256MerkleCardinalityCore.merklePcs_vacuous_of_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePcs_vacuous_of_positive
/-- info: 'Minidregg.Assurance.Tower256MerkleCardinalityCore.merklePcs_isEmpty_of_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePcs_isEmpty_of_positive

end

end Minidregg.Assurance.Tower256MerkleCardinalityCore
