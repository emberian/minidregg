/-
# Assurance.Tower256MerkleBindingCardinality -- why the old PCS carrier is empty

`Tower256AdditiveFriController.MerklePcs` asks the concrete cSHAKE256 Merkle
commitment to be unconditionally position binding.  Completeness plus position
binding makes the whole-word commitment injective.  But every concrete Merkle
root is a 256-bit cSHAKE digest, while a positive-height Tower256 column has
strictly more than `2^256` possible words.

This module turns that audit observation into a theorem.  It explains why the
old history/additive `JointGameFamily` should not be “inhabited” with a toy
constructor: its `additiveRoundsPositive` and tower round bound force a positive
Merkle height, precisely where the binding-closed PCS carrier is impossible.
The raw controller/PCS is the honest replacement because it retains extracted
collision events instead of postulating an injective finite hash.
-/

import Assurance.SemanticHistoryTower256CheckpointGame
import Compiler.Sp800185Cshake256

namespace Minidregg.Assurance.Tower256MerkleBindingCardinality

open Minidregg.Assurance.SemanticHistoryTower256CheckpointGame
open Minidregg.Compiler
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
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
internal node, so its range is also strictly below `2^256`. -/
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

/-- Binding would embed every level-zero word into `Fin (2^256)`. -/
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

/-! ## Consequence for the old history/additive joint -/

universe uSemantics uTranscript uClauseInput uClauseQuery
  uClauseReply uClauseOutcome

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest

variable {ell m queryCount n : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : FriClause pcs m manifest}
variable {verifier : Verifier (queryCount := queryCount) pcs clause}
variable
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext → BindingIx → TowerField}
variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {Transcript : Type uTranscript}
variable {Error : Type} {request : List UInt8}

local notation "BoundJoint" =>
  JointGameFamily
    (ell := ell) (m := m) (queryCount := queryCount) (n := n)
    (manifest := manifest) (pcs := pcs) (clause := clause)
    (verifier := verifier) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (Omega := Omega)
    (Transcript := Transcript) (Error := Error) (request := request)

/-- Every value of the old joint produces a contradiction.  Its positive
additive round count and the additive tower's `m ≤ ell` law force the exact
positive-height PCS regime refuted above. -/
theorem jointGameFamily_impossible (joint : BoundJoint) : False := by
  have positiveEll : 0 < ell :=
    lt_of_lt_of_le joint.additiveRoundsPositive clause.tower.rounds_le
  exact merklePcs_empty_of_positive positiveEll ⟨pcs⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256MerkleBindingCardinality.merklePcs_empty_of_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePcs_empty_of_positive
/-- info: 'Minidregg.Assurance.Tower256MerkleBindingCardinality.jointGameFamily_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jointGameFamily_impossible

end

end Minidregg.Assurance.Tower256MerkleBindingCardinality
