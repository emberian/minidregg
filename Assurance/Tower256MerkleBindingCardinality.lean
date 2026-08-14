/-
# Assurance.Tower256MerkleBindingCardinality -- the old joint game is impossible

The cardinality argument itself now lives in
`Assurance.Tower256MerkleCardinalityCore`, which sits directly above
`Compiler.Tower256AdditiveFriController` so that **every** module quantified
over `MerklePcs` can import the refutation and carry its own retraction.  This
module keeps only the consequence that needs the semantic-history checkpoint
game: the old history/additive `JointGameFamily` is uninhabitable.

It explains why that joint should not be "inhabited" with a toy constructor:
its `additiveRoundsPositive` and tower round bound force a positive Merkle
height, precisely where the binding-closed PCS carrier is impossible.  The raw
controller/PCS is the honest replacement because it retains extracted collision
events instead of postulating an injective finite hash.
-/

import Assurance.SemanticHistoryTower256CheckpointGame
import Assurance.Tower256MerkleCardinalityCore

namespace Minidregg.Assurance.Tower256MerkleBindingCardinality

-- ⚠ `Tower256MerkleCardinalityCore` is NOT opened: it exports its own
-- `TowerField` abbreviation, which is ambiguous against the checkpoint game's.
-- The one name this module needs is written out in full below.
open Minidregg.Assurance.SemanticHistoryTower256CheckpointGame
open Minidregg.Compiler
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Selvage
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

local instance : Fintype TowerField := Fintype.ofFinite _
local instance : DecidableEq TowerField := Classical.decEq _

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
positive-height PCS regime refuted in the cardinality core. -/
theorem jointGameFamily_impossible (joint : BoundJoint) : False := by
  have positiveEll : 0 < ell :=
    lt_of_lt_of_le joint.additiveRoundsPositive clause.tower.rounds_le
  exact Tower256MerkleCardinalityCore.merklePcs_empty_of_positive
    positiveEll ⟨pcs⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256MerkleBindingCardinality.jointGameFamily_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jointGameFamily_impossible

end

end Minidregg.Assurance.Tower256MerkleBindingCardinality
