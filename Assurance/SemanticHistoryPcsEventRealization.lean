/-
# Assurance.SemanticHistoryPcsEventRealization -- the exact remaining history event

The current retained-history BCS reduction is already an *ideal binding-PCS*
reduction.  Its `BindingCommitment` was constructed from
`MerklePcs.positionBinding`, and `HistoryBcsOpenings.bcsWord_eq_historyLink`
has already used that universal property to erase every unequal-opening
attempt.  Consequently the concrete
`Tower256CshakeMerkleBinding.bindingFailure_implies_extractedCollision`
theorem has no adversarial opening pair to consume at this layer.

The actual Fiat--Shamir knowledge-failure event is nevertheless fully fixed
by `SemanticHistoryTower256DeployedBcs`.  It is the inherent MCA/PCS
extraction failure and belongs under `historyPcs`; it is not honest to force
it into commitment-binding or ROM failure.  This module introduces the
minimal remaining common-game interface, indexed only by that fixed event,
and proves that it is equivalent to the old three-way classifier whenever
binding and ROM are good.  It also proves same-coin price and contradiction
teeth.

The future raw migration target is named `RawHistoryBcsOpenings`: it must use
the exact executable `CommitmentScheme` (without `PositionBinding`), retain
the submitted `OpeningPair` for every challenged column, retain exact
root/round/query attribution to the adversary's `SrOutput`, and expose a
split from raw verifier failure to either the ideal history FS event or an
`ExtractedCollision`.  Merely wrapping `HistoryBcsOpenings` cannot implement
that signature because its binding premise has already removed the latter
branch.
-/

import Assurance.SemanticHistoryTower256DeployedBcs

namespace Minidregg.Assurance.SemanticHistoryPcsEventRealization

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryTower256CheckpointGame
open Minidregg.Assurance.SemanticHistoryTower256DeployedBcs
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

universe uSemantics uTranscript uClauseInput uClauseQuery
  uClauseReply uClauseOutcome

variable {ell m queryCount n : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : FriClause pcs m manifest}
variable {verifier : Verifier (queryCount := queryCount) pcs clause}

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext → BindingIx → TowerField}
variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {Transcript : Type uTranscript}
variable {Error : Type} {request : List UInt8}

local notation "BoundJoint" => JointGameFamily
  (ell := ell) (m := m) (queryCount := queryCount) (n := n)
  (manifest := manifest) (pcs := pcs) (clause := clause)
  (verifier := verifier) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (Omega := Omega)
  (Transcript := Transcript) (Error := Error) (request := request)

/-! ## The current binding-closed carrier has no collision witness -/

/-- Every retained opened message has already been identified with its exact
semantic link word.  An unequal-opening attempt is therefore unrepresentable
inside the current `HistoryBcsOpenings` carrier. -/
theorem no_retained_opening_mismatch (joint : BoundJoint) :
    ¬∃ j : Fin joint.checkpoint.head.foldRounds,
      bcsWord (reindexDomain joint.domain) joint.degree
          joint.openings.queries (joint.openings.messages j) ≠
        reindexWord (joint.checkpoint.head.foldLinkWord j) := by
  rintro ⟨j, mismatch⟩
  exact mismatch <|
    HistoryBcsOpenings.bcsWord_eq_historyLink joint.checkpoint.head
      joint.openings j

/-! ## Minimal realization of the inherent history-PCS event -/

/-- The exact remaining event realization.  Its domain is the fixed actual
retained-history Fiat--Shamir knowledge failure; callers cannot substitute an
unrelated proposition.  Its codomain is only `historyPcs`, because MCA/PCS
extraction failure is distinct from CR and ROM transport failure. -/
structure HistoryPcsEventRealization (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint) : Prop where
  historyPcs : ∀ omega, run.FalseAccept joint omega →
    (joint.tower.ledger .historyPcs).event omega

namespace HistoryPcsEventRealization

/-- The fixed history event is priced by the existing history-PCS ledger
entry on the identical common coin. -/
theorem falseAccept_le_historyPcs (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (realization : HistoryPcsEventRealization joint run) :
    uniformProb Omega (run.FalseAccept joint) ≤
      (joint.tower.ledger .historyPcs).price :=
  le_trans (uniformProb_mono realization.historyPcs)
    (joint.tower.ledger .historyPcs).bound

/-- The minimal history-PCS realization is sufficient for the previously
exposed three-way deployment interface, without charging CR or ROM for an
inherent algebraic extraction failure. -/
def toPcsCrRomReduction (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (realization : HistoryPcsEventRealization joint run) :
    PcsCrRomReduction joint run where
  classify := fun omega falseAccept =>
    Or.inl (realization.historyPcs omega falseAccept)

/-- Load-bearing tooth: a real knowledge failure at a coin declared good for
history PCS rules out this realization. -/
theorem impossible_of_falseAccept_and_historyPcsGood (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint) (omega : Omega)
    (falseAccept : run.FalseAccept joint omega)
    (pcsGood : joint.tower.ledger.Good .historyPcs omega) :
    ¬HistoryPcsEventRealization joint run := by
  intro realization
  exact pcsGood (realization.historyPcs omega falseAccept)

/-- If binding and ROM transport never fail, the old three-way classifier is
equivalent to this one exact history-PCS realization.  This proves minimality:
the extra disjuncts cannot secretly discharge the inherent MCA event. -/
theorem pcsCrRomReduction_iff
    (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (bindingGood : ∀ omega, joint.tower.ledger.Good .commitmentBinding omega)
    (romGood : ∀ omega, joint.tower.ledger.Good .oracleTransport omega) :
    PcsCrRomReduction joint run ↔ HistoryPcsEventRealization joint run := by
  constructor
  · intro reduction
    exact
      { historyPcs := fun omega falseAccept => by
          rcases reduction.classify omega falseAccept with pcs | binding | rom
          · exact pcs
          · exact False.elim (bindingGood omega binding)
          · exact False.elim (romGood omega rom) }
  · intro realization
    exact realization.toPcsCrRomReduction joint run

/-- The actual history plus concrete additive game now needs only the exact
history-PCS event realization at this layer. -/
def securityGame (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (realization : HistoryPcsEventRealization joint run) :
    SecurityGame Omega Digest (List UInt8) TowerField Digest m :=
  run.securityGame joint (realization.toPcsCrRomReduction joint run)

/-- Four-event end-to-end price, with the history component assigned to its
own exact ledger class. -/
theorem jointFalseAccept_le (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (realization : HistoryPcsEventRealization joint run) :
    uniformProb Omega (run.JointFalseAccept joint) ≤ joint.Price :=
  run.jointFalseAccept_le joint (realization.toPcsCrRomReduction joint run)

end HistoryPcsEventRealization

#print axioms no_retained_opening_mismatch
#print axioms HistoryPcsEventRealization.falseAccept_le_historyPcs
#print axioms HistoryPcsEventRealization.impossible_of_falseAccept_and_historyPcsGood
#print axioms HistoryPcsEventRealization.pcsCrRomReduction_iff
#print axioms HistoryPcsEventRealization.jointFalseAccept_le

end

end Minidregg.Assurance.SemanticHistoryPcsEventRealization
