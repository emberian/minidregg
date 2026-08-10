/-
# Assurance.SemanticHistoryTower256CheckpointGame -- one history/additive checkpoint game

This module joins the trace-derived unshifted BCS history boundary to the
concrete Tower256 additive-FRI controller family on one `Omega` and one
`FailureLedger`.

The deterministic joints are exact: the retained history supplies the BCS
chain, the existing WARP schedule terminates at the semantic checkpoint root,
and that root is the first root of the accepted additive controller schedule.
The ideal BCS theorem and concrete additive controller result remain separate
objects.  Their genuinely cryptographic composition is one explicit
pointwise cover on the common coin; this file does not manufacture MCA, PCS,
commitment collision resistance, ROM transport, or hiding.
-/

import Assurance.SemanticHistoryBcsGame
import Assurance.Tower256AdditiveFriControllerAdmission

namespace Minidregg.Assurance.SemanticHistoryTower256CheckpointGame

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticAdditiveFriCheckpoint
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryStraightlinePcs
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriControllerAdmission
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.BinaryTower256Profile
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

universe uSemantics uTranscript uClauseInput uClauseQuery
  uClauseReply uClauseOutcome uClauseEvidence

abbrev TowerField := Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m queryCount n : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : Minidregg.Compiler.Tower256AdditiveFriController.FriClause
  pcs m manifest}
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

local notation "TowerCommitments" =>
  (fun level => pcs.commitment level)

local notation "BoundCheckpoint" => Checkpoint
  (n := n) (F := TowerField) (ell := ell) (m := m)
  (FriOp := fun _ => List UInt8)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) TowerCommitments clause

/-- The already-landed semantic straightline object is used here only for its
exact history fold schedule and binding.  Its older component error ledger is
not added to the common-game price below. -/
abbrev CheckpointJoin (checkpoint : BoundCheckpoint) :=
  StraightlineCheckpointExtraction
    (n := n) (F := TowerField) (ell := ell) (m := m)
    (FriOp := fun _ => List UInt8)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells)
    TowerCommitments clause checkpoint Omega Transcript

/-- The semantic code carried by this exact checkpoint. -/
abbrev CheckpointCode (checkpoint : BoundCheckpoint) :=
  checkpointCode TowerCommitments clause checkpoint.padding

/-- The level-zero Tower256 commitment pulled back to semantic receipt
coordinates. -/
abbrev CheckpointCommitment (checkpoint : BoundCheckpoint) :=
  semanticCommitment TowerCommitments checkpoint.padding

/-- Exact opened BCS data for this checkpoint head.  In particular its
`codeExact` field is the honest residual that the semantic pullback code must
also provide the requested Reed--Solomon presentation. -/
abbrev CheckpointBcsOpenings
    (checkpoint : BoundCheckpoint)
    (domain : BoundReceiptIx n ↪ TowerField) (degree openedCount : Nat) :=
  HistoryBcsOpenings
    (C := CheckpointCode checkpoint)
    (S := CheckpointCommitment checkpoint)
    checkpoint.head domain degree openedCount

/-! ## One family, one coin, one exhaustive ledger -/

/-- The joint family carries the ideal history mathematics and concrete
additive controller family separately.  `historyFailureCover` is the real
BCS-to-PCS/CR/ROM reduction residual: it must concern this exact `Omega` and
the very same ledger already owned by `tower`. -/
structure JointGameFamily
    where
  checkpoint : BoundCheckpoint
  tower : CommonGameFamily (pcs := pcs) (clause := clause)
    (verifier := verifier) Omega Error request
  historyJoin : CheckpointJoin (Omega := Omega) (Transcript := Transcript)
    checkpoint
  historyHasLink : 0 < checkpoint.head.foldRounds
  additiveRoundsPositive : 0 < m
  deltaStar : Real
  deltaStarPositive : 0 < deltaStar
  deltaStarLeOne : deltaStar ≤ 1
  domain : BoundReceiptIx n ↪ TowerField
  degree : Nat
  openedCount : Nat
  openings : CheckpointBcsOpenings checkpoint domain degree openedCount
  math : HistoryBcsMath (F := TowerField) (C := CheckpointCode checkpoint)
    deltaStar
  /-- Exact externally supplied false-acceptance predicate selected by the
  concrete BCS/ROM reduction; this is not an implemented verifier predicate. -/
  historyFalseAccept : Omega → Prop
  /-- The pointwise history reduction, on the shared coin and ledger. -/
  historyFailureCover : ∀ omega, historyFalseAccept omega →
    (tower.ledger .historyPcs).event omega ∨
    (tower.ledger .commitmentBinding).event omega ∨
    (tower.ledger .oracleTransport).event omega

namespace JointGameFamily

local notation "BoundJoint" => JointGameFamily
  (ell := ell) (m := m) (queryCount := queryCount) (n := n)
  (manifest := manifest) (pcs := pcs) (clause := clause)
  (verifier := verifier) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (Omega := Omega)
  (Transcript := Transcript) (Error := Error) (request := request)

/-- False end-to-end acceptance means either the exact history BCS execution
is false or the exact byte-checked additive controller execution is false. -/
def FalseAccept
    (joint : BoundJoint)
    (omega : Omega) : Prop :=
  joint.historyFalseAccept omega ∨ joint.tower.FalseAccept omega

/-- Exactly the four failure events used by this history/checkpoint join. -/
def Bad
    (joint : BoundJoint)
    (omega : Omega) : Prop :=
  (joint.tower.ledger .historyPcs).event omega ∨
  (joint.tower.ledger .additiveProximity).event omega ∨
  (joint.tower.ledger .commitmentBinding).event omega ∨
  (joint.tower.ledger .oracleTransport).event omega

/-- Exact additive price of the four-event joint boundary. -/
def Price
    (joint : BoundJoint) : Real :=
  (joint.tower.ledger .historyPcs).price +
  (joint.tower.ledger .additiveProximity).price +
  (joint.tower.ledger .commitmentBinding).price +
  (joint.tower.ledger .oracleTransport).price

/-- The load-bearing pointwise composition theorem.  Both component covers
are used, and both refer to `tower.ledger` at the identical `omega`. -/
theorem falseAccept_bad
    (joint : BoundJoint)
    (omega : Omega) : joint.FalseAccept omega → joint.Bad omega := by
  rintro (history | additive)
  · rcases joint.historyFailureCover omega history with pcs | binding | rom
    · exact Or.inl pcs
    · exact Or.inr (Or.inr (Or.inl binding))
    · exact Or.inr (Or.inr (Or.inr rom))
  · obtain ⟨reply, selected, falseStatement⟩ := additive
    rcases joint.tower.failureCover omega reply selected falseStatement with
      proximity | binding | rom
    · exact Or.inr (Or.inl proximity)
    · exact Or.inr (Or.inr (Or.inl binding))
    · exact Or.inr (Or.inr (Or.inr rom))

/-- The exact four-event join is included in the repository's exhaustive
common ledger. -/
theorem bad_implies_ledgerBad
    (joint : BoundJoint)
    (omega : Omega) : joint.Bad omega → joint.tower.ledger.Bad omega := by
  rintro (history | proximity | binding | rom)
  · exact Or.inr (Or.inr (Or.inl history))
  · exact Or.inr (Or.inr (Or.inr (Or.inl proximity)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl binding))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rom)))))

/-- The same concrete additive schedule now hosts the joint false-acceptance
predicate and the one exhaustive ledger. -/
def securityGame
    (joint : BoundJoint) :
    SecurityGame Omega Digest (List UInt8) TowerField Digest m where
  transcript := joint.tower.schedule
  ledger := joint.tower.ledger
  falseAccept := joint.FalseAccept
  failureCover := fun omega accepted =>
    joint.bad_implies_ledgerBad omega (joint.falseAccept_bad omega accepted)

/-- Four-event union bound on one coin space; no independence is assumed. -/
theorem bad_le_price
    (joint : BoundJoint) :
    uniformProb Omega joint.Bad ≤ joint.Price := by
  have h1 := uniformProb_or_le (joint.tower.ledger .historyPcs).event (fun omega =>
    (joint.tower.ledger .additiveProximity).event omega ∨
    (joint.tower.ledger .commitmentBinding).event omega ∨
    (joint.tower.ledger .oracleTransport).event omega)
  have h2 := uniformProb_or_le (joint.tower.ledger .additiveProximity).event
    (fun omega => (joint.tower.ledger .commitmentBinding).event omega ∨
      (joint.tower.ledger .oracleTransport).event omega)
  have h3 := uniformProb_or_le (joint.tower.ledger .commitmentBinding).event
    (joint.tower.ledger .oracleTransport).event
  unfold Bad Price
  linarith [(joint.tower.ledger .historyPcs).bound,
    (joint.tower.ledger .additiveProximity).bound,
    (joint.tower.ledger .commitmentBinding).bound,
    (joint.tower.ledger .oracleTransport).bound]

/-- End-to-end joint price, sharper than charging every unused ledger class. -/
theorem falseAccept_le
    (joint : BoundJoint) :
    uniformProb Omega joint.FalseAccept ≤ joint.Price :=
  le_trans (uniformProb_mono joint.falseAccept_bad) joint.bad_le_price

/-! ## Exact schedule and root joints -/

/-- The WARP terminal root is the additive transcript's literal level-zero
root for the selected controller receipt. -/
theorem terminalRoot_eq_receiptInitial
    (joint : BoundJoint)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) :
    (historyDualRootSchedule TowerCommitments joint.checkpoint joint.historyJoin).terminalRoot =
      clause.transcript.rootAt reply.receipt.challenges 0
        (Nat.zero_le m) := by
  calc
    (historyDualRootSchedule TowerCommitments joint.checkpoint joint.historyJoin).terminalRoot =
        clause.transcript.root 0 (fun i => i.elim0) :=
      terminal_root_eq_additive_initial TowerCommitments joint.checkpoint
        joint.historyJoin
    _ = clause.transcript.rootAt reply.receipt.challenges 0
        (Nat.zero_le m) := by
      unfold FriAdaptiveTranscript.rootAt
      congr 1
      funext i
      exact i.elim0

/-- At the first additive round, the shared schedule exposes exactly the
history terminal/checkpoint root as its singleton root prefix. -/
theorem sharedInitialRoots_exact
    (joint : BoundJoint)
    {omega : Omega}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : joint.tower.execution omega = some reply) :
    joint.tower.schedule.rootsAt 0
        (challengePrefix (joint.tower.schedule.challenges omega)
          ⟨0, joint.additiveRoundsPositive⟩) =
      [(historyDualRootSchedule TowerCommitments joint.checkpoint
        joint.historyJoin).terminalRoot] := by
  rw [joint.tower.scheduleRootsExact omega reply selected
    ⟨0, joint.additiveRoundsPositive⟩]
  unfold rootsBefore
  rw [show (List.ofFn fun n : Fin 1 =>
      clause.transcript.rootAt reply.receipt.challenges n
        (by omega)) =
      [clause.transcript.rootAt reply.receipt.challenges 0
        (Nat.zero_le m)] by
    rw [List.ofFn_succ, List.ofFn_zero]
    rfl]
  rw [joint.terminalRoot_eq_receiptInitial reply]

/-! ## Conditional accepted joint object -/

/-- The exact Fiat--Shamir error expression for the retained trace. -/
noncomputable def historyFsError
    (joint : BoundJoint) : Nat → Nat → Real → Real :=
  fun _saltBudget grindingBudget delta =>
    ((grindingBudget : Real) +
        ((reindexChain (historyChain joint.checkpoint.head)).length : Real)) *
      accRbrError TowerField joint.math.errstar delta

/-- The ideal BCS result for this exact retained-history instance.  This is
derived solely from `joint.math`; no deployment event is used in its proof. -/
noncomputable def idealHistoryFiatShamir
    (joint : BoundJoint)
    (Z : Set (Stmt (historyBcsReduction
      (C := CheckpointCode joint.checkpoint)
      (S := CheckpointCommitment joint.checkpoint)
      joint.checkpoint.head joint.historyHasLink joint.deltaStar
      joint.deltaStarPositive joint.deltaStarLeOne joint.domain joint.degree
      joint.openedCount joint.openings))) :
    FsStraightlineKnowledgeSoundness
      (historyBcsReduction joint.checkpoint.head joint.historyHasLink
        joint.deltaStar joint.deltaStarPositive joint.deltaStarLeOne
        joint.domain joint.degree joint.openedCount joint.openings) Z
      joint.historyFsError :=
  accFsSound_bcs (F := TowerField)
    (reindexCode (CheckpointCode joint.checkpoint))
    joint.checkpoint.head.foldRoot
    (reindexChain (historyChain joint.checkpoint.head))
    receiptCoordinateCountPositive
    (by simpa [historyChain_length] using joint.historyHasLink)
    joint.deltaStar joint.deltaStarPositive joint.deltaStarLeOne
    (reindexCommitment (S := CheckpointCommitment joint.checkpoint))
    (reindexDomain joint.domain) joint.degree joint.openings.queries
    joint.math.errstar joint.math.minimumDistance
    joint.math.mutualCorrelatedAgreement joint.math.deltaBelowAgreement
    joint.math.deltaBelowHalfDistance joint.math.errorNonnegative Z

/-- A selected good coin retains both sides without conflating them: the
ideal BCS theorem is attached to the exact three history good events, while
the concrete Tower256 controller yields its existing accepted sample. -/
structure AcceptedHistoryCheckpoint
    (joint : BoundJoint)
    (omega : Omega)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request)
    (Z : Set (Stmt (historyBcsReduction
      (C := CheckpointCode joint.checkpoint)
      (S := CheckpointCommitment joint.checkpoint)
      joint.checkpoint.head joint.historyHasLink joint.deltaStar
      joint.deltaStarPositive joint.deltaStarLeOne joint.domain joint.degree
      joint.openedCount joint.openings))) where
  private mk ::
  historyPcs : joint.tower.ledger.Good .historyPcs omega
  historyCommitmentBinding :
    joint.tower.ledger.Good .commitmentBinding omega
  historyOracleTransport : joint.tower.ledger.Good .oracleTransport omega
  idealHistory : FsStraightlineKnowledgeSoundness
    (historyBcsReduction joint.checkpoint.head joint.historyHasLink
      joint.deltaStar joint.deltaStarPositive joint.deltaStarLeOne
      joint.domain joint.degree joint.openedCount joint.openings) Z
    joint.historyFsError
  additiveAdmission : CommonCoinAdmission joint.tower.ledger omega request reply
  additiveSample : AcceptedSample clause
    (joint.tower.ledger.Good .commitmentBinding omega)
    (joint.tower.ledger.Good .oracleTransport omega)
    (ArithmeticBytesChecked request reply)
  scheduleChallengesExact :
    joint.tower.schedule.challenges omega = reply.receipt.challenges
  scheduleRootsExact : ∀ j : Fin m,
    joint.tower.schedule.rootsAt (j : Nat)
        (challengePrefix (joint.tower.schedule.challenges omega) j) =
      rootsBefore (clause := clause) reply.receipt j
  terminalRootExact :
    (historyDualRootSchedule TowerCommitments joint.checkpoint
      joint.historyJoin).terminalRoot =
      clause.transcript.rootAt reply.receipt.challenges 0 (Nat.zero_le m)
  sharedInitialRootsExact :
    joint.tower.schedule.rootsAt 0
        (challengePrefix (joint.tower.schedule.challenges omega)
          ⟨0, joint.additiveRoundsPositive⟩) =
      [(historyDualRootSchedule TowerCommitments joint.checkpoint
        joint.historyJoin).terminalRoot]

/-- The sole constructor in this module for a selected accepted joint: all
four good events come from `¬ ledger.Bad omega`, and the exact controller
selection supplies the schedule equalities. -/
noncomputable def acceptedOfNotBad
    (joint : BoundJoint)
    {omega : Omega}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : joint.tower.execution omega = some reply)
    (notBad : ¬joint.tower.ledger.Bad omega)
    (Z : Set (Stmt (historyBcsReduction
      (C := CheckpointCode joint.checkpoint)
      (S := CheckpointCommitment joint.checkpoint)
      joint.checkpoint.head joint.historyHasLink joint.deltaStar
      joint.deltaStarPositive joint.deltaStarLeOne joint.domain joint.degree
      joint.openedCount joint.openings))) :
    AcceptedHistoryCheckpoint joint omega reply Z := by
  let additiveAdmission : CommonCoinAdmission joint.tower.ledger omega request reply :=
    { commitmentBinding := joint.tower.ledger.good_of_not_bad notBad
        .commitmentBinding
      oracleTransport := joint.tower.ledger.good_of_not_bad notBad .oracleTransport
      additiveProximity := joint.tower.ledger.good_of_not_bad notBad
        .additiveProximity }
  exact
    { historyPcs := joint.tower.ledger.good_of_not_bad notBad .historyPcs
      historyCommitmentBinding :=
        joint.tower.ledger.good_of_not_bad notBad .commitmentBinding
      historyOracleTransport :=
        joint.tower.ledger.good_of_not_bad notBad .oracleTransport
      idealHistory := joint.idealHistoryFiatShamir Z
      additiveAdmission := additiveAdmission
      additiveSample := additiveAdmission.acceptedSample
      scheduleChallengesExact := joint.tower.scheduleChallengesExact omega reply selected
      scheduleRootsExact := joint.tower.scheduleRootsExact omega reply selected
      terminalRootExact := joint.terminalRoot_eq_receiptInitial reply
      sharedInitialRootsExact := joint.sharedInitialRoots_exact selected }

/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.falseAccept_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms falseAccept_bad
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.bad_le_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bad_le_price
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms falseAccept_le
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.terminalRoot_eq_receiptInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms terminalRoot_eq_receiptInitial
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.sharedInitialRoots_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sharedInitialRoots_exact
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.idealHistoryFiatShamir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealHistoryFiatShamir
/-- info: 'Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily.acceptedOfNotBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedOfNotBad

end JointGameFamily

end

end Minidregg.Assurance.SemanticHistoryTower256CheckpointGame
