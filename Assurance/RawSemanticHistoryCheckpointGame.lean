/-
# Assurance.RawSemanticHistoryCheckpointGame -- the honest history/additive seam

The former `SemanticHistoryTower256CheckpointGame.JointGameFamily` is built on
`MerklePcs`, whose universal `PositionBinding` field is inconsistent at every
positive tree depth.  This module does not repair that carrier.  It replaces
the binding-closed seam with the executable `RawMerklePcs` and keeps the
adversary's opening attempt all the way to the landed cSHAKE collision
extractor.

There are three deliberately separate objects here:

* `RawCheckpoint` joins an ideal semantic history head to ONE selected raw
  level-zero word/root.  Its bridge is pointwise; it says nothing about a
  second word and cannot imply universal binding.
* `HistoryLane` selects the raw BCS tape at the same nonempty additive game
  coin.  Failed root attribution is charged to oracle transport, unequal
  accepted openings become exact path-specific `ExtractedCollision`s, and an
  exact tape reaches one explicit PCS/MCA residual.
* `GameFamily` constructs the four-event ledger: history PCS/MCA, additive
  proximity, extracted cSHAKE collision (history OR additive), and oracle
  transport.  Its pointwise cover and probability bound use one coin type.

This is a common-coin ledger, not a shared-ROM theorem.  No transcript schedule
is projected between the history and additive lanes.  The `oracleTransport`
event is precisely where that unbuilt distributional theorem remains.
-/

import Assurance.RawHistoryCollisionBridge
import Assurance.Tower256AdditiveFriRawAdmission

namespace Minidregg.Assurance.RawSemanticHistoryCheckpointGame

open scoped BigOperators
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.RawHistoryBcsOpenings
open Minidregg.Assurance.RawHistoryCollisionBridge
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField := Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m queryCount n : Nat}
variable {pcs : RawMerklePcs ell}
variable {statement : Statement pcs m}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext -> BindingIx -> TowerField}
    {C : Submodule TowerField (BoundReceiptIx n -> TowerField)}
    {idealS : BindingCommitment Digest TowerField
      (BoundReceiptIx n) (List UInt8)}

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := TowerField) (Op := List UInt8)
  manifest registry clauseEvidence family headerCells C idealS

/-! ## A pointwise semantic/raw checkpoint -/

/-- Receipt coordinates occupy a prefix of the level-zero raw Merkle tree.
The unused leaves are explicit filler; no cardinality equality is assumed. -/
structure ReceiptTreeCover (ell n : Nat) where
  covers : CoordinateCount (BoundReceiptIx n) <= 2 ^ ell
  filler : TowerField

namespace ReceiptTreeCover

def toPowerTwoCover (cover : ReceiptTreeCover ell n) :
    PowerTwoCover (CoordinateCount (BoundReceiptIx n)) TowerField where
  exponent := ell
  covers := cover.covers
  filler := cover.filler

end ReceiptTreeCover

/-- One ideal semantic head, related only at its selected folded word to the
executable raw level-zero Merkle checker.  `selectedHeadRootExact` is a
pointwise equality.  It cannot be instantiated at another word and is not a
`PositionBinding` premise in disguise. -/
structure RawCheckpoint where
  head : HistoryHead
  treeCover : ReceiptTreeCover ell n
  /-- The additive statement's selected initial word is exactly the padded
  finite-coordinate semantic word. -/
  initialFiniteWordExact :
      RawMerklePcs.finiteWord 0
        (statement.transcript.word 0 (fun i => i.elim0)) =
      treeCover.toPowerTwoCover.padWord
        (reindexWord head.foldedWord)
  /-- The ideal head root and executable Merkle root agree for THIS word.
  There is intentionally no universal quantifier over words. -/
  selectedHeadRootExact :
    idealS.commit head.foldedWord =
      (treeCover.toPowerTwoCover.restrict
        (pcs.finiteScheme 0)).commit (reindexWord head.foldedWord)

namespace RawCheckpoint

local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)

/-- The exact receipt-coordinate view of the deployed raw level-zero tree. -/
def cover (checkpoint : BoundCheckpoint) :
    PowerTwoCover (CoordinateCount (BoundReceiptIx n)) TowerField :=
  checkpoint.treeCover.toPowerTwoCover

/-- The executable history opening scheme is the raw Merkle checker restricted
to the receipt-coordinate prefix.  Its type has no binding field. -/
def historyScheme (checkpoint : BoundCheckpoint) :
    OpeningScheme Digest TowerField (ReceiptCoordinate n) (List UInt8) :=
  checkpoint.cover.restrict (pcs.finiteScheme 0)

/-- The submitted additive initial root is attributed to the exact raw
commitment of the selected semantic word. -/
theorem initialRawRoot_eq_historyCommit (checkpoint : BoundCheckpoint) :
    statement.transcript.root 0 (fun i => i.elim0) =
      checkpoint.historyScheme.commit (reindexWord checkpoint.head.foldedWord) := by
  calc
    statement.transcript.root 0 (fun i => i.elim0) =
        (pcs.opening 0).commit
          (statement.transcript.word 0 (fun i => i.elim0)) :=
      statement.transcript.root_eq_commit 0 (fun i => i.elim0)
    _ = (pcs.finiteScheme 0).commit
        (RawMerklePcs.finiteWord 0
          (statement.transcript.word 0 (fun i => i.elim0))) := rfl
    _ = (pcs.finiteScheme 0).commit
        (checkpoint.cover.padWord
          (reindexWord checkpoint.head.foldedWord)) := by
      change (pcs.finiteScheme 0).commit
          (RawMerklePcs.finiteWord 0
            (statement.transcript.word 0 (fun i => i.elim0))) =
        (pcs.finiteScheme 0).commit
          (checkpoint.treeCover.toPowerTwoCover.padWord
            (reindexWord checkpoint.head.foldedWord))
      rw [checkpoint.initialFiniteWordExact]
    _ = checkpoint.historyScheme.commit
        (reindexWord checkpoint.head.foldedWord) := by
      change (pcs.finiteScheme 0).commit
          (checkpoint.treeCover.toPowerTwoCover.padWord
            (reindexWord checkpoint.head.foldedWord)) = _
      rfl

/-- The raw additive statement therefore starts at the semantic head root.
The proof uses only the selected-word equality and the ideal head's own root
binding; it does not establish raw binding for any opening. -/
theorem initialRawRoot_eq_semanticHead (checkpoint : BoundCheckpoint) :
    statement.transcript.root 0 (fun i => i.elim0) =
      checkpoint.head.accumulator.rt := by
  calc
    statement.transcript.root 0 (fun i => i.elim0) =
        checkpoint.historyScheme.commit
          (reindexWord checkpoint.head.foldedWord) :=
      checkpoint.initialRawRoot_eq_historyCommit
    _ = idealS.commit checkpoint.head.foldedWord :=
      checkpoint.selectedHeadRootExact.symm
    _ = checkpoint.head.accumulator.rt := checkpoint.head.rootBound.symm

/-- The runtime-shaped level-zero root is the same semantic head for every
later additive challenge tuple. -/
theorem initialRawRoot_before_challenges (checkpoint : BoundCheckpoint)
    (challenges : Fin m -> TowerField) :
    statement.transcript.rootAt challenges 0 (Nat.zero_le m) =
      checkpoint.head.accumulator.rt := by
  calc
    statement.transcript.rootAt challenges 0 (Nat.zero_le m) =
        statement.transcript.root 0 (fun i => i.elim0) := by
      unfold RawTranscript.rootAt
      apply congrArg (statement.transcript.root 0)
      funext i
      exact i.elim0
    _ = checkpoint.head.accumulator.rt :=
      checkpoint.initialRawRoot_eq_semanticHead

end RawCheckpoint

/-! ## The raw retained-history tape and its exact collision event -/

local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)

abbrev CheckpointHistoryTranscript
    (checkpoint : BoundCheckpoint)
    (domain : BoundReceiptIx n ↪ TowerField)
    (degree openedCount : Nat) :=
  RawHistoryBcsTranscript checkpoint.historyScheme checkpoint.head
    (F := TowerField) (n := n) (Op := List UInt8)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (S := idealS)
    domain degree openedCount

namespace CheckpointHistoryTranscript

variable {domain : BoundReceiptIx n ↪ TowerField}
variable {degree openedCount : Nat}

local notation "BoundTranscript" checkpoint => CheckpointHistoryTranscript
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
  (checkpoint := checkpoint) (domain := domain)
  (degree := degree) (openedCount := openedCount)

/-- The fully attributed, collision-free branch: the raw submitted columns
reconstruct exactly the semantic head's retained link-word rounds. -/
def Exact
    (checkpoint : BoundCheckpoint) (transcript : BoundTranscript checkpoint) :
    Prop :=
  bcsRounds (reindexDomain domain) degree transcript.queries
      (List.ofFn fun j : Fin checkpoint.head.foldRounds =>
        (transcript.messages j, checkpoint.head.foldChallenges j)) =
    List.ofFn fun j : Fin checkpoint.head.foldRounds =>
      (reindexWord (checkpoint.head.foldLinkWord j),
        checkpoint.head.foldChallenges j)

/-- Exact path-specific history collision evidence, tied to one selected BCS
round, query, submitted root, values, and opening pair. -/
def ExtractedHistoryCollision
    (checkpoint : BoundCheckpoint) (transcript : BoundTranscript checkpoint) :
    Prop :=
  ∃ (j : Fin checkpoint.head.foldRounds) (i : Fin openedCount)
      (attempt : OpeningPair TowerField (Fin (2 ^ ell))),
    attempt.root = (transcript.messages j).root ∧
    attempt.index = checkpoint.cover.leaf (transcript.queries i) ∧
    attempt.left = (transcript.messages j).cols i ∧
    attempt.right = checkpoint.cover.padWord (honestWord checkpoint.head j)
      (checkpoint.cover.leaf (transcript.queries i)) ∧
    ExtractedCollision pcs.backend.merkle (pcs.level 0).port attempt

/-- A retained unequal accepted history column reaches the concrete cSHAKE
Merkle extractor.  Nothing is replaced by a universal binding proposition. -/
theorem extractedHistoryCollision_of_equivocation
    (checkpoint : BoundCheckpoint) (transcript : BoundTranscript checkpoint)
    (equivocation : transcript.Equivocation) :
    ExtractedHistoryCollision (ell := ell) (pcs := pcs)
      (checkpoint := checkpoint) transcript := by
  obtain ⟨j, unequalOpening⟩ := equivocation
  obtain ⟨i, attempt, rootExact, indexExact, leftExact, rightExact, collision⟩ :=
    extractedCollision_of_restricted_equivocation checkpoint.cover
      pcs.backend.merkle (pcs.level 0).port unequalOpening
  exact ⟨j, i, attempt, rootExact, indexExact, leftExact, rightExact, collision⟩

/-- The raw carrier's trichotomy restated at the checkpoint boundary. -/
theorem attribution_equivocation_or_exact
    (checkpoint : BoundCheckpoint) (transcript : BoundTranscript checkpoint) :
    ¬transcript.RootPreimage ∨
      ExtractedHistoryCollision (ell := ell) (pcs := pcs)
        (checkpoint := checkpoint) transcript ∨
      Exact checkpoint transcript := by
  rcases transcript.attribution_split with missing | unequal | exact
  · exact Or.inl missing
  · exact Or.inr (Or.inl
      (extractedHistoryCollision_of_equivocation checkpoint transcript unequal))
  · exact Or.inr (Or.inr exact)

end CheckpointHistoryTranscript

/-! ## A genuine four-event same-coin ledger -/

/-- Join two exact events on one coin.  No independence premise is used. -/
def orFailure {Omega : Type} [Fintype Omega]
    (left right : PricedFailure Omega) : PricedFailure Omega where
  event := fun omega => left.event omega ∨ right.event omega
  price := left.price + right.price
  bound := by
    have union := uniformProb_or_le left.event right.event
    linarith [left.bound, right.bound]

/-- The four names are intentionally narrower than the repository-wide common
ledger.  In particular collision means an exact extracted cSHAKE collision,
not a universal binding assumption. -/
inductive FailureClass where
  | historyPcsMca
  | additiveProximity
  | extractedCshakeCollision
  | oracleTransport
deriving DecidableEq, Fintype, Repr

/-- One exhaustive four-event ledger on one finite, explicitly nonempty coin
space. -/
abbrev Ledger (Omega : Type) [Fintype Omega] :=
  FailureClass -> PricedFailure Omega

namespace Ledger

variable {Omega : Type} [Fintype Omega]

def Bad (ledger : Ledger Omega) (omega : Omega) : Prop :=
  (ledger .historyPcsMca).event omega ∨
  (ledger .additiveProximity).event omega ∨
  (ledger .extractedCshakeCollision).event omega ∨
  (ledger .oracleTransport).event omega

def Price (ledger : Ledger Omega) : Real :=
  (ledger .historyPcsMca).price +
  (ledger .additiveProximity).price +
  (ledger .extractedCshakeCollision).price +
  (ledger .oracleTransport).price

theorem bad_le_price (ledger : Ledger Omega) :
    uniformProb Omega ledger.Bad <= ledger.Price := by
  have outer := uniformProb_or_le (ledger .historyPcsMca).event (fun omega =>
    (ledger .additiveProximity).event omega ∨
    (ledger .extractedCshakeCollision).event omega ∨
    (ledger .oracleTransport).event omega)
  have middle := uniformProb_or_le (ledger .additiveProximity).event (fun omega =>
    (ledger .extractedCshakeCollision).event omega ∨
    (ledger .oracleTransport).event omega)
  have inner := uniformProb_or_le
    (ledger .extractedCshakeCollision).event
    (ledger .oracleTransport).event
  unfold Bad Price
  linarith [(ledger .historyPcsMca).bound,
    (ledger .additiveProximity).bound,
    (ledger .extractedCshakeCollision).bound,
    (ledger .oracleTransport).bound]

end Ledger

/-! ## The honest replacement family -/

variable {radius : Nat -> Real} {tau : Real}
variable {certificate : FarSoundnessCertificate statement radius tau}
variable {Error : Type} {request : List UInt8}
variable {verifier : Verifier (queryCount := queryCount) pcs statement}

local notation "Coin" => IdealCoin statement

/-- The history lane selects its tape on the exact additive ideal coin.  The
coin is required nonempty, preventing the zero-probability empty-carrier
vacuity that older common-game structures admitted.

`intrinsicOfExact` is the remaining PCS/MCA reduction: once roots are
attributed and no unequal opening remains, an exact raw BCS tape plus false
acceptance must enter the named intrinsic history event.  The field is
deliberately not dressed up as an implemented verifier theorem. -/
structure HistoryLane
    (verifier : Verifier (queryCount := queryCount) pcs statement)
    (checkpoint : BoundCheckpoint)
    (additive : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) where
  /-- The common game carrier is inhabited; no zero-cardinality probability
  space can discharge the joint theorem. -/
  coinNonempty : Nonempty Coin
  domain : BoundReceiptIx n ↪ TowerField
  degree : Nat
  openedCount : Nat
  historyHasLink : 0 < checkpoint.head.foldRounds
  deltaStar : Real
  deltaStarPositive : 0 < deltaStar
  deltaStarLeOne : deltaStar <= 1
  math : HistoryBcsMath (F := TowerField) (C := C) deltaStar
  transcript : Coin ->
    CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := domain)
      (degree := degree) (openedCount := openedCount)
  falseAccept : Coin -> Prop
  intrinsicPcsMcaFailure : Coin -> Prop
  /-- This exact event is what the common ledger calls history PCS/MCA. -/
  historyEventExact : ∀ coin,
    (additive.baseLedger .historyPcs).event coin ↔
      intrinsicPcsMcaFailure coin
  /-- A root for some other word is transport/attribution failure, not a PCS
  collision. -/
  missingAttributionIsTransport : ∀ coin,
    ¬(transcript coin).RootPreimage ->
      (additive.baseLedger .oracleTransport).event coin
  /-- The sole semantic/BCS residual after exact root/column recovery. -/
  intrinsicOfExact : ∀ coin,
    CheckpointHistoryTranscript.Exact (checkpoint := checkpoint)
      (transcript coin) -> falseAccept coin ->
      intrinsicPcsMcaFailure coin
  /-- A deployment price for the exact extracted history collision event. -/
  collisionFailure : PricedFailure Coin
  collisionEventExact : ∀ coin,
    collisionFailure.event coin ↔
      CheckpointHistoryTranscript.ExtractedHistoryCollision
        (ell := ell) (pcs := pcs) (checkpoint := checkpoint)
        (transcript coin)
  /-- The exact deployment reduction on this common coin.  The preceding
  fields expose its three branches separately; this field is the remaining
  executable PCS/MCA/transport proof obligation. -/
  falseAcceptCover : ∀ coin, falseAccept coin ->
    (additive.baseLedger .historyPcs).event coin ∨
      collisionFailure.event coin ∨
      (additive.baseLedger .oracleTransport).event coin

/-- Raw history and raw additive acceptance on the exact same nonempty coin.
No schedule-sharing field exists: the distributional seam remains the common
`oracleTransport` event. -/
structure GameFamily
    (verifier : Verifier (queryCount := queryCount) pcs statement) where
  checkpoint : BoundCheckpoint
  additive : RawGameFamily (queryCount := queryCount)
    (verifier := verifier) certificate Error request
  history : HistoryLane (queryCount := queryCount)
    (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (idealS := idealS)
    (radius := radius) (tau := tau) (certificate := certificate)
    (Error := Error) (request := request)
    verifier checkpoint additive

namespace GameFamily

variable {verifier : Verifier (queryCount := queryCount) pcs statement}

local notation "BoundGame" => GameFamily
  (ell := ell) (m := m) (queryCount := queryCount) (n := n)
  (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
  (radius := radius) (tau := tau) (certificate := certificate)
  (Error := Error) (request := request) verifier

/-- The exact collision event is the union of additive receipt collisions and
history opening collisions, both retaining their extracted attempts. -/
def ledger (game : BoundGame) : Ledger Coin
  | .historyPcsMca => game.additive.baseLedger .historyPcs
  | .additiveProximity => game.additive.additiveFailure
  | .extractedCshakeCollision =>
      orFailure game.additive.collisionFailure game.history.collisionFailure
  | .oracleTransport => game.additive.baseLedger .oracleTransport

def FalseAccept (game : BoundGame) (coin : Coin) : Prop :=
  game.history.falseAccept coin ∨ game.additive.FalseAccept coin

theorem falseAccept_bad (game : BoundGame) (coin : Coin)
    (accepted : game.FalseAccept coin) : game.ledger.Bad coin := by
  rcases accepted with historyAccepted | additiveAccepted
  · rcases game.history.falseAcceptCover coin historyAccepted with
      history | collision | transport
    · exact Or.inl history
    · exact Or.inr (Or.inr (Or.inl (Or.inr collision)))
    · exact Or.inr (Or.inr (Or.inr transport))
  · rcases game.additive.falseAccept_three_event_cover coin additiveAccepted with
      proximity | collision | transport
    · apply Or.inr
      apply Or.inl
      change game.additive.additiveFailure.event coin
      exact proximity
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      change (orFailure game.additive.collisionFailure
        game.history.collisionFailure).event coin
      exact Or.inl collision
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      change (game.additive.baseLedger .oracleTransport).event coin
      exact transport

/-- The honest four-event end-to-end bound on one nonempty coin space. -/
theorem falseAccept_le (game : BoundGame) :
    uniformProb Coin game.FalseAccept <= game.ledger.Price :=
  le_trans (uniformProb_mono game.falseAccept_bad) game.ledger.bad_le_price

/-- Outside all four exact events, neither raw history nor raw additive false
acceptance is possible. -/
theorem falseAccept_impossible_of_not_bad (game : BoundGame) {coin : Coin}
    (good : ¬game.ledger.Bad coin) : ¬game.FalseAccept coin := by
  intro accepted
  exact good (game.falseAccept_bad coin accepted)

end GameFamily

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.RawSemanticHistoryCheckpointGame.RawCheckpoint.initialRawRoot_eq_semanticHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawCheckpoint.initialRawRoot_eq_semanticHead
/-- info: 'Minidregg.Assurance.RawSemanticHistoryCheckpointGame.CheckpointHistoryTranscript.extractedHistoryCollision_of_equivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CheckpointHistoryTranscript.extractedHistoryCollision_of_equivocation
/-- info: 'Minidregg.Assurance.RawSemanticHistoryCheckpointGame.CheckpointHistoryTranscript.attribution_equivocation_or_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CheckpointHistoryTranscript.attribution_equivocation_or_exact
/-- info: 'Minidregg.Assurance.RawSemanticHistoryCheckpointGame.GameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GameFamily.falseAccept_le

end

end Minidregg.Assurance.RawSemanticHistoryCheckpointGame
