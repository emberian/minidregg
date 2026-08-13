/-
# Assurance.Tower256RawSemanticHistoryCanonicalGame -- one executable coin

This module joins the raw semantic-history checkpoint to the actual raw
additive controller execution.  Unlike `RawSemanticHistoryCheckpointGame`,
the additive branch is not a caller-selected `Option` and its transport event
does not quantify over an arbitrary ideal witness: it is the literal mismatch
between the accepted receipt's own coin and the external game coin.

The history runner remains abstract because no executable history verifier or
MCA classifier has landed.  Its one semantic residual is therefore stated as
one sharply typed implication from an executed, exact raw BCS tape to the
intrinsic history PCS/MCA event.  Root-attribution failures and unequal
openings are derived mechanically as exact transport and extracted-cSHAKE
collision events.  All probabilities remain explicit deployment bounds.
-/

import Assurance.RawSemanticHistoryCheckpointGame
import Assurance.Tower256AdditiveFriCanonicalExecutionGame

namespace Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame

open scoped BigOperators
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.RawHistoryBcsOpenings
open Minidregg.Assurance.RawSemanticHistoryCheckpointGame
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField :=
  Minidregg.Compiler.BinaryTower256Profile.Tower256

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
variable {Error : Type} {request : List UInt8}
variable {verifier :
  Minidregg.Compiler.Tower256AdditiveFriRawController.Verifier
    (queryCount := queryCount) pcs statement}

local notation "Coin" => IdealCoin statement
local notation "Runner" =>
  Minidregg.Compiler.Tower256AdditiveFriRawController.OpaqueProofRunner Error

local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)

/-! ## The exact history execution seam -/

/-- The ideal additive carrier is constructively inhabited at every parameter
choice, so none of the probability bounds below can close via an empty coin
space. -/
def canonicalCoin : Coin :=
  (fun _ => 0, fun _ => ⟨0, by positivity⟩)

instance canonicalCoinNonempty : Nonempty Coin := ⟨canonicalCoin⟩

/-- An abstract executable history lane over the SAME coin as the raw
additive controller.  `intrinsicOfExecutedExact` is the sole unbuilt semantic
classifier.  The trichotomy around it is already constructive. -/
structure HistoryExecutionLane (checkpoint : BoundCheckpoint) where
  domain : BoundReceiptIx n ↪ TowerField
  degree : Nat
  openedCount : Nat
  run : Coin -> Option
    (CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := domain)
      (degree := degree) (openedCount := openedCount))
  /-- The semantic condition which makes an accepted history execution a
  false acceptance, kept separate from raw opening validity. -/
  falseStatement : (coin : Coin) ->
    CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := domain)
      (degree := degree) (openedCount := openedCount) -> Prop
  intrinsicPcsMcaFailure : Coin -> Prop
  /-- The only unbuilt classifier: an actually returned exact raw tape for a
  false statement must enter the intrinsic history PCS/MCA event. -/
  intrinsicOfExecutedExact : ∀ (coin : Coin)
      (tape : CheckpointHistoryTranscript
        (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
        (manifest := manifest) (registry := registry)
        (clauseEvidence := clauseEvidence) (family := family)
        (headerCells := headerCells) (C := C) (idealS := idealS)
        (checkpoint := checkpoint) (domain := domain)
        (degree := degree) (openedCount := openedCount)),
    run coin = some tape ->
    falseStatement coin tape ->
    CheckpointHistoryTranscript.Exact (checkpoint := checkpoint) tape ->
    intrinsicPcsMcaFailure coin

namespace HistoryExecutionLane

abbrev BoundLane (checkpoint : BoundCheckpoint) := HistoryExecutionLane
  (ell := ell) (m := m) (n := n)
  (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

abbrev Tape {checkpoint : BoundCheckpoint} (lane : BoundLane checkpoint) :=
  CheckpointHistoryTranscript
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
  (checkpoint := checkpoint) (domain := lane.domain)
  (degree := lane.degree) (openedCount := lane.openedCount)

/-- An actual history false acceptance: one tape was returned and the
semantic false-statement predicate holds. -/
def FalseAccept {checkpoint : BoundCheckpoint} (lane : BoundLane checkpoint)
    (coin : Coin) : Prop :=
  ∃ tape : Tape lane,
    lane.run coin = some tape ∧ lane.falseStatement coin tape

/-- Exact extracted history collision event, retaining the executed tape. -/
def CollisionEvent {checkpoint : BoundCheckpoint} (lane : BoundLane checkpoint)
    (coin : Coin) : Prop :=
  ∃ tape : Tape lane,
    lane.run coin = some tape ∧ lane.falseStatement coin tape ∧
    CheckpointHistoryTranscript.ExtractedHistoryCollision
      (ell := ell) (pcs := pcs) (checkpoint := checkpoint) tape

/-- Exact history-side oracle/transport event: the returned root has no
preimage attribution to the selected semantic checkpoint word. -/
def TransportEvent {checkpoint : BoundCheckpoint} (lane : BoundLane checkpoint)
    (coin : Coin) : Prop :=
  ∃ tape : Tape lane,
    lane.run coin = some tape ∧ lane.falseStatement coin tape ∧
    ¬tape.RootPreimage

/-- All history adapters are now proved.  Only
`intrinsicOfExecutedExact` is supplied by the future executable MCA
classifier. -/
theorem falseAccept_three_event_cover {checkpoint : BoundCheckpoint}
    (lane : BoundLane checkpoint) (coin : Coin)
    (accepted : lane.FalseAccept coin) :
    lane.intrinsicPcsMcaFailure coin ∨
      lane.CollisionEvent coin ∨ lane.TransportEvent coin := by
  obtain ⟨tape, executed, falseStatement⟩ := accepted
  rcases CheckpointHistoryTranscript.attribution_equivocation_or_exact
      checkpoint tape with missing | collision | exact
  · exact Or.inr (Or.inr ⟨tape, executed, falseStatement, missing⟩)
  · exact Or.inr (Or.inl ⟨tape, executed, falseStatement, collision⟩)
  · exact Or.inl
      (lane.intrinsicOfExecutedExact coin tape executed falseStatement exact)

end HistoryExecutionLane

/-! ## Exact prices and the one-coin four-event ledger -/

/-- Prices only the three exact history events.  This structure cannot alter
their predicates. -/
structure HistoryPriceCertificate {checkpoint : BoundCheckpoint}
    (lane : HistoryExecutionLane
      (ell := ell) (m := m) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint) where
  intrinsicPrice : Real
  intrinsicBound : uniformProb Coin lane.intrinsicPcsMcaFailure <= intrinsicPrice
  collisionPrice : Real
  collisionBound : uniformProb Coin lane.CollisionEvent <= collisionPrice
  transportPrice : Real
  transportBound : uniformProb Coin lane.TransportEvent <= transportPrice

inductive FailureClass where
  | historyPcsMca
  | additiveProximity
  | extractedCshakeCollision
  | oracleTransport
deriving DecidableEq, Fintype, Repr

local notation "ExactLedger" => FailureClass -> PricedFailure Coin

namespace LedgerOps

def Bad (ledger : ExactLedger) (coin : Coin) : Prop :=
  (ledger .historyPcsMca).event coin ∨
  (ledger .additiveProximity).event coin ∨
  (ledger .extractedCshakeCollision).event coin ∨
  (ledger .oracleTransport).event coin

def Price (ledger : ExactLedger) : Real :=
  (ledger .historyPcsMca).price +
  (ledger .additiveProximity).price +
  (ledger .extractedCshakeCollision).price +
  (ledger .oracleTransport).price

theorem bad_le_price (ledger : ExactLedger) :
    uniformProb Coin (Bad ledger) <= Price ledger := by
  have outer := uniformProb_or_le (ledger .historyPcsMca).event (fun coin =>
    (ledger .additiveProximity).event coin ∨
    (ledger .extractedCshakeCollision).event coin ∨
    (ledger .oracleTransport).event coin)
  have middle := uniformProb_or_le (ledger .additiveProximity).event (fun coin =>
    (ledger .extractedCshakeCollision).event coin ∨
    (ledger .oracleTransport).event coin)
  have inner := uniformProb_or_le
    (ledger .extractedCshakeCollision).event
    (ledger .oracleTransport).event
  unfold Bad Price
  linarith [(ledger .historyPcsMca).bound,
    (ledger .additiveProximity).bound,
    (ledger .extractedCshakeCollision).bound,
    (ledger .oracleTransport).bound]

end LedgerOps

def joinFailure (left right : PricedFailure Coin) : PricedFailure Coin where
  event := fun coin => left.event coin ∨ right.event coin
  price := left.price + right.price
  bound := by
    have union := uniformProb_or_le left.event right.event
    linarith [left.bound, right.bound]

/-- The final joint object.  `additiveExecutionNonempty` rules out a merely
vacuous family: at least one external coin reaches a Lean-accepted opaque-byte
raw controller execution. -/
structure JointGame (runner : Coin -> Runner) where
  checkpoint : BoundCheckpoint
  history : HistoryExecutionLane
    (ell := ell) (m := m) (n := n)
    (pcs := pcs) (statement := statement)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint
  historyPrices : HistoryPriceCertificate history
  additivePrices :
    Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.PriceCertificate
      (pcs := pcs) (statement := statement) (verifier := verifier)
      (request := request) runner
  additiveExecutionNonempty : ∃ coin,
    Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawFalseAcceptEvent
      additivePrices coin

namespace JointGame

abbrev BoundGame {runner : Coin -> Runner} := JointGame
  (ell := ell) (m := m) (queryCount := queryCount) (n := n)
  (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
  (Error := Error) (request := request) (verifier := verifier) runner

def historyFailure {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner)) :
    PricedFailure Coin where
  event := game.history.intrinsicPcsMcaFailure
  price := game.historyPrices.intrinsicPrice
  bound := game.historyPrices.intrinsicBound

def historyCollisionFailure {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner)) :
    PricedFailure Coin where
  event := game.history.CollisionEvent
  price := game.historyPrices.collisionPrice
  bound := game.historyPrices.collisionBound

def historyTransportFailure {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner)) :
    PricedFailure Coin where
  event := game.history.TransportEvent
  price := game.historyPrices.transportPrice
  bound := game.historyPrices.transportBound

def ledger {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner))
    (failure : FailureClass) : PricedFailure Coin :=
  match failure with
  | .historyPcsMca => historyFailure game
  | .additiveProximity =>
      Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawExactThreeLedger
        game.additivePrices
        Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.FailureClass.additiveProximity
  | .extractedCshakeCollision =>
      joinFailure
        (Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawExactThreeLedger
          game.additivePrices
          Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.FailureClass.extractedCshakeCollision)
        (historyCollisionFailure game)
  | .oracleTransport =>
      joinFailure
        (Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawExactThreeLedger
          game.additivePrices
          Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.FailureClass.oracleTransport)
        (historyTransportFailure game)

def FalseAccept {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner))
    (coin : Coin) : Prop :=
  game.history.FalseAccept coin ∨
    Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawFalseAcceptEvent
      game.additivePrices coin

theorem falseAccept_bad {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner))
    (coin : Coin) (accepted : FalseAccept game coin) :
    LedgerOps.Bad (ledger game) coin := by
  rcases accepted with historyAccepted | additiveAccepted
  · rcases game.history.falseAccept_three_event_cover coin historyAccepted with
      intrinsic | collision | transport
    · exact Or.inl intrinsic
    · exact Or.inr (Or.inr (Or.inl (Or.inr collision)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr transport)))
  · rcases
      Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.falseAccept_three_event_cover
        game.additivePrices coin additiveAccepted with
      proximity | collision | transport
    · exact Or.inr (Or.inl proximity)
    · exact Or.inr (Or.inr (Or.inl (Or.inl collision)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl transport)))

theorem falseAccept_le {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner)) :
    uniformProb Coin (FalseAccept game) <= LedgerOps.Price (ledger game) :=
  le_trans (uniformProb_mono (falseAccept_bad game))
    (LedgerOps.bad_le_price (ledger game))

theorem execution_nonempty {runner : Coin -> Runner}
    (game : BoundGame
      (ell := ell) (m := m) (queryCount := queryCount) (n := n)
      (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (Error := Error) (request := request) (verifier := verifier)
      (runner := runner)) :
    ∃ coin,
      Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.rawFalseAcceptEvent
        game.additivePrices coin :=
  game.additiveExecutionNonempty

end JointGame

/-! ## Closed accepted byte-bound execution witness -/

namespace Bootstrap

local notation "BootstrapCoin" => IdealCoin
  Minidregg.Compiler.Tower256AdditiveFriRawDeployment.bootstrapStatement

def coin : BootstrapCoin :=
  (fun i => i.elim0, fun i => i.elim0)

def runner : BootstrapCoin ->
    Minidregg.Compiler.Tower256AdditiveFriRawController.OpaqueProofRunner Unit :=
  fun _ => Minidregg.Compiler.Tower256AdditiveFriRawDeployment.honestRunner

/-- The exact execution function used by the joint game is genuinely
inhabited at the opaque byte boundary. -/
theorem execute_nonempty (request : List UInt8) :
    ∃ reply,
      Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.execute
        (pcs := Minidregg.Compiler.Tower256AdditiveFriRawDeployment.OneRoundPcs)
        (statement :=
          Minidregg.Compiler.Tower256AdditiveFriRawDeployment.bootstrapStatement)
        (verifier :=
          Minidregg.Compiler.Tower256AdditiveFriRawDeployment.verifier)
        (request := request) runner coin = some reply := by
  obtain ⟨reply, succeeded⟩ :=
    Minidregg.Compiler.Tower256AdditiveFriRawDeployment.honest_run_succeeds request
  refine ⟨reply, ?_⟩
  apply
    (Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.execute_eq_some_iff
      (pcs := Minidregg.Compiler.Tower256AdditiveFriRawDeployment.OneRoundPcs)
      (statement :=
        Minidregg.Compiler.Tower256AdditiveFriRawDeployment.bootstrapStatement)
      (verifier :=
        Minidregg.Compiler.Tower256AdditiveFriRawDeployment.verifier)
      (request := request) runner coin reply).2
  simpa [runner] using succeeded

end Bootstrap

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame.HistoryExecutionLane.falseAccept_three_event_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms HistoryExecutionLane.falseAccept_three_event_cover
/-- info: 'Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame.JointGame.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms JointGame.falseAccept_le
/-- info: 'Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame.Bootstrap.execute_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Bootstrap.execute_nonempty

end

end Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame
