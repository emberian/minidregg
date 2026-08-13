/-
# Assurance.Tower256RawHistoryFsExecution -- raw FS execution is the history lane

This module removes `HistoryExecutionLane.intrinsicOfExecutedExact` as a
caller-supplied semantic classifier.  The replacement predicate is the literal
state-restoration Fiat--Shamir false-acceptance event for the checkpoint's
binding-free BCS reduction: scoped statement, failed relaxed source extraction,
successful raw verifier, and accepted relaxed target witness, all on the
`srTrace`/`srFinalChal` coin pair owned by the controller.

An opaque native run can contribute to that event only after
`Tower256RawHistoryFsController` decodes its bytes and proves equality with the
literal SR trace and oracle realization.  The resulting history tape is the
accepted `SrOutput` message family itself.  Thus the intrinsic branch in the
canonical three-way history split is now constructed, while the PCS/MCA price,
the exact common/native coin transport, raw Merkle/cSHAKE collision price, and
root-attribution/ROM price remain separate, exact predicates.
-/

import Assurance.RawHistorySecurityPrices
import Assurance.Tower256RawHistoryFsController

namespace Minidregg.Assurance.Tower256RawHistoryFsExecution

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.RawHistoryBcsOpenings
open Minidregg.Assurance.RawHistorySecurityPrices
open Minidregg.Assurance.RawSemanticHistoryCheckpointGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Assurance.Tower256RawHistoryFsController
open Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField :=
  Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m n : Nat}
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

local notation "Coin" => IdealCoin statement
local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
local notation "BoundSpec" checkpoint =>
  Tower256RawHistoryFsController.Spec
    (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

/-! ## The literal native SR/FS failure predicate -/

/-- Exact extraction semantics for one raw history FS instance.  This object
does not choose a common-game predicate: it fixes the statement scope,
relaxation radius, and straightline extractor consumed by the already-defined
SR/FS event. -/
structure ExtractionPlan {checkpoint : BoundCheckpoint}
    (spec : BoundSpec checkpoint) (oracle : OraclePlan spec) where
  statementSet : Set (Stmt spec.reduction)
  delta : Real
  deltaInterior : delta ∈ Set.Ioo (0 : Real) spec.reduction.δstar
  extractor : SrExtractor spec.reduction oracle.saltBudget

namespace ExtractionPlan

/-- The exact Def-B.2 failure event for the raw checkpoint reduction.  No
`Coin -> Prop` argument occurs anywhere in its definition. -/
def NativeFalseAccept {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    (extraction : ExtractionPlan spec oracle)
    (coins : NativeFsCoins TowerField oracle.queryBudget spec.reduction.k) : Prop :=
  let log := srTrace oracle.prover coins.1
  let output := oracle.prover.out (log.map Prod.snd)
  let challenges : Fin spec.reduction.k -> spec.reduction.Chal :=
    srFinalChal oracle.prover coins.1 coins.2
  output.stmt ∈ extraction.statementSet ∧
    ¬RelaxedMem spec.reduction.R extraction.delta output.stmt.idx
      output.stmt.x output.stmt.y
      (extraction.extractor output challenges log) ∧
    ∃ (x' : spec.reduction.X')
        (y' : Fin spec.reduction.n' -> spec.reduction.A'),
      fiatShamir spec.reduction oracle.saltBudget
          (fsOracle output challenges) output = some (x', y') ∧
        RelaxedMem spec.reduction.R' extraction.delta output.stmt.idx
          x' y' output.w'

/-- The exact native event evaluated on the controller's two projections from
the common additive/history coin. -/
def CommonFalseAccept {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    (extraction : ExtractionPlan spec oracle) (coin : Coin) : Prop :=
  extraction.NativeFalseAccept
    (oracle.queryCoins coin, oracle.finalCoins coin)

/-- Select exactly the salt-specialized extractor promised by the native
straightline Fiat--Shamir theorem.  The theorem remains an explicit premise:
this constructor does not smuggle a PCS theorem or a deployment event into the
execution bridge. -/
noncomputable def ofSoundness {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    (statementSet : Set (Stmt spec.reduction))
    (epsilon : Nat → Nat → Real → Real)
    (sound : FsStraightlineKnowledgeSoundness spec.reduction statementSet epsilon)
    (delta : Real)
    (deltaInterior : delta ∈ Set.Ioo (0 : Real) spec.reduction.δstar) :
    ExtractionPlan spec oracle where
  statementSet := statementSet
  delta := delta
  deltaInterior := deltaInterior
  extractor := Classical.choose sound oracle.saltBudget

end ExtractionPlan

/-! ## Actual opaque execution and its history tape -/

namespace Execution

/-- Retain only successful Lean-reflected executions. -/
def accepted {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    {oracle : OraclePlan spec} {verifier : Verifier spec oracle}
    {Error : Type} (runner : OpaqueRunner Error) (payload : List UInt8)
    (coin : Coin) :
    Option (AcceptedExecution spec oracle verifier coin payload) :=
  match Tower256RawHistoryFsController.run verifier runner coin payload with
  | .ok result => some result
  | .error _ => none

/-- The actual raw history lane: successful executions project their accepted
`SrOutput` messages to the checkpoint tape; failures return no tape. -/
def historyRun {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    {oracle : OraclePlan spec} {verifier : Verifier spec oracle}
    {Error : Type} (runner : OpaqueRunner Error) (payload : List UInt8)
    (coin : Coin) : Option (CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := spec.domain)
      (degree := spec.degree) (openedCount := spec.openedCount)) :=
  (accepted (oracle := oracle) (verifier := verifier) runner payload coin).map
    (fun result => result.tape)

theorem historyRun_eq_some_iff {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8) (coin : Coin)
    (tape : CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := spec.domain)
      (degree := spec.degree) (openedCount := spec.openedCount)) :
    historyRun (oracle := oracle) (verifier := verifier) runner payload coin =
        some tape ↔
      ∃ result : AcceptedExecution spec oracle verifier coin payload,
        accepted (oracle := oracle) (verifier := verifier) runner payload coin =
          some result ∧
        result.tape = tape := by
  unfold historyRun
  exact Option.map_eq_some_iff

end Execution

/-! ## The constructed canonical history lane -/

/-- A semantic false statement is now tied to an actually accepted opaque
execution, its exact projected tape, and the literal native SR/FS failure
event.  It cannot be independently selected by a caller. -/
def ExecutedFalseStatement {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (coin : Coin)
    (tape : CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := spec.domain)
      (degree := spec.degree) (openedCount := spec.openedCount)) : Prop :=
  ∃ accepted : AcceptedExecution spec oracle verifier coin payload,
    Execution.accepted (oracle := oracle) (verifier := verifier)
      runner payload coin = some accepted ∧
    accepted.tape = tape ∧
    extraction.CommonFalseAccept coin

/-- The formerly abstract history execution lane, built directly from the raw
controller and literal SR/FS failure event.  The proof of
`intrinsicOfExecutedExact` contains no classifier hypothesis. -/
def historyLane {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) :
    HistoryExecutionLane
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint where
  domain := spec.domain
  degree := spec.degree
  openedCount := spec.openedCount
  run := Execution.historyRun (oracle := oracle) (verifier := verifier)
    runner payload
  falseStatement := ExecutedFalseStatement (verifier := verifier)
    runner payload extraction
  intrinsicPcsMcaFailure := extraction.CommonFalseAccept
  intrinsicOfExecutedExact := by
    intro coin tape _executed falseStatement _exact
    rcases falseStatement with ⟨_accepted, _executed, _tapeExact, intrinsic⟩
    exact intrinsic

@[simp] theorem historyLane_run {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (coin : Coin) :
    (historyLane (verifier := verifier) runner payload extraction).run coin =
      Execution.historyRun (oracle := oracle) (verifier := verifier)
        runner payload coin := rfl

/-- The exact former seam is now a theorem of the constructed lane. -/
theorem intrinsic_of_executed_exact {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (coin : Coin)
    (tape : CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := spec.domain)
      (degree := spec.degree) (openedCount := spec.openedCount))
    (executed : (historyLane (verifier := verifier) runner payload extraction).run
      coin = some tape)
    (falseStatement :
      (historyLane (verifier := verifier) runner payload extraction).falseStatement
        coin tape)
    (exact : CheckpointHistoryTranscript.Exact
      (checkpoint := checkpoint) tape) :
    (historyLane (verifier := verifier) runner payload extraction).intrinsicPcsMcaFailure
      coin :=
  (historyLane (verifier := verifier) runner payload extraction).intrinsicOfExecutedExact
    coin tape executed falseStatement exact

/-! ## Exact prices, still explicit -/

/-- A price for the literal native event.  This is not a free common-game
bound: transport to the common coin requires `NativeFsCoinRealization`. -/
structure NativeMcaPrice {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    (extraction : ExtractionPlan spec oracle) where
  price : Real
  nativeBound : uniformProb
      (NativeFsCoins TowerField oracle.queryBudget spec.reduction.k)
      extraction.NativeFalseAccept <= price

namespace NativeMcaPrice

/-- The exact native MCA/FS price obtained from the literal
`FsStraightlineKnowledgeSoundness` predicate for this raw reduction and this
controller-owned prover/query budget. -/
noncomputable def ofSoundness {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    (statementSet : Set (Stmt spec.reduction))
    (epsilon : Nat → Nat → Real → Real)
    (sound : FsStraightlineKnowledgeSoundness spec.reduction statementSet epsilon)
    (delta : Real)
    (deltaInterior : delta ∈ Set.Ioo (0 : Real) spec.reduction.δstar) :
    NativeMcaPrice
      (ExtractionPlan.ofSoundness (oracle := oracle)
        statementSet epsilon sound delta deltaInterior) where
  price := epsilon oracle.saltBudget oracle.queryBudget delta
  nativeBound := by
    have native := Classical.choose_spec sound oracle.saltBudget
      oracle.queryBudget delta deltaInterior oracle.prover
    simpa [ExtractionPlan.NativeFalseAccept, ExtractionPlan.ofSoundness] using native

/-- Exact uniform realization transports the exact native price to the
constructed lane's intrinsic predicate. -/
theorem commonBound {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {extraction : ExtractionPlan spec oracle}
    (priced : NativeMcaPrice extraction)
    (realization : NativeFsCoinRealization Coin TowerField
      oracle.queryBudget spec.reduction.k)
    (queryExact : realization.queryCoins = oracle.queryCoins)
    (finalExact : realization.finalCoins = oracle.finalCoins) :
    uniformProb Coin extraction.CommonFalseAccept <= priced.price := by
  change uniformProb Coin (fun coin => extraction.NativeFalseAccept
    (oracle.queryCoins coin, oracle.finalCoins coin)) <= priced.price
  rw [← queryExact, ← finalExact]
  exact realization.event_le_of_native
    extraction.NativeFalseAccept priced.price priced.nativeBound

end NativeMcaPrice

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256RawHistoryFsExecution.intrinsic_of_executed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intrinsic_of_executed_exact
/-- info: 'Minidregg.Assurance.Tower256RawHistoryFsExecution.NativeMcaPrice.commonBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NativeMcaPrice.commonBound

end

end Minidregg.Assurance.Tower256RawHistoryFsExecution
