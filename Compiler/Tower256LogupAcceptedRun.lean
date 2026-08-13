/-
# Compiler.Tower256LogupAcceptedRun -- eliminate the concrete controller trace

The Tower256 LogUp plan fixes the semantic roots, transcript order, native-call
positions, openings, and terminal proposition.  This module gives plans a
generic structural terminal certificate, proves that every verified execution
retains its certificate, and instantiates that theorem for the concrete LogUp
schedule.  Only the genuinely cryptographic PCS, commitment-binding, and
random-oracle judgments remain as inputs.

No native implementation semantics occur here.  Native runners remain opaque,
fallible byte producers; their only successful path is the existing Lean check.
-/

import Compiler.Tower256LogupControllerPlan

namespace Minidregg.Compiler.Tower256LogupAcceptedRun

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256LogupControllerPlan
open Minidregg.Selvage

set_option autoImplicit false

variable {F : Type} [Field F] [CharP F 2]
variable {rowLog tableLog checkpointLog : Nat}

/-! ## A reusable structural terminal certificate -/

/-- A proposition/type family holds at every syntactic terminal of a plan.
Challenge continuations are quantified over every Lean-derived coin. -/
def AllTerminals {transcriptDomain : Minidregg.Theory.TypedAuthorization.Digest}
    {phase : Phase} (plan : Plan transcriptDomain phase)
    (P : (ledger : Ledger) -> FinalChecker ledger -> Prop) : Prop :=
  match plan with
  | .bindPublic _ next => AllTerminals next P
  | .bindFirstRoot _ next => AllTerminals next P
  | .bindAdditionalRoot _ next => AllTerminals next P
  | .drawRound next => (coin : _) -> AllTerminals (next coin) P
  | .runRoundNative _ next => AllTerminals next P
  | .bindNextRoundRoot _ next => AllTerminals next P
  | .drawQuery next => (coin : _) -> AllTerminals (next coin) P
  | .runQueryNative _ next => AllTerminals next P
  | .bindFirstOpening _ _ next => AllTerminals next P
  | .bindAdditionalOpening _ _ next => AllTerminals next P
  | .bindReprEq _ _ _ next => AllTerminals next P
  | .finalize checker => P _ checker

/-- Generic elimination: if a plan is structurally certified, every actual
verified outcome carries the terminal certificate.  Blocked and rejected
native paths are impossible under the supplied equality. -/
theorem terminalFactsOfVerified
    {Error State : Type}
    {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Minidregg.Theory.TypedAuthorization.Digest}
    {phase : Phase} (runner : NativeRunner Error)
    (plan : Plan transcriptDomain phase)
    (state : RuntimeState portal transcriptDomain phase.ledger)
    (P : (ledger : Ledger) -> FinalChecker ledger -> Prop)
    (certificate : AllTerminals plan P)
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges)
    (resultExact : run portal runner transcriptDomain plan state =
      .verified attestation) :
    P ⟨roots, draws, native, openings, edges⟩ attestation.checker := by
  induction plan generalizing roots draws native openings edges with
  | bindPublic context next ih =>
      exact ih _ certificate attestation resultExact
  | bindFirstRoot column next ih =>
      exact ih _ certificate attestation resultExact
  | bindAdditionalRoot column next ih =>
      exact ih _ certificate attestation resultExact
  | drawRound next ih =>
      exact ih _ _ (certificate _) attestation resultExact
  | runRoundNative call next ih =>
      simp only [run] at resultExact
      split at resultExact
      · cases resultExact
      · split at resultExact
        · exact ih _ certificate attestation resultExact
        · cases resultExact
  | bindNextRoundRoot column next ih =>
      exact ih _ certificate attestation resultExact
  | drawQuery next ih =>
      exact ih _ _ (certificate _) attestation resultExact
  | runQueryNative call next ih =>
      simp only [run] at resultExact
      split at resultExact
      · cases resultExact
      · split at resultExact
        · exact ih _ certificate attestation resultExact
        · cases resultExact
  | bindFirstOpening opening rootPresent next ih =>
      exact ih _ certificate attestation resultExact
  | bindAdditionalOpening opening rootPresent next ih =>
      exact ih _ certificate attestation resultExact
  | bindReprEq edge sourcePresent targetPresent next ih =>
      exact ih _ certificate attestation resultExact
  | finalize checker =>
      simp only [run] at resultExact
      split at resultExact
      · cases resultExact
        exact certificate
      · cases resultExact

/-! ## Static LogUp terminal facts -/

/-- Root-prefix data stated only over a terminal ledger. -/
structure StaticRootPrefix
    (transcriptDomain : Minidregg.Theory.TypedAuthorization.Digest)
    (ledger : Ledger)
    {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
    {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog}
    (required : RequiredRoots trace claim) : Prop where
  drawsNonempty : ledger.draws ≠ []
  transcriptDomainExact :
    (ledger.draws.head drawsNonempty).label.transcriptDomain = transcriptDomain
  roundChallengeExact :
    (ledger.draws.head drawsNonempty).label.role = .roundChallenge
  firstOrdinal : (ledger.draws.head drawsNonempty).label.ordinal = 0
  requiredBefore : forall record, record ∈ required.records ->
    record ∈ ledger.roots.take
      (ledger.draws.head drawsNonempty).priorRootCount

/-- Replace the harmless domain-polymorphic equation above with the actual
controller domain when converting a certified plan terminal. -/
def StaticRootPrefix.toSchedule
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Minidregg.Theory.TypedAuthorization.Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
    {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog}
    {required : RequiredRoots trace claim}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges)
    (facts : StaticRootPrefix transcriptDomain
      ⟨roots, draws, native, openings, edges⟩ required) :
    RootPrefixSchedule attestation required where
  firstDraw := draws.head facts.drawsNonempty
  drawPresent := List.head_mem facts.drawsNonempty
  transcriptDomainExact := facts.transcriptDomainExact
  roundChallengeExact := facts.roundChallengeExact
  firstOrdinal := facts.firstOrdinal
  requiredBefore := facts.requiredBefore

structure StaticTerminalFacts
    (transcriptDomain : Minidregg.Theory.TypedAuthorization.Digest)
    (ledger : Ledger) (checker : FinalChecker ledger)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog)
    (required : RequiredRoots trace claim) : Prop where
  finalStatementExact : checker.Statement <-> LogupFinalStatement trace claim
  rootPrefix : StaticRootPrefix transcriptDomain ledger required

/-! ## Concrete plan certificate and execution elimination -/

variable {backend : Backend F}
variable {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
variable {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog}
variable {inputs : ControllerInputs (checkpointLog := checkpointLog)
  backend trace claim}
variable [Decidable (LogupFinalStatement trace claim)]

/-- The exact plan has four required roots before its first round draw and the
literal reflected LogUp checker at every terminal. -/
def planCertificate :
    AllTerminals inputs.plan (fun ledger checker =>
      StaticTerminalFacts inputs.transcriptDomain ledger checker trace claim
        inputs.columns.required) := by
  simp only [ControllerInputs.plan, AllTerminals]
  intro roundCoin queryCoin
  refine
    { finalStatementExact := Iff.rfl
      rootPrefix :=
        { drawsNonempty := ?_
          transcriptDomainExact := ?_
          roundChallengeExact := rfl
          firstOrdinal := rfl
          requiredBefore := ?_ } }
  · simp [Ledger.empty, Ledger.addRoot, Ledger.addDraw, Ledger.addNative,
      Ledger.addOpening]
  · simp [Ledger.empty, Ledger.addRoot, Ledger.addDraw, Ledger.addNative,
      Ledger.addOpening]
  · intro record member
    simp only [RequiredRoots.records, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with h | h | h | h
    all_goals subst record
    all_goals
      simp [LogupColumns.required, AdditiveColumn.rootRecord, Ledger.empty,
        Ledger.addRoot, Ledger.addDraw, Ledger.addNative, Ledger.addOpening]

/-- Proof-relevant evidence that the exact generated controller returned one
particular terminal attestation. -/
structure VerifiedExecution
    {Error : Type}
    (backend : Backend F)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog)
    (inputs : ControllerInputs (checkpointLog := checkpointLog)
      backend trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (runner : NativeRunner Error) (seed : List UInt8) where
  roots : List RootRecord
  draws : List DrawRecord
  native : List NativeRecord
  openings : List OpeningRecord
  edges : List ReprEqRecord
  attestation : TerminalAttestation backend.transcript.portal
    inputs.transcriptDomain roots draws native openings edges
  resultExact : inputs.execute runner seed = .verified attestation

namespace VerifiedExecution

variable {Error : Type} {runner : NativeRunner Error} {seed : List UInt8}

def staticFacts
    (execution : VerifiedExecution backend trace claim inputs runner seed) :
    StaticTerminalFacts
      inputs.transcriptDomain
      ⟨execution.roots, execution.draws, execution.native,
        execution.openings, execution.edges⟩
      execution.attestation.checker trace claim inputs.columns.required :=
  terminalFactsOfVerified runner inputs.plan
    (RuntimeState.initial backend.transcript.portal inputs.transcriptDomain seed)
    _ planCertificate execution.attestation execution.resultExact

def rootSchedule
    (execution : VerifiedExecution backend trace claim inputs runner seed) :
    RootPrefixSchedule execution.attestation inputs.columns.required :=
  execution.staticFacts.rootPrefix.toSchedule execution.attestation

def acceptedLogupRun
    (execution : VerifiedExecution backend trace claim inputs runner seed)
    (PCSOpeningSound : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog -> Prop)
    (CommitmentBindingCR :
      IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog -> Prop)
    (RandomOracleModel :
      IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog -> Prop)
    (pcsOpeningSound : PCSOpeningSound claim trace)
    (commitmentBindingCR : CommitmentBindingCR claim trace)
    (fiatShamirROM : RandomOracleModel claim) :
    AcceptedLogupRun execution.attestation trace claim inputs.columns.required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel where
  finalStatementExact := execution.staticFacts.finalStatementExact
  rootSchedule := execution.rootSchedule
  tower256Cardinality := backend.tower.cardinality
  pcsOpeningSound := pcsOpeningSound
  commitmentBindingCR := commitmentBindingCR
  fiatShamirROM := fiatShamirROM

theorem indexedEvaluation
    (execution : VerifiedExecution backend trace claim inputs runner seed)
    (PCSOpeningSound : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog -> Prop)
    (CommitmentBindingCR :
      IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog ->
      CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog -> Prop)
    (RandomOracleModel :
      IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog -> Prop)
    (pcsOpeningSound : PCSOpeningSound claim trace)
    (commitmentBindingCR : CommitmentBindingCR claim trace)
    (fiatShamirROM : RandomOracleModel claim) :
    claim.claimedEvaluation =
      logupDot (fun row => claim.table (trace.index row)) claim.weights :=
  (execution.acceptedLogupRun PCSOpeningSound CommitmentBindingCR
    RandomOracleModel pcsOpeningSound commitmentBindingCR
    fiatShamirROM).indexedEvaluation_of_attestation

end VerifiedExecution

/-- info: 'Minidregg.Compiler.Tower256LogupAcceptedRun.terminalFactsOfVerified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms terminalFactsOfVerified
/-- info: 'Minidregg.Compiler.Tower256LogupAcceptedRun.VerifiedExecution.indexedEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms VerifiedExecution.indexedEvaluation

end Minidregg.Compiler.Tower256LogupAcceptedRun
