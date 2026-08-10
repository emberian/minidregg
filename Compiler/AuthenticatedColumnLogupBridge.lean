/-
# Compiler.AuthenticatedColumnLogupBridge -- accepted control discharges LogUp semantics

This is the first consumer of `AuthenticatedColumnPlan`'s proof-relevant
terminal statement.  It replaces LogUp's former caller timestamps with the
actual first challenge record and its append-only committed-root prefix.

An accepted controller attestation supplies canonical address linkage,
the Tower arithmetic equality, and exact semantic/root bindings through its
reflected final proposition.  The resulting object is fed directly into the
existing `Logup256ReceiptClause.indexedTableReceiptClause`; no lookup relation
or verifier is restated here.

PCS semantic soundness, commitment binding/collision resistance, and the
Fiat--Shamir random-oracle reduction remain explicit security premises.  The
bridge deliberately closes only facts which an accepted Lean controller can
actually carry.
-/

import Compiler.AuthenticatedColumnPlan
import Compiler.Logup256ReceiptClause

namespace Minidregg.Compiler.AuthenticatedColumnLogupBridge

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Loom

set_option autoImplicit false

universe u

variable {F : Type*} [Field F] [CharP F 2]
variable {κ : Type u} [Fintype κ]
variable {k : Nat}

/-! ## Exact roots committed before the first challenge -/

/-- The four roots consumed by the semantic LogUp clause, with their values
fixed to the exact trace and claim.  Slot metadata remains in each
`RootRecord`; this object does not identify unlike column roles. -/
structure RequiredRoots
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k) where
  semanticTrace : RootRecord
  address : RootRecord
  weights : RootRecord
  table : RootRecord
  semanticTraceExact : semanticTrace.root = trace.semanticTraceRoot
  addressExact : address.root = claim.addressRoot
  weightsExact : weights.root = claim.weightsRoot
  tableExact : table.root = claim.tableRoot

def RequiredRoots.records
    {trace : CommittedSemanticTrace κ k}
    {claim : IndexedTableReceiptClaim F κ k}
    (required : RequiredRoots trace claim) : List RootRecord :=
  [required.semanticTrace, required.address, required.weights, required.table]

/-- The exact roots-before-challenges predicate.  The first draw carries the
number of roots present when it was derived, and every required LogUp root is
in that prefix of the accepted trace's append-only root list. -/
structure RootPrefixSchedule
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges)
    {trace : CommittedSemanticTrace κ k}
    {claim : IndexedTableReceiptClaim F κ k}
    (required : RequiredRoots trace claim) : Type where
  firstDraw : DrawRecord
  drawPresent : firstDraw ∈ draws
  transcriptDomainExact : firstDraw.label.transcriptDomain = transcriptDomain
  roundChallengeExact : firstDraw.label.role = .roundChallenge
  firstOrdinal : firstDraw.label.ordinal = 0
  requiredBefore : ∀ record, record ∈ required.records ->
    record ∈ roots.take firstDraw.priorRootCount

namespace RootPrefixSchedule

variable
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    {attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges}
    {trace : CommittedSemanticTrace κ k}
    {claim : IndexedTableReceiptClaim F κ k}
    {required : RequiredRoots trace claim}

/-- The authenticated prefix count cannot exceed the final root list. -/
theorem priorRootCount_le (schedule : RootPrefixSchedule attestation required) :
    schedule.firstDraw.priorRootCount ≤ roots.length :=
  attestation.trace.draw_priorRootCount_le
    schedule.firstDraw schedule.drawPresent

/-- Every root required by the LogUp statement is literally present in the
accepted trace, not only named by a root digest outside it. -/
theorem required_present (schedule : RootPrefixSchedule attestation required)
    {record : RootRecord} (member : record ∈ required.records) :
    record ∈ roots :=
  List.mem_of_mem_take (schedule.requiredBefore record member)

/-- A missing committed root makes the schedule uninhabitable.  This is the
load-bearing tooth replacing the old free timestamp inequality. -/
theorem no_schedule_of_required_missing
    {record : RootRecord} (member : record ∈ required.records)
    (missing : ∀ draw ∈ draws,
      record ∉ roots.take draw.priorRootCount) :
    ¬ Nonempty (RootPrefixSchedule attestation required) := by
  rintro ⟨schedule⟩
  exact missing schedule.firstDraw schedule.drawPresent
    (schedule.requiredBefore record member)

end RootPrefixSchedule

/-! ## Reflected terminal semantics -/

/-- The proposition selected by the Lean-authored LogUp final checker.  These
are precisely the semantic facts which a successful controller can decide;
cryptographic security games remain outside it. -/
structure LogupFinalStatement
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k) : Prop where
  canonicalAddressLinked : CanonicalAddressLinked trace
  towerArithmetic :
    claim.claimedEvaluation =
      logupDot claim.table (committedIncidencePushforward trace claim.weights)
  pcsRootsBound :
    claim.addressRoot = trace.addressRoot ∧
    claim.weightsRoot = trace.weightsRoot ∧
    claim.tableRoot = trace.tableRoot
  semanticTraceRootBound : claim.semanticTraceRoot = trace.semanticTraceRoot

/-- The schedule predicate supplied to the semantic clause is indexed by the
expected claim and trace.  Another claim cannot reuse this controller run. -/
def ControllerTranscriptSchedule
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges)
    (expectedTrace : CommittedSemanticTrace κ k)
    (expectedClaim : IndexedTableReceiptClaim F κ k)
    (required : RequiredRoots expectedTrace expectedClaim)
    (candidateClaim : IndexedTableReceiptClaim F κ k)
    (candidateTrace : CommittedSemanticTrace κ k) : Prop :=
  candidateClaim = expectedClaim ∧ candidateTrace = expectedTrace ∧
    Nonempty (RootPrefixSchedule attestation required)

/-- One accepted controller run plus only the security premises not derivable
from local execution.  `finalStatementExact` binds the retained checker
proposition to this exact LogUp claim and trace. -/
structure AcceptedLogupRun
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges)
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k)
    (required : RequiredRoots trace claim)
    (PCSOpeningSound : IndexedTableReceiptClaim F κ k ->
      CommittedSemanticTrace κ k -> Prop)
    (CommitmentBindingCR : IndexedTableReceiptClaim F κ k ->
      CommittedSemanticTrace κ k -> Prop)
    (RandomOracleModel : IndexedTableReceiptClaim F κ k -> Prop) : Type where
  finalStatementExact :
    attestation.FinalStatement <-> LogupFinalStatement trace claim
  rootSchedule : RootPrefixSchedule attestation required
  tower256Cardinality : Nat.card F = 2 ^ 256
  pcsOpeningSound : PCSOpeningSound claim trace
  commitmentBindingCR : CommitmentBindingCR claim trace
  fiatShamirROM : RandomOracleModel claim

namespace AcceptedLogupRun

variable
    {State : Type} {portal : GlobalTranscriptPortal State}
    {transcriptDomain : Digest}
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    {attestation : TerminalAttestation portal transcriptDomain
      roots draws native openings edges}
    {trace : CommittedSemanticTrace κ k}
    {claim : IndexedTableReceiptClaim F κ k}
    {required : RequiredRoots trace claim}
    {PCSOpeningSound : IndexedTableReceiptClaim F κ k ->
      CommittedSemanticTrace κ k -> Prop}
    {CommitmentBindingCR : IndexedTableReceiptClaim F κ k ->
      CommittedSemanticTrace κ k -> Prop}
    {RandomOracleModel : IndexedTableReceiptClaim F κ k -> Prop}

local notation "Schedule" =>
  ControllerTranscriptSchedule attestation trace claim required

/-- The accepted Boolean now exposes the exact semantic statement selected by
the controller, rather than an untyped success flag. -/
theorem controllerStatement
    (accepted : AcceptedLogupRun attestation trace claim required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel) :
    LogupFinalStatement trace claim :=
  accepted.finalStatementExact.mp attestation.finalStatement_proved

/-- Assemble the existing LogUp boundary from the accepted controller trace
and the still-explicit cryptographic premises. -/
def towerPremises
    (accepted : AcceptedLogupRun attestation trace claim required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel) :
    Tower256ClausePremises trace claim PCSOpeningSound Schedule
      CommitmentBindingCR RandomOracleModel where
  tower256Characteristic := inferInstance
  tower256Cardinality := accepted.tower256Cardinality
  tower256Arithmetic := accepted.controllerStatement.towerArithmetic
  pcsOpeningSound := accepted.pcsOpeningSound
  pcsRootsBound := accepted.controllerStatement.pcsRootsBound
  transcriptOrdered := ⟨rfl, rfl, ⟨accepted.rootSchedule⟩⟩
  commitmentBindingCR := accepted.commitmentBindingCR
  semanticTraceRootBound := accepted.controllerStatement.semanticTraceRootBound
  fiatShamirROM := accepted.fiatShamirROM

/-- Main join: one accepted authenticated-column run reaches the already
proved exact indexed-evaluation conclusion. -/
theorem indexedTableReceiptClause_of_attestation
    (accepted : AcceptedLogupRun attestation trace claim required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel) :
    IndexedTableClauseConclusion trace claim PCSOpeningSound Schedule
      CommitmentBindingCR RandomOracleModel :=
  indexedTableReceiptClause trace claim PCSOpeningSound Schedule
    CommitmentBindingCR RandomOracleModel
    accepted.controllerStatement.canonicalAddressLinked
    accepted.towerPremises

/-- Consumer-facing exact table-read equation. -/
theorem indexedEvaluation_of_attestation
    (accepted : AcceptedLogupRun attestation trace claim required
      PCSOpeningSound CommitmentBindingCR RandomOracleModel) :
    claim.claimedEvaluation =
      logupDot (fun row => claim.table (trace.index row)) claim.weights :=
  accepted.indexedTableReceiptClause_of_attestation.indexedEvaluation

end AcceptedLogupRun

/-- info: 'Minidregg.Compiler.AuthenticatedColumnLogupBridge.RootPrefixSchedule.priorRootCount_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootPrefixSchedule.priorRootCount_le
/-- info: 'Minidregg.Compiler.AuthenticatedColumnLogupBridge.RootPrefixSchedule.no_schedule_of_required_missing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootPrefixSchedule.no_schedule_of_required_missing
/-- info: 'Minidregg.Compiler.AuthenticatedColumnLogupBridge.AcceptedLogupRun.controllerStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedLogupRun.controllerStatement
/-- info: 'Minidregg.Compiler.AuthenticatedColumnLogupBridge.AcceptedLogupRun.indexedTableReceiptClause_of_attestation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedLogupRun.indexedTableReceiptClause_of_attestation

end Minidregg.Compiler.AuthenticatedColumnLogupBridge
