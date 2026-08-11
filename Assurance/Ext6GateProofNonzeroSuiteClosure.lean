/-
# Assurance.Ext6GateProofNonzeroSuiteClosure -- exact honest Ext6 closure seam

BFV384 and NoteSpend still derive zero proof-suite pins from their authorized
kernel requests, so their existing no-bound-suite theorems correctly prevent
semantic deployment.  Ext6 is the narrow honest nonzero candidate: its V1
suite/controller and codecs are assigned, its 23-residual five-round receipt
is accepted by a Lean Boolean checker, and the versioned endpoint rejects V0
and stale-codec requests before consulting proof bytes.

What remains unavailable is cryptographic authentication.  This module does
not manufacture it.  `SameCoinSecurity` is the smallest deployment carrier:
the existing eight-event `SecurityResidual` plus proof that this exact selected
coin is outside the ledger.  A semantic admitted receipt exists exactly when
that carrier is supplied.  The proof projects the controller acceptance and
then uses the explicit same-coin reductions; it cannot use the control-only
maximal-residual countermodel.
-/

import Assurance.Ext6GateProofDeploymentAdmission
import Compiler.Ext6GateProofVersionedDeployment

namespace Minidregg.Assurance.Ext6GateProofNonzeroSuiteClosure

open Minidregg.Assurance.Ext6GateProofControllerAdmission
open Minidregg.Assurance.Ext6GateProofDeploymentAdmission
open Minidregg.Compiler
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.Ext6GateProofDeployment
open Minidregg.Compiler.Ext6GateProofPositiveRun
open Minidregg.Compiler.Ext6GateProofVersionedDeployment
open Minidregg.Compiler.GateMleExt6
open Minidregg.Loom

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Closure

abbrev DeployedSuite := Minidregg.Compiler.Ext6GateProofDeployment.suite
abbrev DeployedStatement := Minidregg.Compiler.Ext6GateProofDeployment.statement
abbrev DeployedVerifier := Minidregg.Compiler.Ext6GateProofDeployment.verifier
abbrev Reply := AcceptedReceipt DeployedSuite DeployedStatement DeployedVerifier
  canonicalRequest

def execution : Unit → Option Reply := fun _ => some pinnedAcceptedReceipt

def runner : Unit → OpaqueProofRunner Unit := fun _ => pinnedHonestRunner

/-- Project the versioned endpoint's positive result into the generic
controller carrier used by the Ext6 reduction family.  The projection is
justified by `runPinned_success_integrity`; it does not discard the preceding
exact-request check. -/
noncomputable def control :
    Deployment.ControlledExecution Unit Unit canonicalRequest where
  execution := execution
  runner := runner
  executionExact := by
    intro omega reply selected
    cases omega
    have replyExact : reply = pinnedAcceptedReceipt := by
      simpa [execution] using (Option.some.inj selected).symm
    subst reply
    exact (runPinned_success_integrity pinnedHonestRunner canonicalRequest
      pinnedAcceptedReceipt pinned_honest_run_succeeds).2

@[simp] theorem control_selects :
    control.execution () = some pinnedAcceptedReceipt := rfl

/-- Controller closure includes all exact V1 request and receipt evidence, but
not authenticated-trace semantics. -/
theorem positive_control_exact :
    runPinned pinnedHonestRunner canonicalRequest = .ok pinnedAcceptedReceipt ∧
    control.runner () canonicalRequest = .ok pinnedAcceptedReceipt.proofBytes ∧
    DeployedVerifier.receiptCodec.decode pinnedAcceptedReceipt.proofBytes =
      some pinnedAcceptedReceipt.receipt ∧
    Accepts DeployedSuite DeployedStatement pinnedAcceptedReceipt.receipt := by
  refine ⟨pinned_honest_run_succeeds, ?_⟩
  exact Deployment.selected_control_evidence control control_selects

/-! ## The exact missing same-coin security carrier -/

/-- No security law is inferred from controller success.  A deployment must
supply all eight Ext6 reductions and prove their disjunction false on the
same `Unit` coin that selected the canonical receipt. -/
structure SameCoinSecurity where
  residual : Deployment.SecurityResidual Unit
  selectedGood : ¬ residual.ledger.Bad ()

theorem SameCoinSecurity.good
    (security : SameCoinSecurity) (failure : Ext6FailureClass) :
    security.residual.ledger.Good failure () :=
  security.residual.ledger.good_of_not_bad security.selectedGood failure

/-- A positive admitted receipt retains the supplied residual, the selected
coin, and the exact authenticated semantic witness derived from those laws. -/
structure PositiveAdmittedReceipt where
  security : SameCoinSecurity
  selected : control.execution () = some pinnedAcceptedReceipt
  trace : Nat → BabyBear
  authenticated : AuthenticatedTraceRelation DeployedStatement
    pinnedAcceptedReceipt.receipt trace
  descriptor : descriptorHolds DeployedStatement.descriptor trace

/-- The only constructor for the semantic receipt consumes the explicit
same-coin security carrier. -/
noncomputable def admitPositive
    (security : SameCoinSecurity) : PositiveAdmittedReceipt := by
  let semantic :=
    Deployment.selected_semantic_of_residual control security.residual
      control_selects security.selectedGood
  let trace := Classical.choose semantic
  have semanticExact := Classical.choose_spec semantic
  exact
    { security := security
      selected := control_selects
      trace := trace
      authenticated := semanticExact.1
      descriptor := semanticExact.2 }

/-- **Exact closure statement.** The nonzero, versioned positive receipt has
authenticated Ext6 semantics iff the eight-event same-coin carrier is
supplied.  The reverse direction does not recover laws from semantics; the
admitted object deliberately retains the laws that justified it. -/
theorem positive_admitted_iff_same_coin_security :
    Nonempty PositiveAdmittedReceipt ↔ Nonempty SameCoinSecurity := by
  constructor
  · rintro ⟨admitted⟩
    exact ⟨admitted.security⟩
  · rintro ⟨security⟩
    exact ⟨admitPositive security⟩

theorem admitted_has_exact_v1_pins (admitted : PositiveAdmittedReceipt) :
    deployedV1.proofSuiteId = suiteId ∧
    deployedV1.controllerId = controllerId ∧
    deployedV1.proofSuiteId ≠ ⟨0⟩ ∧
    deployedV1.controllerId ≠ ⟨0⟩ ∧
    control.execution () = some pinnedAcceptedReceipt := by
  exact ⟨rfl, rfl, suiteId_nonzero, controllerId_nonzero, admitted.selected⟩

theorem admitted_uses_selected_receipt (admitted : PositiveAdmittedReceipt) :
    runPinned pinnedHonestRunner canonicalRequest = .ok pinnedAcceptedReceipt ∧
    AuthenticatedTraceRelation DeployedStatement pinnedAcceptedReceipt.receipt
      admitted.trace ∧
    descriptorHolds DeployedStatement.descriptor admitted.trace :=
  ⟨pinned_honest_run_succeeds, admitted.authenticated, admitted.descriptor⟩

/-! ## Control-only and replay teeth -/

/-- The existing maximal residual marks every event certain, so it cannot
inhabit the selected-good field required by semantic closure. -/
theorem maximalResidual_selected_bad :
    (Deployment.maximalResidual Unit).ledger.Bad () := by
  exact Or.inl trivial

theorem maximalResidual_cannot_close :
    ¬∃ security : SameCoinSecurity,
      security.residual = Deployment.maximalResidual Unit := by
  rintro ⟨security, residualExact⟩
  have selectedGood := security.selectedGood
  rw [residualExact] at selectedGood
  exact selectedGood maximalResidual_selected_bad

theorem zero_pinned_receipt_cannot_replay :
    runPinned pinnedHonestRunner zeroPinnedRequest =
      .error (.wrongDeployment) :=
  zero_pinned_replay_rejected

theorem stale_codec_receipt_cannot_replay :
    runPinned pinnedHonestRunner staleCodecRequest =
      .error (.wrongDeployment) :=
  stale_codec_replay_rejected

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Ext6GateProofNonzeroSuiteClosure.Closure.positive_control_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_control_exact
/-- info: 'Minidregg.Assurance.Ext6GateProofNonzeroSuiteClosure.Closure.admitPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitPositive
/-- info: 'Minidregg.Assurance.Ext6GateProofNonzeroSuiteClosure.Closure.positive_admitted_iff_same_coin_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_admitted_iff_same_coin_security

end Closure

end


end Minidregg.Assurance.Ext6GateProofNonzeroSuiteClosure
