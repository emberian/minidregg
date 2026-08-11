/-
# Assurance.Ext6GateProofPositiveExecution -- positive control, honest ceiling

This module lifts `Compiler.Ext6GateProofPositiveRun` into the exact deployed
`ControlledExecution` carrier.  The execution is positive on its single coin:
the opaque runner returns the canonical encoded receipt and Lean decodes and
accepts it for the nonzero suite/controller identity, the 23 residual
coordinates, and all five Fiat--Shamir rounds.

No `SecurityResidual` is constructed here.  The eight-event PCS/subfield/
proximity/binding/oracle/sampling/final-LDT record remains a separate argument
to `Deployment.admit`; consequently this module states neither semantic
succinctness nor a sub-unit false-acceptance bound.
-/

import Assurance.Ext6GateProofDeploymentAdmission
import Compiler.Ext6GateProofPositiveRun

namespace Minidregg.Assurance.Ext6GateProofPositiveExecution

open Minidregg.Assurance.Ext6GateProofControllerAdmission
open Minidregg.Assurance.Ext6GateProofDeploymentAdmission
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.Ext6GateProofDeployment
open Minidregg.Compiler.Ext6GateProofPositiveRun
open Minidregg.Compiler.GateMleExt6
open Minidregg.Loom

namespace Positive

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

abbrev DeployedSuite := Minidregg.Compiler.Ext6GateProofDeployment.suite
abbrev DeployedStatement := Minidregg.Compiler.Ext6GateProofDeployment.statement
abbrev DeployedVerifier := Minidregg.Compiler.Ext6GateProofDeployment.verifier
abbrev DeployedRounds := Minidregg.Compiler.Ext6GateProofDeployment.Rounds

abbrev Reply := AcceptedReceipt DeployedSuite DeployedStatement DeployedVerifier request

def execution : Unit → Option Reply := fun _ ↦ some acceptedReceipt

def runner : Unit → OpaqueProofRunner Unit := fun _ ↦ honestRunner

/-- The concrete single-coin execution carrier.  Its fields end exactly at
opaque bytes, lawful decoding, and the Lean controller relation. -/
noncomputable def control :
    Ext6GateProofDeploymentAdmission.Deployment.ControlledExecution
      Unit Unit request where
  execution := execution
  runner := runner
  executionExact := by
    intro omega reply selected
    cases omega
    have replyExact : reply = acceptedReceipt := by
      simpa [execution] using (Option.some.inj selected).symm
    subst reply
    exact honest_run_succeeds

@[simp] theorem control_selects : control.execution () = some acceptedReceipt := rfl

@[simp] theorem control_runner_exact : control.runner () request = .ok proofBytes := by
  simp [control, runner, honestRunner]

theorem control_run_exact :
    run DeployedSuite DeployedStatement DeployedVerifier (control.runner ()) request =
      .ok acceptedReceipt :=
  control.executionExact () acceptedReceipt control_selects

/-- The positive carrier is attached to the exact landed deployment profile,
not a zero/default suite or a smaller toy statement. -/
theorem deployed_profile_exact :
    identity.suiteId = suiteId ∧ identity.controllerId = controllerId ∧
      suiteId ≠ ⟨0⟩ ∧ controllerId ≠ ⟨0⟩ ∧
      (descriptorResiduals DeployedStatement.descriptor (fun _ ↦ 0)).length = 23 ∧
      DeployedRounds = 5 := by
  exact ⟨rfl, rfl, suiteId_nonzero, controllerId_nonzero,
    demoResidualCount, rfl⟩

/-- Exact control evidence projected through the admission API: retained bytes,
canonical codec decode, and all deterministic Ext6 acceptance equations. -/
theorem selected_control_evidence_exact :
    control.runner () request = .ok acceptedReceipt.proofBytes ∧
      DeployedVerifier.receiptCodec.decode acceptedReceipt.proofBytes =
        some acceptedReceipt.receipt ∧
      Accepts DeployedSuite DeployedStatement acceptedReceipt.receipt := by
  exact Ext6GateProofDeploymentAdmission.Deployment.selected_control_evidence
    control control_selects

theorem selected_bytes_are_canonical : acceptedReceipt.proofBytes = proofBytes := rfl

theorem selected_receipt_is_canonical : acceptedReceipt.receipt = receipt := rfl

theorem selected_gamma_exact :
    acceptedReceipt.receipt.gamma =
      derivedGamma DeployedSuite DeployedStatement acceptedReceipt.receipt :=
  receipt_accepts.1

theorem selected_round_order_exact (i : Fin DeployedRounds) :
    acceptedReceipt.receipt.roundChallenge i =
      derivedRoundChallenge DeployedSuite DeployedStatement acceptedReceipt.receipt i :=
  receipt_accepts.2.1 i

theorem selected_eta_exact :
    acceptedReceipt.receipt.eta =
      derivedEta DeployedSuite DeployedStatement acceptedReceipt.receipt :=
  receipt_accepts.2.2.1

theorem selected_terminal_accepts :
    scChain 0 (roundMessages acceptedReceipt.receipt)
        (roundChallenges acceptedReceipt.receipt) DeployedRounds =
      terminalExpression acceptedReceipt.receipt.terminalValue :=
  receipt_accepts.2.2.2.2.2.1

/-! ## Teeth at the same deployed boundary -/

theorem stale_request_has_no_selected_execution :
    run DeployedSuite DeployedStatement DeployedVerifier honestRunner staleRequest =
      .error (.native ()) :=
  stale_request_rejected

theorem malformed_reply_has_no_selected_execution :
    run DeployedSuite DeployedStatement DeployedVerifier malformedRunner request =
      .error .invalidEncoding :=
  malformed_bytes_rejected

theorem decoded_algebra_tamper_has_no_selected_execution :
    run DeployedSuite DeployedStatement DeployedVerifier tamperedRunner request =
      .error .rejected :=
  decoded_tamper_rejected

/-! ## The security side remains explicit -/

/-- Supplying a real security residual is an additional operation with an
additional argument.  This definition is intentionally not instantiated here. -/
def withSecurity
    (security : Ext6GateProofDeploymentAdmission.Deployment.SecurityResidual Unit) :
    GameFamily (suite := DeployedSuite) (statement := DeployedStatement)
      (verifier := DeployedVerifier) Unit Unit request :=
  Ext6GateProofDeploymentAdmission.Deployment.admit control security

@[simp] theorem withSecurity_ledger_exact
    (security : Ext6GateProofDeploymentAdmission.Deployment.SecurityResidual Unit) :
    (withSecurity security).ledger = security.ledger := rfl

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Ext6GateProofPositiveExecution.Positive.control_run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms control_run_exact
/-- info: 'Minidregg.Assurance.Ext6GateProofPositiveExecution.Positive.selected_control_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_control_evidence_exact
/-- info: 'Minidregg.Assurance.Ext6GateProofPositiveExecution.Positive.withSecurity_ledger_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms withSecurity_ledger_exact

end


end Positive

end Minidregg.Assurance.Ext6GateProofPositiveExecution
