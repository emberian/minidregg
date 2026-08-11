/-
# Assurance.Tower256LogupExtensionDeploymentAdmission -- residual-preserving join

The concrete clause-404 carrier proves byte framing and reflected controller
acceptance.  This module states the remaining deployment boundary without
collapsing it into that control result.  The exact table/checkpoint position
binding, LogUp PCS plus sampled decider, commitment CR, and cSHAKE/ROM transport
come from the existing common-game admission record.  History execution and
mutable-RAM consistency remain additional named residuals on the same coin.
-/

import Assurance.Tower256LogupControllerAdmission
import Compiler.Tower256LogupExtensionDeployment

namespace Minidregg.Assurance.Tower256LogupExtensionDeploymentAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.Tower256LogupControllerAdmission
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.Tower256LogupAcceptedRun
open Minidregg.Compiler.Tower256LogupExtensionDeployment
open Minidregg.Loom

set_option autoImplicit false

noncomputable section

abbrev Value256 :=
  Minidregg.Compiler.Tower256LogupExtensionDeployment.Tower256

local instance finalStatementDecidable :
    Decidable (LogupFinalStatement trace claim) :=
  isTrue Minidregg.Compiler.Tower256LogupExtensionDeployment.finalStatement

/-! ## Exact residual bundle -/

/-- Security and deployment evidence not manufactured by controller success.

`CommonGameHistory` and `MutableRamConsistency` are deployment-selected
relations rather than Boolean flags.  The history relation is additionally
charged to the existing history-PCS and oracle-transport events on the same
`Omega`; the RAM relation is pinned to this exact concrete trace and claim. -/
structure SecurityResidual
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (CommonGameHistory : Omega -> Prop)
    (MutableRamConsistency :
      CommittedSemanticTrace (Fin (2 ^ RowLog)) TableLog ->
      IndexedTableReceiptClaim Value256 (Fin (2 ^ RowLog)) TableLog -> Prop) :
    Prop where
  controller : ControllerGameSecurity ledger omega backend inputs
  commonGameHistory : CommonGameHistory omega
  historyPcs : ledger.Good .historyPcs omega
  historyOracleTransport : ledger.Good .oracleTransport omega
  mutableRamConsistency : MutableRamConsistency trace claim

namespace SecurityResidual

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}
variable {CommonGameHistory : Omega -> Prop}
variable {MutableRamConsistency :
  CommittedSemanticTrace (Fin (2 ^ RowLog)) TableLog ->
  IndexedTableReceiptClaim Value256 (Fin (2 ^ RowLog)) TableLog -> Prop}

theorem tablePositionBinding
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    (backend.additiveMerkleScheme
      inputs.columns.tableSpec.role
      inputs.columns.tableSpec.slotId
      inputs.columns.tableSpec.semanticTypeId
      inputs.columns.tableSpec.domainId
      inputs.columns.tableSpec.domainCodecPin
      inputs.columns.tableSpec.domainCodec).PositionBinding :=
  residual.controller.tablePositionBinding

theorem checkpointPositionBinding
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    (backend.additiveMerkleScheme
      inputs.checkpointSpec.role
      inputs.checkpointSpec.slotId
      inputs.checkpointSpec.semanticTypeId
      inputs.checkpointSpec.domainId
      inputs.checkpointSpec.domainCodecPin
      inputs.checkpointSpec.domainCodec).PositionBinding :=
  residual.controller.checkpointPositionBinding

theorem pcsAndSampledDecider
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    ledger.Good .logupPcs omega :=
  residual.controller.table.pcsAndSampledDecider

theorem commitmentBindingCR
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    ledger.Good .commitmentBinding omega :=
  residual.controller.commitmentBinding

theorem cshakeRomTransport
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    ledger.Good .oracleTransport omega :=
  residual.controller.table.cshakeRomTransport

end SecurityResidual

/-! ## Verified execution plus retained residuals -/

structure AdmittedExtension
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (CommonGameHistory : Omega -> Prop)
    (MutableRamConsistency :
      CommittedSemanticTrace (Fin (2 ^ RowLog)) TableLog ->
      IndexedTableReceiptClaim Value256 (Fin (2 ^ RowLog)) TableLog -> Prop)
    {Error : Type} {runner : NativeRunner Error} {seed : List UInt8}
    (execution : VerifiedExecution backend trace claim inputs runner seed) :
    Prop where
  lookup : AdmittedLookup ledger omega execution
  commonGameHistory : CommonGameHistory omega
  historyPcs : ledger.Good .historyPcs omega
  historyOracleTransport : ledger.Good .oracleTransport omega
  mutableRamConsistency : MutableRamConsistency trace claim

namespace AdmittedExtension

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}
variable {CommonGameHistory : Omega -> Prop}
variable {MutableRamConsistency :
  CommittedSemanticTrace (Fin (2 ^ RowLog)) TableLog ->
  IndexedTableReceiptClaim Value256 (Fin (2 ^ RowLog)) TableLog -> Prop}
variable {Error : Type} {runner : NativeRunner Error} {seed : List UInt8}
variable {execution : VerifiedExecution backend trace claim inputs runner seed}

/-- The join consumes, rather than derives, every residual field. -/
def ofVerified
    (execution : VerifiedExecution backend trace claim inputs runner seed)
    (residual : SecurityResidual ledger omega CommonGameHistory
      MutableRamConsistency) :
    AdmittedExtension ledger omega CommonGameHistory MutableRamConsistency
      execution where
  lookup := AdmittedLookup.ofVerifiedExecution execution residual.controller
  commonGameHistory := residual.commonGameHistory
  historyPcs := residual.historyPcs
  historyOracleTransport := residual.historyOracleTransport
  mutableRamConsistency := residual.mutableRamConsistency

/-- The consumer-visible lookup equation is available only after the complete
residual-preserving join. -/
theorem indexedEvaluation
    (admitted : AdmittedExtension ledger omega CommonGameHistory
      MutableRamConsistency execution) :
    claim.claimedEvaluation =
      logupDot (fun row => claim.table (trace.index row)) claim.weights :=
  admitted.lookup.indexedEvaluation

end AdmittedExtension

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256LogupExtensionDeploymentAdmission.SecurityResidual.tablePositionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SecurityResidual.tablePositionBinding
/-- info: 'Minidregg.Assurance.Tower256LogupExtensionDeploymentAdmission.AdmittedExtension.ofVerified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdmittedExtension.ofVerified
/-- info: 'Minidregg.Assurance.Tower256LogupExtensionDeploymentAdmission.AdmittedExtension.indexedEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdmittedExtension.indexedEvaluation

end


end Minidregg.Assurance.Tower256LogupExtensionDeploymentAdmission
