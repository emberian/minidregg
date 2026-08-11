/-
# Assurance.Ext6GateProofDeploymentAdmission -- the concrete Ext6 join

This module specializes the Ext6 admission game to the versioned suite,
statement, receipt framing, and reflected verifier deployed by
`Compiler.Ext6GateProofDeployment`.

The join is intentionally split. `ControlledExecution` is native bytes plus
the exact controller result. `SecurityResidual` is the independently supplied
PCS/subfield/proximity/binding/ROM/challenge/final-LDT reduction.  Combining
the two records does not synthesize the latter from the former.
-/

import Assurance.ExtensibleProofCompositionGame
import Compiler.Ext6GateProofDeployment

namespace Minidregg.Assurance.Ext6GateProofDeploymentAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.Ext6GateProofControllerAdmission
open Minidregg.Assurance.ExtensibleProofCompositionGame
open Minidregg.Compiler
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.GateFactoredExt6
open Minidregg.Compiler.GateMleExt6
open Minidregg.Loom

namespace Deployment

set_option autoImplicit false

noncomputable section

abbrev Suite := Ext6GateProofDeployment.suite
abbrev Statement := Ext6GateProofDeployment.statement
abbrev Verifier := Ext6GateProofDeployment.verifier
abbrev Rounds := Ext6GateProofDeployment.Rounds
abbrev Padding := Ext6GateProofDeployment.Padding

/-! ## The two sides of the deployment join -/

/-- Native execution data and its exact connection to the reflected
controller.  This record contains no semantic or probabilistic premise. -/
structure ControlledExecution (Omega : Type) [Fintype Omega]
    (Error : Type) (request : List UInt8) where
  execution : Omega -> Option
    (AcceptedReceipt Suite Statement Verifier request)
  runner : Omega -> OpaqueProofRunner Error
  executionExact : ∀ omega reply, execution omega = some reply ->
    run Suite Statement Verifier (runner omega) request = .ok reply

/-- The residual required for a semantic or probability theorem.  Its single
`reductions` field retains all eight named obligations: gate algebra, PCS,
subfield provenance, proximity, commitment binding, oracle transport,
challenge sampling, and final LDT. -/
structure SecurityResidual (Omega : Type) [Fintype Omega] where
  ledger : Ext6FailureLedger Omega
  reductions : ReductionLaws (suite := Suite) (statement := Statement)
    Omega ledger

/-- The concrete game family is inhabited only when both independent records
are supplied. -/
def admit {Omega : Type} [Fintype Omega] {Error : Type}
    {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega) :
    GameFamily (suite := Suite) (statement := Statement)
      (verifier := Verifier) Omega Error request where
  ledger := security.ledger
  laws := security.reductions
  execution := control.execution
  runner := control.runner
  executionExact := control.executionExact

@[simp] theorem admit_ledger_exact {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega) :
    (admit control security).ledger = security.ledger :=
  rfl

@[simp] theorem admit_reductions_exact {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega) :
    (admit control security).laws = security.reductions :=
  rfl

/-! ## The exact strength of control-only success -/

/-- This is the strongest deployment conclusion obtained from
`ControlledExecution` alone: native bytes are retained, the versioned codec
decodes them, and the reflected controller accepts.  There is deliberately no
trace witness and no probability bound in this conclusion. -/
theorem selected_control_evidence {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    {omega : Omega}
    {reply : AcceptedReceipt Suite Statement Verifier request}
    (selected : control.execution omega = some reply) :
    control.runner omega request = .ok reply.proofBytes ∧
      Ext6GateProofDeployment.verifier.receiptCodec.decode reply.proofBytes =
        some reply.receipt ∧
      Accepts Suite Statement reply.receipt := by
  exact Ext6GateProofDeployment.success_control_only
    (control.runner omega) request reply
    (control.executionExact omega reply selected)

/-- Semantic validity appears only after the separately named reduction is
provided and its exact eight-event ledger is good on this same coin. -/
theorem selected_semantic_of_residual {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega) {omega : Omega}
    {reply : AcceptedReceipt Suite Statement Verifier request}
    (selected : control.execution omega = some reply)
    (good : ¬security.ledger.Bad omega) :
    ∃ trace : Nat -> BabyBear,
      AuthenticatedTraceRelation Statement reply.receipt trace ∧
      descriptorHolds Ext6GateProofDeployment.statement.descriptor trace := by
  have evidence := selected_control_evidence control selected
  exact security.reductions.semantic_of_not_bad good reply.receipt evidence.2.2

/-! ## A formal control/security separation tooth -/

/-- A certain failure event priced only by the universal `Pr[E] ≤ 1` bound. -/
def certainFailure {Omega : Type} [Fintype Omega] : PricedFailure Omega where
  event := fun _ => True
  price := 1
  bound := uniformProb_le_one _

/-- A deliberately vacuous residual.  Every reduction premise contains the
goodness of a certain event and is therefore contradictory.  This is not a
deployment claim; it is the witness that controller correctness alone cannot
imply a non-vacuous proof-system theorem. -/
def maximalResidual (Omega : Type) [Fintype Omega] : SecurityResidual Omega where
  ledger := fun _ => certainFailure
  reductions :=
    { aggregateOpeningExact := by
        intro omega receipt accepted goodPcs
        exact (goodPcs trivial).elim
      etaSound := by
        intro omega receipt trace accepted aggregate goodAlgebra
        exact (goodAlgebra trivial).elim
      sumcheckSound := by
        intro omega receipt trace accepted relation goodAlgebra
        exact (goodAlgebra trivial).elim
      gammaSound := by
        intro omega receipt trace goodAlgebra
        exact (goodAlgebra trivial).elim }

@[simp] theorem maximalResidual_total (Omega : Type) [Fintype Omega] :
    (maximalResidual Omega).ledger.total = 8 := by
  norm_num [maximalResidual, Ext6FailureLedger.total, certainFailure]

/-- Any correct controller execution can be paired with the vacuous
eight-event residual of total price `8`.  Hence the control carrier, by
itself, enforces neither a sub-unit bound nor any cryptographic reduction. -/
theorem control_can_be_admitted_with_vacuous_security
    {Omega : Type} [Fintype Omega] {Error : Type}
    {request : List UInt8}
    (control : ControlledExecution Omega Error request) :
    (admit control (maximalResidual Omega)).ledger.total = 8 :=
  maximalResidual_total Omega

/-! ## Local and global probability statements, with the residual visible -/

theorem falseAccept_le {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega) :
    uniformProb Omega (admit control security).FalseAccept ≤
      security.ledger.total := by
  simpa using (admit control security).falseAccept_le

def globalLedger {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega)
    (base : FailureLedger Omega) : Ext6GlobalFailureLedger Omega :=
  Ext6Instantiation.globalLedger (admit control security) base

theorem falseAccept_le_global {Omega : Type} [Fintype Omega]
    {Error : Type} {request : List UInt8}
    (control : ControlledExecution Omega Error request)
    (security : SecurityResidual Omega)
    (base : FailureLedger Omega) :
    uniformProb Omega (admit control security).FalseAccept ≤
      (globalLedger control security base).total :=
  Ext6Instantiation.falseAccept_le_globalTotal (admit control security) base

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Ext6GateProofDeploymentAdmission.Deployment.selected_control_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_control_evidence
/-- info: 'Minidregg.Assurance.Ext6GateProofDeploymentAdmission.Deployment.selected_semantic_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_semantic_of_residual
/-- info: 'Minidregg.Assurance.Ext6GateProofDeploymentAdmission.Deployment.falseAccept_le_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms falseAccept_le_global

end

end Deployment

end Minidregg.Assurance.Ext6GateProofDeploymentAdmission
