/-
# `Assurance.BfvConcreteBatchCell` -- checked BFV batch to cell and history

This module connects the concrete 384-row controller to the already established
sealed BFV cell/history path.  A successful direct buffer admission can become
an `AcceptedCellEffect` because its Lean token already proves all exact integer
equations.  That fact does **not** deploy the currently zero-pinned proof suite.

The final section makes the distinction structural.  The current canonical
proof statement has zero codec/suite/controller identities and cannot bind any
assigned checker.  A future semantic proof deployment must supply both a bound
nonzero checker and the existing five-event same-coin reduction laws.  A merely
reflected control checker is therefore still not PCS, extraction, PoK, ZK,
hiding, or FHE security.
-/
import Assurance.BfvAcceptedCellEffect
import Assurance.BfvConcreteBatchAdmission
import Assurance.BfvProofControllerAdmission

namespace Minidregg.Assurance.BfvConcreteBatchCell

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.BfvAcceptedCellEffect
open Minidregg.Assurance.BfvConcreteBatchAdmission
open Minidregg.Assurance.BfvNativeBufferAdmission
open Minidregg.Assurance.BfvPrivateComputationJoin
open Minidregg.Assurance.BfvProofControllerAdmission
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvProofController
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y

noncomputable section

/-! ## Concrete admission carrier -/

abbrev ConcreteAdmission {claim : PublicStatement} (manifest : Manifest)
    (prepared : PreparedBatch claim) :=
  BatchAdmission manifest claim prepared.template

theorem concreteAdmission_all_384_exact {claim : PublicStatement}
    {manifest : Manifest} {prepared : PreparedBatch claim}
    (admission : ConcreteAdmission manifest prepared) :
    forall rowIndex : Fin 384,
      (claim.equations.equation
          (Fin.cast (by simp [equationsPerOwner]) rowIndex)).numerator
          prepared.input.row =
        ((claim.equations.equation
          (Fin.cast (by simp [equationsPerOwner]) rowIndex)).rns.value : Int) *
          ((admission.acceptedToken).batch.rowCall
            (Fin.cast (by simp [equationsPerOwner]) rowIndex)).witness.quotient.value :=
  Minidregg.Assurance.BfvConcreteBatchAdmission.BatchAdmission.all_384_exact
    admission

/-! ## The direct checked-buffer path enters the sealed cell kernel -/

variable
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority
      Release : Type}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)

/-- The concrete all-row admission, rather than an abstract batch template,
enters the established release-free BFV cell constructor. -/
noncomputable def acceptPreparedBatchSealed
    {manifest : Manifest} {claim : PublicStatement}
    {prepared : PreparedBatch claim}
    (admission : ConcreteAdmission manifest prepared)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.ComputationAdapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.ComputationOutcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.computationStatementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (PrivateCellEffect.sealedFamily (M := M)
        (privateDeclaration := authority.declaration) adapter :
          SemanticEffectFamily S M Nullifier)
      commonRequest pre request outcome :=
  acceptBatchSealed authority admission commitmentId adapter commonAuthorization
    effectsDigestBound preRootBound legs statementExact validated

@[simp] theorem acceptPreparedBatchSealed_disclosure
    {manifest : Manifest} {claim : PublicStatement}
    {prepared : PreparedBatch claim}
    (admission : ConcreteAdmission manifest prepared)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.ComputationAdapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.ComputationOutcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.computationStatementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome)) :
    (acceptPreparedBatchSealed authority admission commitmentId adapter
      commonAuthorization effectsDigestBound preRootBound legs statementExact
      validated).disclosure = .sealed :=
  rfl

/-- The concrete accepted cell exposes every one of the 384 exact integer
equations.  This conclusion comes from checked direct buffers, not proof bytes. -/
theorem acceptedPreparedBatch_all_384_exact
    {manifest : Manifest} {claim : PublicStatement}
    {prepared : PreparedBatch claim}
    (admission : ConcreteAdmission manifest prepared)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.ComputationAdapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.ComputationOutcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.computationStatementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome)) :
    forall rowIndex : Fin equationsPerOwner,
      (((acceptPreparedBatchSealed authority admission commitmentId adapter
        commonAuthorization effectsDigestBound preRootBound legs statementExact
        validated).modeEvidence.computation.witness.outputRepresentation.equations.equation
          rowIndex).numerator
        (acceptPreparedBatchSealed authority admission commitmentId adapter
          commonAuthorization effectsDigestBound preRootBound legs statementExact
          validated).modeEvidence.computation.witness.token.input.row) =
      ((((acceptPreparedBatchSealed authority admission commitmentId adapter
        commonAuthorization effectsDigestBound preRootBound legs statementExact
        validated).modeEvidence.computation.witness.outputRepresentation.equations.equation
          rowIndex).rns.value : Nat) : Int) *
        ((acceptPreparedBatchSealed authority admission commitmentId adapter
          commonAuthorization effectsDigestBound preRootBound legs statementExact
          validated).modeEvidence.computation.witness.token.batch.rowCall
            rowIndex).witness.quotient.value := by
  intro rowIndex
  exact accepted_every_exact_integer_equation authority
    (acceptPreparedBatchSealed authority admission commitmentId adapter
      commonAuthorization effectsDigestBound preRootBound legs statementExact validated)
    rowIndex

/-! ## The same concrete admission enters verified history -/

noncomputable def historyClaimOfPreparedBatch
    {manifest : Manifest} {claim : PublicStatement}
    {prepared : PreparedBatch claim}
    (admission : ConcreteAdmission manifest prepared)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.ComputationAdapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.ComputationOutcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.computationStatementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome))
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (projection : HistoryProjection
      (PrivateCellEffect.sealedFamily (M := M)
        (privateDeclaration := authority.declaration) adapter :
          SemanticEffectFamily S M Nullifier) n F)
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext) :
    BoundSemanticReceiptClaim n F :=
  historyClaimOfBatchSealed authority admission commitmentId adapter
    commonAuthorization effectsDigestBound preRootBound legs statementExact
    validated projection headerCells context

/-! ## Exact proof-suite ceiling -/

/-- Canonical proof-controller statement for the directly admitted batch.  Its
three zero identities are deliberate and are not repaired by the existence of
an in-process `BatchAdmission`. -/
def zeroPinnedStatement (argsDigest effectsDigest preRoot : Digest)
    {claim : PublicStatement} (_prepared : PreparedBatch claim)
    (outputCommitment : Digest) : Statement :=
  canonicalStatement argsDigest effectsDigest preRoot claim outputCommitment
    outputRepresentationId unassignedProofCodecId unassignedProofSuiteId
    unassignedControllerDigest

theorem zeroPinnedStatement_ids (argsDigest effectsDigest preRoot : Digest)
    {claim : PublicStatement} (prepared : PreparedBatch claim)
    (outputCommitment : Digest) :
    (zeroPinnedStatement argsDigest effectsDigest preRoot prepared
      outputCommitment).proofCodecId = ⟨0⟩ /\
    (zeroPinnedStatement argsDigest effectsDigest preRoot prepared
      outputCommitment).proofSuiteId = ⟨0⟩ /\
    (zeroPinnedStatement argsDigest effectsDigest preRoot prepared
      outputCommitment).controllerDigest = ⟨0⟩ := by
  exact ⟨rfl, rfl, rfl⟩

/-- Assigned reflected checkers cannot bind the current zero-pinned statement. -/
theorem zeroPinnedStatement_no_bound_checker
    (argsDigest effectsDigest preRoot : Digest)
    {claim : PublicStatement} (prepared : PreparedBatch claim)
    (outputCommitment : Digest) :
    ¬Nonempty (BoundReflectedChecker
      (zeroPinnedStatement argsDigest effectsDigest preRoot prepared
        outputCommitment)) := by
  exact canonicalStatement_no_boundReflectedChecker argsDigest effectsDigest
    preRoot claim outputCommitment outputRepresentationId

/-- What a future semantic suite must actually provide.  Nonzero identities
come from `BoundReflectedChecker`; semantic extraction comes separately from
the five-event same-coin laws.  Neither component is inferred from the other. -/
structure FutureSemanticSuite {Omega : Type} [Fintype Omega]
    (statement : Statement) (Witness : Type) where
  bound : BoundReflectedChecker statement
  ledger : FailureLedger Omega
  laws : SameCoinReductionLaws ledger bound Witness

theorem FutureSemanticSuite.identities_nonzero
    {Omega : Type} [Fintype Omega] {statement : Statement} {Witness : Type}
    (suite : FutureSemanticSuite (Omega := Omega) statement Witness) :
    statement.proofCodecId ≠ ⟨0⟩ /\
    statement.proofSuiteId ≠ ⟨0⟩ /\
    statement.controllerDigest ≠ ⟨0⟩ := by
  constructor
  · rw [suite.bound.proofCodecBound]
    exact suite.bound.checker.proofCodecAssigned
  constructor
  · rw [suite.bound.proofSuiteBound]
    exact suite.bound.checker.proofSuiteAssigned
  · rw [suite.bound.controllerBound]
    exact suite.bound.checker.controllerAssigned

/-- Consequently no future semantic-suite closure can be attached to the
current statement without first changing its canonical identity-bearing bytes. -/
theorem zeroPinnedStatement_no_semantic_suite
    {Omega : Type} [Fintype Omega]
    (argsDigest effectsDigest preRoot : Digest)
    {claim : PublicStatement} (prepared : PreparedBatch claim)
    (outputCommitment : Digest) (Witness : Type) :
    ¬Nonempty (FutureSemanticSuite (Omega := Omega)
      (zeroPinnedStatement argsDigest effectsDigest preRoot prepared
        outputCommitment) Witness) := by
  rintro ⟨suite⟩
  exact zeroPinnedStatement_no_bound_checker argsDigest effectsDigest preRoot
    prepared outputCommitment ⟨suite.bound⟩

/-- info: 'Minidregg.Assurance.BfvConcreteBatchCell.acceptPreparedBatchSealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptPreparedBatchSealed
/-- info: 'Minidregg.Assurance.BfvConcreteBatchCell.historyClaimOfPreparedBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyClaimOfPreparedBatch
/-- info: 'Minidregg.Assurance.BfvConcreteBatchCell.zeroPinnedStatement_no_bound_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zeroPinnedStatement_no_bound_checker
/-- info: 'Minidregg.Assurance.BfvConcreteBatchCell.zeroPinnedStatement_no_semantic_suite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zeroPinnedStatement_no_semantic_suite

end

end Minidregg.Assurance.BfvConcreteBatchCell
