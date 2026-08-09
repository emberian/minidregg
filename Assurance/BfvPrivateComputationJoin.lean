/-
# `Assurance.BfvPrivateComputationJoin` — BFV evidence as encrypted-RNS-FHE completion

This module specializes `PrivateComputationLanguage.Evidence encryptedRnsFhe` to the
proof-relevant `BfvReceiptClause.AcceptedToken`.  The accepted relation binds the exact
BFV public statement, its single input/witness reference, its input and output RNS
representations, and the same modulus-major family of 384 compressed equations.

The evidence portal checks only this Lean relation.  The resulting receipt theorem says
that every output-representation row satisfies its exact integer equation.  It deliberately
makes no privacy, knowledge, proof-suite, PCS, controller-implementation, or cryptographic
soundness claim.  Those independent authority legs remain parameters of the existing
private-computation declaration and receipt clause.
-/
import Assurance.PrivateComputationReceiptClause
import Compiler.BfvReceiptClause
import Theory.AcceptedCellEffect

namespace Minidregg.Assurance.BfvPrivateComputationJoin

open Minidregg.Assurance.PrivateComputationReceiptClause
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Concrete encrypted-RNS-FHE language -/

structure Program where
  clauseId : Digest
  relationId : Digest
  outputRepresentationId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
deriving DecidableEq, Repr

def outputRepresentationId : Digest := ⟨941⟩

/-- The only program admitted by this evidence relation.  Its suite/controller pins are
the same explicit unassigned sentinels as the BFV receipt clause. -/
def program : Program where
  clauseId := bfvClauseId
  relationId := bfvRelationId
  outputRepresentationId := outputRepresentationId
  proofSuiteId := unassignedProofSuiteId
  controllerDigest := unassignedControllerDigest

theorem program_crypto_pins_unassigned :
    program.proofSuiteId = ⟨0⟩ /\ program.controllerDigest = ⟨0⟩ := by
  decide

structure InputRepresentation where
  reference : WitnessReference
  equations : OwnerBatch

structure OutputRepresentation where
  representationId : Digest
  commitmentId : Digest
  inputReference : WitnessReference
  equations : OwnerBatch

/-- The evidence retains the actual accepted BFV token and the exact two representations
to which it is bound.  The proof fields are equality/shape bindings, not hiding claims. -/
structure Evidence where
  claim : PublicStatement
  token : AcceptedToken claim
  inputRepresentation : InputRepresentation
  input_reference_eq : inputRepresentation.reference = claim.input.reference
  input_equation_eq : forall rowIndex,
    inputRepresentation.equations.equation rowIndex = claim.equations.equation rowIndex
  outputRepresentation : OutputRepresentation
  output_representation_id : outputRepresentation.representationId = outputRepresentationId
  output_reference_eq : outputRepresentation.inputReference = claim.input.reference
  output_equation_eq : forall rowIndex,
    outputRepresentation.equations.equation rowIndex = claim.equations.equation rowIndex

/-- Unsupported private-computation modes are uninhabited in this language. -/
def language : PrivateComputationLanguage where
  Program := fun
    | .encryptedRnsFhe => Program
    | .witnessZk => PEmpty
    | .sharedMpc => PEmpty
  InputArtifact := fun
    | .encryptedRnsFhe => InputRepresentation
    | .witnessZk => PEmpty
    | .sharedMpc => PEmpty
  OutputArtifact := fun
    | .encryptedRnsFhe => OutputRepresentation
    | .witnessZk => PEmpty
    | .sharedMpc => PEmpty
  Evidence := fun
    | .encryptedRnsFhe => Evidence
    | .witnessZk => PEmpty
    | .sharedMpc => PEmpty

abbrev ComputationStatement :=
  PrivateComputationStatement language .encryptedRnsFhe PublicStatement Digest Unit

/-! ## Exact computation-evidence relation -/

/-- This is the entire mode-specific acceptance relation.  In particular it contains no
privacy or knowledge predicate and does not interpret the zero suite/controller pins. -/
def Accepts (statement : ComputationStatement) (evidence : Evidence) : Prop :=
  statement.program = program /\
  statement.inputValue = evidence.claim /\
  statement.inputArtifact = evidence.inputRepresentation /\
  statement.outputArtifact = evidence.outputRepresentation /\
  statement.outputCommitment = evidence.outputRepresentation.commitmentId /\
  statement.privateOutput = ()

/-- A logical checker for the exact Lean relation.  This does not introduce a native
verifier: the only substantive witness field is the already AIR-checked BFV token. -/
noncomputable def evidencePortal :
    PrivateEvidencePortal ComputationStatement Evidence := by
  classical
  exact {
    verify := fun statement evidence => decide (Accepts statement evidence)
    Accepts := Accepts
    accepted_law := by
      intro statement evidence accepted
      exact of_decide_eq_true accepted
  }

theorem Evidence.every_exact_integer_equation (evidence : Evidence)
    (rowIndex : Fin equationsPerOwner) :
    (evidence.outputRepresentation.equations.equation rowIndex).numerator
        evidence.token.input.row =
      ((evidence.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
        (evidence.token.batch.rowCall rowIndex).witness.quotient.value := by
  rw [evidence.output_equation_eq rowIndex]
  exact evidence.token.every_exact_integer_equation rowIndex

/-- Checked private evidence binds the statement's exact public claim, input reference,
output representation, and equation family, and proves every output row over `Int`. -/
theorem CheckedPrivateEvidence.bfv_bound_semantics
    {statement : ComputationStatement}
    (checked : CheckedPrivateEvidence evidencePortal statement) :
    statement.inputValue = checked.witness.claim /\
    statement.inputArtifact.reference = checked.witness.claim.input.reference /\
    statement.outputArtifact = checked.witness.outputRepresentation /\
    statement.outputArtifact.inputReference = checked.witness.claim.input.reference /\
    statement.outputArtifact.representationId = outputRepresentationId /\
    statement.outputCommitment = statement.outputArtifact.commitmentId /\
    (forall rowIndex,
      (statement.outputArtifact.equations.equation rowIndex).numerator
          checked.witness.token.input.row =
        ((statement.outputArtifact.equations.equation rowIndex).rns.value : Int) *
          (checked.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
  have accepted : Accepts statement checked.witness := checked.accepts
  rcases accepted with ⟨-, claimEq, inputEq, outputEq, commitmentEq, -⟩
  refine ⟨claimEq, ?_, outputEq, ?_, ?_, ?_, ?_⟩
  · rw [inputEq]
    exact checked.witness.input_reference_eq
  · rw [outputEq]
    exact checked.witness.output_reference_eq
  · rw [outputEq]
    exact checked.witness.output_representation_id
  · simpa [outputEq] using commitmentEq
  · intro rowIndex
    rw [outputEq]
    exact checked.witness.every_exact_integer_equation rowIndex

/-! ## Authoritative release-free BFV core -/

/-- First-order mode pins retained in the pure computation request.  Zero
suite/controller values remain explicit unassigned sentinels; they are not
interpreted as privacy or cryptographic evidence. -/
structure ModeEvidencePins where
  clauseId : Digest
  relationId : Digest
  outputRepresentationId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
deriving DecidableEq, Repr

def modeEvidencePins : ModeEvidencePins where
  clauseId := bfvClauseId
  relationId := bfvRelationId
  outputRepresentationId := outputRepresentationId
  proofSuiteId := unassignedProofSuiteId
  controllerDigest := unassignedControllerDigest

theorem modeEvidencePins_crypto_unassigned :
    modeEvidencePins.proofSuiteId = ⟨0⟩ /\
      modeEvidencePins.controllerDigest = ⟨0⟩ := by
  decide

abbrev CoreComputationStatement :=
  CoreStatement language .encryptedRnsFhe Digest PublicStatement Digest Unit
    ModeEvidencePins

/-- The pure BFV relation adds exact relation and mode-pin bindings to the
existing representation/equation statement.  It contains no disclosure or
transition-authorization premise. -/
def CoreAccepts (statement : CoreComputationStatement) (evidence : Evidence) : Prop :=
  statement.program = program /\
  statement.relation = bfvRelationId /\
  statement.modeEvidencePins = modeEvidencePins /\
  statement.inputValue = evidence.claim /\
  statement.inputArtifact = evidence.inputRepresentation /\
  statement.outputArtifact = evidence.outputRepresentation /\
  statement.outputCommitment = evidence.outputRepresentation.commitmentId /\
  statement.privateOutput = ()

/-- Lean checker for the exact pure BFV relation.  The checked witness embeds
the existing 384-row BFV AIR token; this definition adds no privacy, ZK, MPC,
PCS, controller-implementation, or cryptographic soundness theorem. -/
noncomputable def coreEvidencePortal :
    PrivateEvidencePortal CoreComputationStatement Evidence := by
  classical
  exact {
    verify := fun statement evidence => decide (CoreAccepts statement evidence)
    Accepts := CoreAccepts
    accepted_law := by
      intro statement evidence accepted
      exact of_decide_eq_true accepted
  }

/-- A pure BFV dialect owns only the named input-identity bridge.  It is not an
authority object: transition authority is the common request-indexed kernel
`Authorized` token consumed by `ComputationCellEffect.accept`. -/
structure CoreDialect
    (CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type) where
  inputBridge : NamedRepresentationBridge Digest CanonicalInput InputSourceWitness
    InputRepresentation InputTargetWitness PublicStatement

noncomputable def CoreDialect.declaration
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier) :
    ComputationDeclaration language .encryptedRnsFhe Digest Digest CanonicalInput
      PublicStatement InputSourceWitness InputTargetWitness Digest Unit ResourceEffect
      Footprint Nullifier ModeEvidencePins where
  inputBridge := dialect.inputBridge
  computationPortal := coreEvidencePortal

theorem core_bfv_bound_semantics
    {statement : CoreComputationStatement}
    (checked : CheckedPrivateEvidence coreEvidencePortal statement) :
    statement.program = program /\
    statement.relation = bfvRelationId /\
    statement.modeEvidencePins = modeEvidencePins /\
    statement.inputValue = checked.witness.claim /\
    statement.inputArtifact.reference = checked.witness.claim.input.reference /\
    statement.outputArtifact = checked.witness.outputRepresentation /\
    statement.outputArtifact.inputReference = checked.witness.claim.input.reference /\
    statement.outputArtifact.representationId = outputRepresentationId /\
    statement.outputCommitment = statement.outputArtifact.commitmentId /\
    (forall rowIndex,
      (statement.outputArtifact.equations.equation rowIndex).numerator
          checked.witness.token.input.row =
        ((statement.outputArtifact.equations.equation rowIndex).rns.value : Int) *
          (checked.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
  have accepted : CoreAccepts statement checked.witness := checked.accepts
  rcases accepted with
    ⟨programEq, relationEq, pinsEq, claimEq, inputEq, outputEq, commitmentEq, -⟩
  refine ⟨programEq, relationEq, pinsEq, claimEq, ?_, outputEq, ?_, ?_, ?_, ?_⟩
  · rw [inputEq]
    exact checked.witness.input_reference_eq
  · rw [outputEq]
    exact checked.witness.output_reference_eq
  · rw [outputEq]
    exact checked.witness.output_representation_id
  · simpa [outputEq] using commitmentEq
  · intro rowIndex
    rw [outputEq]
    exact checked.witness.every_exact_integer_equation rowIndex

/-- The positive pure-BFV kernel path.  The common `Authorized` token is the
sole transition authority; exact argument/effect digests, pre-root, validated
patch, input identity, and the BFV mode token are all required in this one
construction. -/
noncomputable def acceptCore
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (authorization : Authorized portal authState commonRequest)
    (argsDigestBound : commonRequest.argsDigest = adapter.completeRequestDigest request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.completeEffectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : dialect.declaration.Completion request result)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request result)) :
    ComputationCellEffect.Accepted (portal := portal) (authState := authState)
      dialect.declaration adapter commonRequest pre request result :=
  ComputationCellEffect.accept dialect.declaration adapter authorization argsDigestBound
    effectsDigestBound preRootBound completion validated

/-- An accepted pure BFV effect retains all request bindings, is necessarily
sealed, and exposes the exact equation for every one of the 384 owner rows.
This is an arithmetic/representation theorem only. -/
theorem acceptedCore_bfv_semantics
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal) (authState := authState)
      dialect.declaration adapter commonRequest pre request result) :
    commonRequest.argsDigest = adapter.completeRequestDigest request /\
    commonRequest.effectsDigest = adapter.completeEffectDigest request /\
    accepted.cellEffect.disclosure = .sealed /\
    request.program = program /\
    request.relation = bfvRelationId /\
    request.modeEvidencePins = modeEvidencePins /\
    request.inputValue =
      accepted.cellEffect.modeEvidence.computation.witness.claim /\
    result.outputRepresentation =
      accepted.cellEffect.modeEvidence.computation.witness.outputRepresentation /\
    result.outputRepresentation.representationId = outputRepresentationId /\
    request.outputCommitment = result.outputRepresentation.commitmentId /\
    (forall rowIndex,
      (result.outputRepresentation.equations.equation rowIndex).numerator
          accepted.cellEffect.modeEvidence.computation.witness.token.input.row =
        ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
          (accepted.cellEffect.modeEvidence.computation.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
  have bound :=
    core_bfv_bound_semantics accepted.cellEffect.modeEvidence.computation
  have core :
      request.program = program /\
      request.relation = bfvRelationId /\
      request.modeEvidencePins = modeEvidencePins /\
      request.inputValue =
        accepted.cellEffect.modeEvidence.computation.witness.claim /\
      result.outputRepresentation =
        accepted.cellEffect.modeEvidence.computation.witness.outputRepresentation /\
      result.outputRepresentation.inputReference =
        accepted.cellEffect.modeEvidence.computation.witness.claim.input.reference /\
      result.outputRepresentation.representationId = outputRepresentationId /\
      request.outputCommitment = result.outputRepresentation.commitmentId /\
      (forall rowIndex,
        (result.outputRepresentation.equations.equation rowIndex).numerator
            accepted.cellEffect.modeEvidence.computation.witness.token.input.row =
          ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
            (accepted.cellEffect.modeEvidence.computation.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
    simpa only [CoreDialect.declaration, ComputationDeclaration.statementOf] using
      ⟨bound.1, bound.2.1, bound.2.2.1, bound.2.2.2.1,
        bound.2.2.2.2.2.1, bound.2.2.2.2.2.2.1,
        bound.2.2.2.2.2.2.2.1, bound.2.2.2.2.2.2.2.2.1,
        bound.2.2.2.2.2.2.2.2.2⟩
  exact ⟨accepted.argsDigestBound,
    accepted.cellEffect.effectsDigestBound,
    accepted.disclosure_sealed,
    core.1, core.2.1, core.2.2.1, core.2.2.2.1,
    core.2.2.2.2.1, core.2.2.2.2.2.2.1,
    core.2.2.2.2.2.2.2.1,
    core.2.2.2.2.2.2.2.2⟩

/-! ## Concrete declaration constructor -/

/-- The authorization, canonical-input bridge, and disclosure authority stay authored by
their existing declarations.  Only the computation portal is fixed here. -/
structure Authority
    (Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*) where
  authorizationPortal : PrivateEvidencePortal
    (PrivateComputationRequest language .encryptedRnsFhe Observer Policy Recipient Purpose
      Digest AuthorizationContext CanonicalInput PublicStatement DeclassificationAuthority)
    AuthorizationWitness
  inputBridge : NamedRepresentationBridge Digest CanonicalInput InputSourceWitness
    InputRepresentation InputTargetWitness PublicStatement
  disclosureDeclaration : DisclosureDeclaration Observer Policy Recipient Purpose Digest
    OutputRepresentation Unit OutputSourceWitness OutputTargetWitness
    ReleaseAuthorizationWitness Release

noncomputable def Authority.declaration
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release) :
    PrivateComputationDeclaration language .encryptedRnsFhe Observer Policy Recipient Purpose
      Digest AuthorizationContext CanonicalInput PublicStatement InputSourceWitness
      InputTargetWitness AuthorizationWitness Digest Unit OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release where
  authorizationPortal := authority.authorizationPortal
  inputBridge := authority.inputBridge
  computationPortal := evidencePortal
  disclosureDeclaration := authority.disclosureDeclaration

/-- One-way compatibility for legacy authors: retain only the named BFV input
identity bridge and forget the legacy transition-authorization portal and all
disclosure/release syntax.  There is deliberately no inverse projection. -/
noncomputable def Authority.toCoreDialect
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release
      ResourceEffect Footprint Nullifier : Type}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release) :
    CoreDialect CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect
      Footprint Nullifier where
  inputBridge := authority.inputBridge

theorem exact_owner_row_count : equationsPerOwner = 384 :=
  rfl

/-! ## Existing private-computation receipt clause -/

theorem receiptEvent_bfv_semantics
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)
    {manifest : Manifest}
    {binding : ClauseBinding manifest authority.declaration}
    [DecidableEq Release]
    (event : ReceiptEvent binding)
    (clauseExact : binding.clause = bfvClauseDecl) :
    event.evidence.modeTag = .encryptedRnsFhe /\
    event.evidence.clauseId = bfvClauseId /\
    event.evidence.relationId = bfvRelationId /\
    binding.clause.proofSuiteId = ⟨0⟩ /\
    binding.clause.verifierControllerDigest = ⟨0⟩ /\
    (forall rowIndex,
      (event.outcome.output.representation.equations.equation rowIndex).numerator
          event.evidence.checked.witness.token.input.row =
        ((event.outcome.output.representation.equations.equation rowIndex).rns.value : Int) *
          (event.evidence.checked.witness.token.batch.rowCall rowIndex).witness.quotient.value) := by
  have accepted : Accepts
      (authority.declaration.statementOf event.privateRequest event.outcome)
      event.evidence.checked.witness := by
    simpa only [Authority.declaration] using event.evidence.checked.accepts
  rcases accepted with ⟨-, -, -, outputEq, -, -⟩
  have outputEq' : event.outcome.output.representation =
      event.evidence.checked.witness.outputRepresentation := by
    simpa only [PrivateComputationDeclaration.statementOf] using outputEq
  refine ⟨event.evidence.modeExact, ?_⟩
  refine ⟨?_, ?_⟩
  · exact event.evidence.clauseIdExact.trans (congrArg DialectClauseDecl.clauseId clauseExact)
  refine ⟨?_, ?_⟩
  · exact event.evidence.relationIdExact.trans (congrArg DialectClauseDecl.relationId clauseExact)
  refine ⟨?_, ?_⟩
  · rw [clauseExact]
    rfl
  refine ⟨?_, ?_⟩
  · rw [clauseExact]
    rfl
  · intro rowIndex
    rw [outputEq']
    exact event.evidence.checked.witness.every_exact_integer_equation rowIndex

#print axioms program_crypto_pins_unassigned
#print axioms modeEvidencePins_crypto_unassigned
#print axioms Evidence.every_exact_integer_equation
#print axioms CheckedPrivateEvidence.bfv_bound_semantics
#print axioms core_bfv_bound_semantics
#print axioms acceptedCore_bfv_semantics
#print axioms exact_owner_row_count
#print axioms receiptEvent_bfv_semantics

end Minidregg.Assurance.BfvPrivateComputationJoin
