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

namespace Minidregg.Assurance.BfvPrivateComputationJoin

open Minidregg.Assurance.PrivateComputationReceiptClause
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)

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
#print axioms Evidence.every_exact_integer_equation
#print axioms CheckedPrivateEvidence.bfv_bound_semantics
#print axioms receiptEvent_bfv_semantics

end Minidregg.Assurance.BfvPrivateComputationJoin
