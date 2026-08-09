/-
# Assurance.BfvAcceptedCellEffect -- checked BFV work becomes a cell effect

The compressed-BFV lane previously ended by projecting a private-computation
completion into a disclosure receipt.  Here the checked 384-row admission is
instead used as the computation leg of the existing typed completion, and that
completion constructs the common canonical `AcceptedCellEffect`.

The constructor below is sealed: successful private computation does not imply
release.  The output/opening authorization retained by `Completion` remains
available for a later, independent disclosure decision.  Native buffers remain
opaque candidate data and acquire meaning only through the Lean admission
already proved in `BfvNativeBufferAdmission`.
-/
import Assurance.AcceptedCellEffectHistory
import Assurance.BfvNativeBufferAdmission

namespace Minidregg.Assurance.BfvAcceptedCellEffect

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.BfvNativeBufferAdmission
open Minidregg.Assurance.BfvPrivateComputationJoin
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y

noncomputable section

variable
    {Observer Policy Recipient Purpose AuthorizationContext CanonicalInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority
      Release : Type}
    (authority : Authority Observer Policy Recipient Purpose AuthorizationContext
      CanonicalInput InputSourceWitness InputTargetWitness AuthorizationWitness
      OutputSourceWitness OutputTargetWitness ReleaseAuthorizationWitness
      DeclassificationAuthority Release)

/-! ## Checked batch admission supplies the computation leg -/

/-- All non-computation authority legs of a private completion.  The
computation field is deliberately absent: it is constructed below from the
checked BFV batch admission.  Output authorization is retained even though the
canonical effect constructor in this module chooses `.sealed`. -/
structure CompletionLegs [DecidableEq Release]
    (request : authority.declaration.Request)
    (outcome : authority.declaration.Outcome) where
  authorization : CheckedPrivateEvidence
    authority.declaration.authorizationPortal request
  inputIdentity : authority.declaration.inputBridge.CheckedIdentity
    request.inputBridgeName request.canonicalInput request.computationInput
    request.inputValue
  outputDisclosure :
    authority.declaration.disclosureDeclaration.VerifiedRelease
      request.disclosureRequest outcome.output outcome.release
  disclosureDeclared :
    outcome.disclosureEffect =
      request.disclosureIntent.materialize outcome.release

/-- A checked all-row BFV admission fills the exact mode-evidence field of the
private completion.  `statementExact` is load-bearing: it identifies the
request/outcome statement with the batch's program, claim, representations,
and output commitment. -/
noncomputable def completionOfBatchAdmission
    [DecidableEq Release]
    {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template)
    (commitmentId : Digest)
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.statementOf request outcome =
        admission.statement commitmentId) :
    authority.declaration.Completion request outcome where
  authorization := legs.authorization
  inputIdentity := legs.inputIdentity
  computation := by
    have checked : CheckedPrivateEvidence evidencePortal
        (authority.declaration.statementOf request outcome) := by
      rw [statementExact]
      exact admission.checkedPrivateEvidence commitmentId
    simpa only [Authority.declaration] using checked
  outputDisclosure := legs.outputDisclosure
  disclosureDeclared := legs.disclosureDeclared

/-- The accepted private completion retains all exact signed integer BFV
equations.  This theorem attributes them to the checked token inside mode
evidence, not to a manifest pin or native implementation. -/
theorem completion_every_exact_integer_equation
    [DecidableEq Release]
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (completion : authority.declaration.Completion request outcome)
    (rowIndex : Fin equationsPerOwner) :
    (completion.computation.witness.outputRepresentation.equations.equation rowIndex).numerator
        completion.computation.witness.token.input.row =
      ((completion.computation.witness.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
        (completion.computation.witness.token.batch.rowCall rowIndex).witness.quotient.value := by
  exact completion.computation.witness.every_exact_integer_equation rowIndex

/-! ## Checked BFV admission enters the canonical cell kernel -/

/--
The direct positive path

`checked native buffers -> BFV completion -> sealed accepted cell effect`.

The post-cell and footprints come only from the validated family patch.  The
common authorization is indexed by the exact common request.  No turn-mode sum,
receipt augmentation, or release premise occurs.
-/
noncomputable def acceptBatchSealed
    [DecidableEq Release]
    {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.Adapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.statementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (PrivateCellEffect.family (M := M)
        (privateDeclaration := authority.declaration) adapter :
          SemanticEffectFamily S M Nullifier)
      commonRequest pre request outcome :=
  PrivateCellEffect.acceptCompletionSealed
    (privateDeclaration := authority.declaration) adapter
    commonAuthorization effectsDigestBound preRootBound
    (completionOfBatchAdmission authority admission commitmentId legs statementExact)
    validated

@[simp] theorem acceptBatchSealed_disclosure
    [DecidableEq Release]
    {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.Adapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.statementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome)) :
    (acceptBatchSealed authority admission commitmentId adapter
      commonAuthorization effectsDigestBound preRootBound legs statementExact
      validated).disclosure = .sealed :=
  rfl

/-- Any accepted BFV cell effect exposes the exact equation family carried by
its mode evidence.  Sealing has no effect on this semantic fact. -/
theorem accepted_every_exact_integer_equation
    [DecidableEq Release]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {adapter : PrivateCellEffect.Adapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (PrivateCellEffect.family (M := M)
        (privateDeclaration := authority.declaration) adapter :
          SemanticEffectFamily S M Nullifier)
      commonRequest pre request outcome)
    (rowIndex : Fin equationsPerOwner) :
    (accepted.modeEvidence.computation.witness.outputRepresentation.equations.equation rowIndex).numerator
        accepted.modeEvidence.computation.witness.token.input.row =
      ((accepted.modeEvidence.computation.witness.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
        (accepted.modeEvidence.computation.witness.token.batch.rowCall rowIndex).witness.quotient.value := by
  exact accepted.modeEvidence.computation.witness.every_exact_integer_equation rowIndex

/-! ## Direct history claim, with no legacy turn receipt -/

/-- A checked BFV batch can immediately produce the common canonical history
claim through the accepted-cell projection.  The returned claim is valid by
construction; manifest clause evidence and PCS/code membership remain later
admission obligations. -/
noncomputable def historyClaimOfBatchSealed
    [DecidableEq Release]
    {manifest : Manifest}
    {claim : PublicStatement} {template : BatchTemplate claim}
    (admission : BatchAdmission manifest claim template)
    (commitmentId : Digest)
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : PrivateCellEffect.Adapter (S := S)
      (privateDeclaration := authority.declaration) Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : authority.declaration.Request}
    {outcome : authority.declaration.Outcome}
    (commonAuthorization : Authorized portal authState commonRequest)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (legs : CompletionLegs authority request outcome)
    (statementExact :
      authority.declaration.statementOf request outcome =
        admission.statement commitmentId)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request outcome))
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    (projection : HistoryProjection
      (PrivateCellEffect.family (M := M)
        (privateDeclaration := authority.declaration) adapter :
          SemanticEffectFamily S M Nullifier) n F)
    (headerCells : HistoryAdmissionContext -> BindingIx -> F)
    (context : HistoryAdmissionContext) :
    BoundSemanticReceiptClaim n F :=
  projection.historyClaim headerCells context
    (acceptBatchSealed authority admission commitmentId adapter
      commonAuthorization effectsDigestBound preRootBound legs statementExact validated)

#print axioms completionOfBatchAdmission
#print axioms completion_every_exact_integer_equation
#print axioms acceptBatchSealed
#print axioms accepted_every_exact_integer_equation
#print axioms historyClaimOfBatchSealed

end


end Minidregg.Assurance.BfvAcceptedCellEffect
