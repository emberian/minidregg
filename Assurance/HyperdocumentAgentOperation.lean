/-
# Assurance.HyperdocumentAgentOperation -- one proof-native user/agent slice

This adapter composes existing semantic boundaries for one link or annotation
operation:

* exact v1 interface negotiation and request-indexed authority;
* an eager promise woken only by an authenticated history entry;
* shape-fixed late advice and `AcceptedCellEffect` finalization;
* atomic logical publication of the content post and derived causal event;
* canonical observer invalidation and accepted-effect receipt/history views;
* a costed durable intent with fail-closed crash/replay semantics.

It defines no scheduler, database transaction, CAS, persistence routine, or
runtime object model.  Physical joint binding remains in
`MultiCellHyperedge.HandlerBoundary`; physical installation remains conditional
on `DurableCommitProtocol.ImplementationRefinement`.
-/
import Assurance.ReactiveLifecycleHistory
import Kernel.DurableCommitProtocol
import Kernel.HyperdocumentPublication
import Theory.HyperdocumentInterface

namespace Minidregg.Assurance.HyperdocumentAgentOperation

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.ReactiveLifecycleHistory
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CanonicalReactiveView
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe q r h uBoundary uPhysical uStep
  uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence

noncomputable section

namespace HDO

abbrev Config := Minidregg.Theory.HyperdocumentOperations.Config
abbrev Declaration := Minidregg.Theory.HyperdocumentOperations.Declaration

end HDO

namespace HVE

abbrev Config := Minidregg.Kernel.HyperdocumentVersionEffects.Config
abbrev Declaration := Minidregg.Kernel.HyperdocumentVersionEffects.Declaration

end HVE

namespace HEP

abbrev Representation := Minidregg.Kernel.HyperdocumentEventLog.Representation
abbrev Store := Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store

end HEP

namespace Publication

abbrev Incidence := Minidregg.Kernel.HyperdocumentPublication.Incidence
abbrev Header := Minidregg.Kernel.HyperdocumentPublication.Header

end Publication

/-! ## One user-visible link or annotation result -/

/-- The bounded operation vocabulary in this adapter.  The full underlying
Hyperdocument action remains present; this token only selects the corresponding
canonical observer query and result type. -/
inductive SelectedAction where
  | link (payload : LinkPayload)
  | annotation (payload : AnnotatePayload)

def SelectedAction.action : SelectedAction → Action
  | .link payload => .link payload
  | .annotation payload => .annotate payload

def SelectedAction.query : SelectedAction → ContentQuery
  | .link payload => .link payload.id
  | .annotation payload => .annotation payload.id

def SelectedAction.address : SelectedAction → Hyperdocument.Address
  | .link payload => ⟨.links, payload.id⟩
  | .annotation payload => ⟨.annotations, payload.id⟩

def SelectedAction.Result : SelectedAction → Type
  | .link _ => LinkRecord
  | .annotation _ => AnnotationRecord

def SelectedAction.record (selected : SelectedAction)
    (config : HDO.Config) (declaration : HDO.Declaration) : selected.Result :=
  match selected with
  | .link payload =>
      linkRecord (declaration.operationId config) declaration.intent.author
        payload
  | .annotation payload =>
      annotationRecord (declaration.operationId config)
        declaration.intent.author payload

/-- Exact selection proof.  This is data equality, not a tag supplied to a
runtime dispatcher. -/
structure Selection (declaration : HDO.Declaration) where
  selected : SelectedAction
  actionExact : declaration.action = selected.action

def actionInvocation (interfaceId : InterfaceId)
    (declaration : HDO.Declaration) : ActionInvocation where
  interfaceId := interfaceId
  declaration := declaration

/-! ## Accepted content induces the exact interface negotiation -/

section Content

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HDO.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HDO.Declaration}

def contentCapability
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre
      contentPortal contentDeclaration) : Capability .object :=
  authenticatedObjectHead content.principal
    content.semantic.canonical.objectCapability

/-- Successful semantic content admission retains every field needed by the
typed v1 interface negotiation; no second authorization is introduced. -/
def acceptedNegotiation
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre
      contentPortal contentDeclaration) :
    ActionSuccess contentConfig contentPortal
      (CredentialAuthorityState.authState projection authorityPre) documentPre
      (actionInvocation contentMutationV1 contentDeclaration)
      (contentDeclaration.toRequest contentConfig)
      (contentCapability content) where
  requestExact := rfl
  interfaceExact := rfl
  declarationCanonical := content.semantic.canonical
  authorization := content.accepted.authorization
  capabilityAdmissible := content.namedCapabilityAdmissible
  preRootExact := content.accepted.preRootBound

/-! ## Specializing the generic promise to a content effect -/

variable
    {U : FirstOrderUniverse.{q, r}}
    {Height Condition Continuation : Type h}

/-- Eager promise shape for this exact content request.  The late advice code
may carry any first-order type, but every value maps to the already selected
unit outcome.  Consequently it cannot alter the patch, footprint, request, or
nullifier. -/
def promiseSpec
    (requestPreRootExact :
      (contentDeclaration.toRequest contentConfig).preStateRoot =
        documentPre.root)
    (promiseId : Digest) (adviceCode : U.Code)
    (condition : Condition) (deadline : Height)
    (continuation : Continuation)
    (cancelKind : ResourceKind) (cancelRequest : Request cancelKind) :
    PromiseSpec U (family (M := MDoc) contentConfig)
      Height Condition Continuation where
  promiseId := promiseId
  kind := .object
  request := contentDeclaration.toRequest contentConfig
  pre := documentPre
  declaration := contentDeclaration
  adviceCode := adviceCode
  interpretAdvice := fun _ => ()
  condition := condition
  deadline := deadline
  continuation := continuation
  nullifier := contentDeclaration.intent.nonce
  cancelKind := cancelKind
  cancelRequest := cancelRequest
  fieldFootprint := (contentDeclaration.patch contentConfig).fieldFootprint
  resourceFootprint := (contentDeclaration.patch contentConfig).resourceFootprint
  requestPreRootExact := requestPreRootExact
  requestEffectExact := rfl
  fieldFootprintExact := by intro _; rfl
  resourceFootprintExact := by intro _; rfl
  nullifierExact := by intro _; rfl

end Content

/-! ## Authenticated promise -> notify -> react -> accepted content -/

section Lifecycle

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HDO.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HDO.Declaration}
    {U : FirstOrderUniverse.{q, r}}
    {Height Condition Continuation BreakReason : Type h}
    [LinearOrder Height]
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {entryFamily : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    (rules : HistoryRules n F Height Condition BreakReason)
    (requestPreRootExact :
      (contentDeclaration.toRequest contentConfig).preStateRoot =
        documentPre.root)
    (promiseId : Digest) (adviceCode : U.Code)
    (condition : Condition) (deadline : Height)
    (continuation : Continuation)
    (cancelKind : ResourceKind) (cancelRequest : Request cancelKind)

local notation "Spec" =>
  promiseSpec (U := U) (MDoc := MDoc) requestPreRootExact promiseId adviceCode
    condition deadline continuation cancelKind cancelRequest

/-- The pre-acceptance user/agent path.  It contains only the eagerly fixed
request and an authenticated reaction; no accepted effect is an input. -/
structure ReactiveRequest : Type _ where
  selection : Selection contentDeclaration
  reaction : Reaction (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules Spec

namespace ReactiveRequest

variable {rules requestPreRootExact promiseId adviceCode condition deadline
  continuation cancelKind cancelRequest}

local notation "Reactive" =>
  ReactiveRequest (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules requestPreRootExact promiseId
    adviceCode condition deadline continuation cancelKind cancelRequest

/-- Positive construction at the sole supported mutation interface. -/
def build
    (selection : Selection contentDeclaration)
    (reaction : Reaction (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules Spec) :
    Reactive where
  selection := selection
  reaction := reaction

/-- Opening is pure and schedules nothing. -/
def promise (_operation : Reactive) :
    Promise Spec :=
  Promise.open Spec

end ReactiveRequest

/-! Acceptance first enters here, after authenticated reaction. -/

/-- Post-finalization operation.  The accepted Hyperdocument token is retained
at the exact promise indices, then supplies the typed interface negotiation. -/
structure AcceptedOperation
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre contentPortal contentDeclaration)
    (interfaceId : InterfaceId) : Type _ where
  reactive : ReactiveRequest (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules requestPreRootExact promiseId
    adviceCode condition deadline continuation cancelKind cancelRequest
  negotiation : ActionSuccess contentConfig contentPortal
    (CredentialAuthorityState.authState projection authorityPre) documentPre
    (actionInvocation interfaceId contentDeclaration)
    (contentDeclaration.toRequest contentConfig)
    (contentCapability content)

namespace AcceptedOperation

variable {rules requestPreRootExact promiseId adviceCode condition deadline
  continuation cancelKind cancelRequest}
variable
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre contentPortal contentDeclaration}

local notation "AcceptedAt" interfaceId =>
  AcceptedOperation (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
    (headerCells := headerCells) (C := C) rules requestPreRootExact promiseId
    adviceCode condition deadline continuation cancelKind cancelRequest
    content interfaceId

/-- Positive construction at the supported v1 mutation interface. -/
def build
    (reactive : ReactiveRequest (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules requestPreRootExact promiseId
      adviceCode condition deadline continuation cancelKind cancelRequest) :
    AcceptedAt contentMutationV1 where
  reactive := reactive
  negotiation := acceptedNegotiation content

/-- Finalization consumes the exact already accepted content effect. -/
def finalized
    {interfaceId : InterfaceId}
    (operation : AcceptedAt interfaceId) :
    Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := contentPortal)
      (authState := CredentialAuthorityState.authState projection authorityPre)
      rules Spec :=
  finalize rules operation.reactive.reaction content.accepted

/-- The accepted receipt is a projection of the exact finalized content effect. -/
def receiptEvent
    {interfaceId : InterfaceId}
    (operation : AcceptedAt interfaceId) :
    ReceiptEvent (family (M := MDoc) contentConfig) :=
  finalizedToReceiptEvent operation.finalized

@[simp] theorem receiptEvent_exact
    {interfaceId : InterfaceId}
    (operation : AcceptedAt interfaceId) :
    operation.receiptEvent = content.receiptEvent :=
  rfl

/-- The effect handed to publication is definitionally the effect first
supplied at finalization; no replacement post-state can be inserted. -/
@[simp] theorem finalized_content_exact
    {interfaceId : InterfaceId}
    (operation : AcceptedAt interfaceId) :
    operation.finalized.accepted = content.accepted :=
  rfl

/-- History claims are projections of the finalized accepted effect.  This
does not assert membership or physical persistence without separate evidence. -/
def historyClaim
    {interfaceId : InterfaceId}
    (projection : HistoryProjection (family (M := MDoc) contentConfig) n F)
    (finalHeaderCells : HistoryAdmissionContext → BindingIx → F)
    (context : HistoryAdmissionContext)
    (operation : AcceptedAt interfaceId) :
    BoundSemanticReceiptClaim n F :=
  finalizedHistoryClaim projection finalHeaderCells context operation.finalized

/-- Unsupported interface versions cannot inhabit the operation slice. -/
theorem no_wrong_version
    {interfaceId : InterfaceId}
    (wrong : interfaceId.version ≠ .v1) :
    IsEmpty (AcceptedAt interfaceId) :=
  ⟨fun operation =>
    (no_action_success_wrong_version wrong).false operation.negotiation⟩

/-- The exact document target must be inside the retained capability scope. -/
theorem no_outside_scope
    {interfaceId : InterfaceId}
    (outside :
      (⟨contentDeclaration.intent.document.digest.value⟩ : ResourceId .object) ∉
        (contentCapability content).scope.targets) :
    IsEmpty (AcceptedAt interfaceId) :=
  ⟨fun operation =>
    (no_action_success_outside_scope outside).false operation.negotiation⟩

end AcceptedOperation

end Lifecycle

/-! ## Content + derived event as one logical publication -/

section Publication

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HDO.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HDO.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre
      contentPortal contentDeclaration}
    {representation : HEP.Representation Digest}
    {store : HEP.Store}
    {eventConfig : HVE.Config}
    {eventPortal : Portal}
    {eventDeclaration : HVE.Declaration}
    (event : Minidregg.Kernel.HyperdocumentVersionEffects.Accepted content
      representation store eventConfig eventPortal
      eventDeclaration)
    (header : Publication.Header)
    (contentCellId eventCellId : Digest)

local notation "PubDeclaration" =>
  Minidregg.Kernel.HyperdocumentPublication.declaration content event header
    contentCellId eventCellId

local notation "PubAccepted" =>
  Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
    contentCellId eventCellId

local notation "PubLaw" =>
  Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event header
    contentCellId eventCellId

/-- Published operation retains the exact accepted effect produced by
finalization and the two-incidence logical commit. -/
structure PublishedOperation
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HDO.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HDO.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre
      contentPortal contentDeclaration}
    {representation : HEP.Representation Digest}
    {store : HEP.Store}
    {eventConfig : HVE.Config}
    {eventPortal : Portal}
    {eventDeclaration : HVE.Declaration}
    (event : Minidregg.Kernel.HyperdocumentVersionEffects.Accepted content
      representation store eventConfig eventPortal
      eventDeclaration)
    (header : Publication.Header)
    (contentCellId eventCellId : Digest)
    (boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentPublication.declaration content event
        header contentCellId eventCellId)) : Type _ where
  finalizedContent : AcceptedCellEffect
    (portal := contentPortal)
    (authState := CredentialAuthorityState.authState projection authorityPre)
    (family (M := MDoc) contentConfig)
    (contentDeclaration.toRequest contentConfig) documentPre
    contentDeclaration ()
  finalizedExact : finalizedContent = content.accepted
  publication : Minidregg.Kernel.MultiCellHyperedge.Commit
    (Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event
      header contentCellId eventCellId)
    (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event
      header contentCellId eventCellId)
    boundary
  contentPostExact : publication.post .content =
    content.accepted.prepared.post
  eventPostContains :
    (publication.post .eventLog).logical.fields
      ⟨Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events,
        eventDeclaration.key eventConfig⟩ = some eventDeclaration.record
  eventReplayRejected :
    ¬ (Minidregg.Kernel.HyperdocumentEventLog.Sparse.appendOp
      (eventDeclaration.stored eventConfig event.sourceWellFormed)).Enabled
      event.sparse.post.logical

namespace PublishedOperation

variable
    {event : Minidregg.Kernel.HyperdocumentVersionEffects.Accepted content
      representation store eventConfig eventPortal eventDeclaration}
    {header : Publication.Header}
    {contentCellId eventCellId : Digest}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      PubDeclaration}

/-- Ordinary construction through the existing publication kernel. -/
def build
    (finalizedContent : AcceptedCellEffect
      (portal := contentPortal)
      (authState := CredentialAuthorityState.authState projection authorityPre)
      (family (M := MDoc) contentConfig)
      (contentDeclaration.toRequest contentConfig) documentPre
      contentDeclaration ())
    (finalizedExact : finalizedContent = content.accepted)
    (domainExact : eventConfig.requestDomain = contentConfig.requestDomain)
    (cellIdsDistinct : contentCellId ≠ eventCellId)
    (jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput)
    (jointCommitExact : jointInput.jointCommit = header.apex)
    (jointEvidence : boundary.Evidence PubAccepted jointInput) :
    PublishedOperation event header contentCellId eventCellId boundary where
  finalizedContent := finalizedContent
  finalizedExact := finalizedExact
  publication :=
    Minidregg.Kernel.HyperdocumentPublication.commit content event header
      contentCellId eventCellId domainExact cellIdsDistinct boundary jointInput
      jointCommitExact jointEvidence
  contentPostExact := rfl
  eventPostContains := event.post_contains
  eventReplayRejected := event.duplicate_rejected

end PublishedOperation

end Publication

/-! ## Canonical observer invalidation for the selected action -/

section View

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HDO.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HDO.Declaration}
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre
      contentPortal contentDeclaration)

theorem selected_address_touched (selection : Selection contentDeclaration) :
    selection.selected.address ∈
      content.accepted.prepared.delta.fieldFootprint := by
  rw [AcceptedCellEffect.prepared_fieldFootprint]
  rcases selection with ⟨selected, actionExact⟩
  cases selected with
  | link payload =>
      simp [HyperdocumentOperations.family, Declaration.patch,
        Declaration.fieldWrites, Declaration.packedWrites, Action.packedWrites,
        linkWrites, PackedWrite.toFieldWrite, PackedWrite.address,
        SelectedAction.address, SelectedAction.action, actionExact]
      exact Finset.mem_singleton_self _
  | annotation payload =>
      simp [HyperdocumentOperations.family, Declaration.patch,
        Declaration.fieldWrites, Declaration.packedWrites, Action.packedWrites,
        annotateWrites, PackedWrite.toFieldWrite, PackedWrite.address,
        SelectedAction.address, SelectedAction.action, actionExact]
      exact Finset.mem_singleton_self _

/-- The exact selected observer is dirty in the accepted canonical delta. -/
theorem selected_view_dirty (selection : Selection contentDeclaration) :
    ContentQuery.lens.Dirty selection.selected.query
      content.accepted.prepared.delta := by
  left
  exact ⟨selection.selected.address,
    Finset.mem_inter.mpr ⟨by
      cases selection.selected <;>
        apply Finset.mem_singleton.mpr <;> rfl,
      selected_address_touched content selection⟩⟩

end View

/-! ## Costed durable intent; physical execution remains conditional -/

section Durable

open Minidregg.Kernel.DurableCommitProtocol

variable
    {Incidence : Type*} [Fintype Incidence] [DecidableEq Incidence]
    {cells : Minidregg.Kernel.MultiCellHyperedge.CellFamily Incidence}
    {declaration : Minidregg.Kernel.MultiCellHyperedge.Declaration cells}
    {Coordinate Balance : Type*} [AddCommMonoid Balance]
    {law : Minidregg.Kernel.MultiCellHyperedge.ResourceLaw declaration
      Coordinate Balance}
    {accepted : declaration.AcceptedLegs}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary declaration}
    (commit : Minidregg.Kernel.MultiCellHyperedge.Commit law accepted boundary)

/-- Exact quote and funding for one already accepted joint publication. -/
structure DurablePlan where
  bounded : BoundedMultiCellCommit commit
    Minidregg.Kernel.MultiCellHyperedge.JointCommitInput commit.jointInput
  available : Charge
  funding : ChargeReceipt available bounded.quote

namespace DurablePlan

variable {commit}

def intent (plan : DurablePlan commit) :
    Intent Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput :=
  Intent.ofMultiCellJointReceipt commit plan.bounded plan.available plan.funding

@[simp] theorem intent_root_count (plan : DurablePlan commit) :
    plan.intent.rootWrites.length = Fintype.card Incidence :=
  Intent.ofMultiCell_rootWrites_length commit commit.jointInput plan.bounded
    plan.available plan.funding

theorem no_partial_commit
    [DecidableEq
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)]
    (plan : DurablePlan commit) (schedule : Schedule)
    (before : Snapshot Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput) :
    (execute schedule before plan.intent).storeAfter before = before ∨
      (execute schedule before plan.intent).storeAfter before =
        Snapshot.install before plan.intent :=
  execute_no_partial_commit schedule before plan.intent

@[simp] theorem retry_after_install
    [DecidableEq
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)]
    (plan : DurablePlan commit) (schedule : Schedule)
    (before : Snapshot Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput) :
    execute schedule (Snapshot.install before plan.intent) plan.intent =
      .replayed plan.intent :=
  execute_retry_after_install schedule before plan.intent

/-- A physical step yields atomicity only through the explicit implementation
simulation premise. -/
theorem physical_step_no_partial
    [DecidableEq
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)]
    (plan : DurablePlan commit)
    {PhysicalState : Type uPhysical}
    {PhysicalStep : PhysicalState →
      Intent Digest Digest
        (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
        Minidregg.Kernel.MultiCellHyperedge.JointCommitInput →
      PhysicalState → Type uStep}
    {Represents : PhysicalState → Snapshot Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput → Prop}
    (refinement : ImplementationRefinement Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput
      PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : Snapshot Digest Digest
      (Minidregg.Kernel.MultiCellHyperedge.JointNullifier accepted)
      Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore plan.intent physicalAfter) :
    ∃ modelAfter,
      Represents physicalAfter modelAfter ∧
        (modelAfter = modelBefore ∨
          modelAfter = Snapshot.install modelBefore plan.intent) :=
  Minidregg.Kernel.DurableCommitProtocol.physical_step_no_partial_commit
    refinement represented stepped

end DurablePlan

end Durable

#print axioms acceptedNegotiation
#print axioms promiseSpec
#print axioms AcceptedOperation.finalized_content_exact
#print axioms AcceptedOperation.no_wrong_version
#print axioms AcceptedOperation.no_outside_scope
#print axioms AcceptedOperation.historyClaim
#print axioms selected_view_dirty
#print axioms DurablePlan.no_partial_commit
#print axioms DurablePlan.retry_after_install
#print axioms DurablePlan.physical_step_no_partial

end

end Minidregg.Assurance.HyperdocumentAgentOperation
