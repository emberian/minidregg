/-
# Theory.HyperdocumentInterface -- first-order interfaces for users and agents

OLE/DCOM made compound documents, interface discovery, and typed method sets
ordinary application concepts.  This module keeps those useful affordances
without importing remote-object authority: there are no object pointers,
callbacks, activation hooks, or method dispatch functions here.  An invocation
is first-order data, its arguments have a lawful codec, and successful
negotiation retains the existing `TypedAuthorization.Authorized` token at the
complete request index.

Direct content reads are pure projections of an exact finite canonical
`Hyperdocument.cellSchema` footprint.  Backlink and version queries are only
history declarations: resolving them requires the authenticated history layer.
In particular this module makes no claim that a host search index is complete,
that a version is final, or that any logical result was durably persisted.

Action negotiation exposes the existing first-order
`HyperdocumentOperations.Declaration`.  It does not manufacture an
`AcceptedCellEffect` or a post-state; the ordinary operation admission path
must still validate the declaration, patch, authority cell, and canonical
pre-cell.
-/
import Theory.CanonicalReactiveView
import Theory.HyperdocumentOperations

namespace Minidregg.Theory.HyperdocumentInterface

open IndexedProgram
open TypedAuthorization
open Hyperdocument
open HyperdocumentOperations
open CanonicalReactiveView

set_option autoImplicit false

/-! ## Versioned interface identities -/

/-- Interface schemas name semantic contracts, not remotely activatable
classes or host object layouts. -/
inductive InterfaceSchema where
  | contentRead
  | contentMutation
  | historyRead
  deriving DecidableEq, Repr

/-- `reservedV2` is deliberately unsupported.  Its presence makes exact
version negotiation and downgrade/upgrade rejection visible in the type. -/
inductive InterfaceVersion where
  | v1
  | reservedV2
  deriving DecidableEq, Repr

structure InterfaceId where
  schema : InterfaceSchema
  version : InterfaceVersion
  deriving DecidableEq, Repr

def contentReadV1 : InterfaceId := ⟨.contentRead, .v1⟩
def contentMutationV1 : InterfaceId := ⟨.contentMutation, .v1⟩
def historyReadV1 : InterfaceId := ⟨.historyRead, .v1⟩

/-! ## Exact content views and honest history query shapes -/

/-- Reads which are pure projections of the mutable canonical content cell. -/
inductive ContentQuery where
  | link (id : LinkId)
  | annotation (id : AnnotationId)
  deriving DecidableEq

namespace ContentQuery

/-- The complete canonical field footprint inspected by a direct query. -/
def footprint : ContentQuery → Finset Address
  | .link id => {⟨.links, id⟩}
  | .annotation id => {⟨.annotations, id⟩}

/-- Result type is selected by the query constructor. -/
def View : ContentQuery → Type
  | .link _ => Option LinkRecord
  | .annotation _ => Option AnnotationRecord

/-- Pure projection from the sole canonical logical state. -/
def project (query : ContentQuery)
    (state : CellState.LogicalState cellSchema) : query.View :=
  match query with
  | .link id => Hyperdocument.lookup state .links id
  | .annotation id => Hyperdocument.lookup state .annotations id

/-- A direct query may not use authority for one document to read a record
owned by another.  Absence is allowed and discloses no record. -/
def OwnedBy (query : ContentQuery) (document : DocumentId)
    (state : CellState.LogicalState cellSchema) : Prop :=
  match query with
  | .link id => ∀ record,
      Hyperdocument.lookup state .links id = some record →
        record.sourceDocument = document
  | .annotation id => ∀ record,
      Hyperdocument.lookup state .annotations id = some record →
        record.document = document

/-- The canonical reactive lens for direct Hyperdocument reads.  Its resource
footprint is empty because `cellSchema` has no resource lane. -/
def lens : ObserverLens cellSchema ContentQuery View where
  fieldDependencies := footprint
  resourceDependencies := fun _ => ∅
  project := project
  locality := by
    intro query left right fieldsExact _resourcesExact
    cases query with
    | link id =>
        simpa [project, Hyperdocument.lookup] using
          fieldsExact (⟨.links, id⟩ : Address)
            (Finset.mem_singleton.mpr rfl)
    | annotation id =>
        simpa [project, Hyperdocument.lookup] using
          fieldsExact (⟨.annotations, id⟩ : Address)
            (Finset.mem_singleton.mpr rfl)

@[simp] theorem lens_fieldDependencies (query : ContentQuery) :
    lens.fieldDependencies query = query.footprint :=
  rfl

@[simp] theorem lens_resourceDependencies (query : ContentQuery) :
    lens.resourceDependencies query = ∅ :=
  rfl

end ContentQuery

/-- Explicit sequence bounds for a later authenticated history derivation. -/
structure HistorySlice where
  historyDomain : Digest
  firstSequence : Nat
  pastSequence : Nat
  deriving DecidableEq, Repr

def HistorySlice.WellFormed (slice : HistorySlice) : Prop :=
  slice.firstSequence < slice.pastSequence

/-- History queries deliberately carry no host lookup function.  Backlinks are
requested only inside an explicit history slice, and a version query names one
exact content-addressed event id. -/
inductive HistoryQuery where
  | backlinks (slice : HistorySlice) (target : StoredSourceIdentity)
  | version (id : VersionEventId)
  deriving DecidableEq

def HistoryQuery.WellFormed : HistoryQuery → Prop
  | .backlinks slice _ => slice.WellFormed
  | .version _ => True

/-- All first-order query shapes supported by the v1 interface family. -/
inductive Query where
  | content (query : ContentQuery)
  | history (query : HistoryQuery)
  deriving DecidableEq

def Query.requiredInterface : Query → InterfaceId
  | .content _ => contentReadV1
  | .history _ => historyReadV1

def Query.WellFormed : Query → Prop
  | .content _ => True
  | .history query => query.WellFormed

/-- History queries have no mutable-content footprint by construction.  Their
answers must come from a later authenticated history adapter. -/
def Query.contentFootprint : Query → Finset Address
  | .content query => query.footprint
  | .history _ => ∅

@[simp] theorem history_query_contentFootprint_empty (query : HistoryQuery) :
    (Query.history query).contentFootprint = ∅ :=
  rfl

/-! ## Canonical query arguments and complete requests -/

/-- The exact semantic query argument.  Interface id and target document are
inside the lawful argument codec, so neither is an out-of-band dispatch hint. -/
structure QueryArgument where
  interfaceId : InterfaceId
  document : DocumentId
  query : Query
  deriving DecidableEq

structure QueryEnvelope where
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  nonce : Nat
  height : Height
  expectedPreRoot : Digest
  policyId : PolicyId
  policyEpoch : Epoch
  cost : Nat
  deriving DecidableEq, Repr

structure QueryDeclaration where
  argument : QueryArgument
  request : QueryEnvelope
  deriving DecidableEq

/-- Family-wide pure configuration.  `digestBytes` is an abstract addressing
operation, not a soundness theorem or callback capable of supplying a result. -/
structure QueryConfig where
  argumentCodec : LawfulCodec QueryArgument
  digestBytes : List UInt8 → Digest
  requestDomain : Digest
  semanticRelation : Digest
  noEffectDigest : Digest

def QueryConfig.argumentDigest (config : QueryConfig)
    (argument : QueryArgument) : Digest :=
  config.digestBytes (config.argumentCodec.encode argument)

def QueryDeclaration.toRequest (config : QueryConfig)
    (declaration : QueryDeclaration) : Request .object where
  domain := config.requestDomain
  semantics := config.semanticRelation
  federation := declaration.request.federation
  subject := declaration.request.subject
  subjectKeyEpoch := declaration.request.subjectKeyEpoch
  target := ⟨declaration.argument.document.digest.value⟩
  verb := .observeObject
  argsDigest := config.argumentDigest declaration.argument
  effectsDigest := config.noEffectDigest
  nonce := declaration.request.nonce
  height := declaration.request.height
  preStateRoot := declaration.request.expectedPreRoot
  policyId := declaration.request.policyId
  policyEpoch := declaration.request.policyEpoch
  cost := declaration.request.cost

@[simp] theorem QueryDeclaration.request_target
    (config : QueryConfig) (declaration : QueryDeclaration) :
    (declaration.toRequest config).target =
      (⟨declaration.argument.document.digest.value⟩ : ResourceId .object) :=
  rfl

@[simp] theorem QueryDeclaration.request_verb
    (config : QueryConfig) (declaration : QueryDeclaration) :
    (declaration.toRequest config).verb = Verb.observeObject :=
  rfl

@[simp] theorem QueryDeclaration.request_argsDigest
    (config : QueryConfig) (declaration : QueryDeclaration) :
    (declaration.toRequest config).argsDigest =
      config.argumentDigest declaration.argument :=
  rfl

@[simp] theorem QueryDeclaration.request_preRoot
    (config : QueryConfig) (declaration : QueryDeclaration) :
    (declaration.toRequest config).preStateRoot =
      declaration.request.expectedPreRoot :=
  rfl

@[simp] theorem QueryConfig.decode_encode_argument
    (config : QueryConfig) (argument : QueryArgument) :
    config.argumentCodec.decode (config.argumentCodec.encode argument) =
      some argument :=
  config.argumentCodec.decode_encode argument

/-! ## Action invocations reuse the sole Hyperdocument effect declaration -/

structure ActionInvocation where
  interfaceId : InterfaceId
  declaration : HyperdocumentOperations.Declaration

/-- Before digesting the `OperationIntent`, the existing action codec binds
the exact action bytes selected by the declaration. -/
theorem action_argument_bytes_exact
    (config : HyperdocumentOperations.Config)
    (invocation : ActionInvocation)
    (canonical : invocation.declaration.Canonical config) :
    invocation.declaration.intent.actionBytes =
      config.actionCodec.encode invocation.declaration.action :=
  canonical.actionBytesExact

/-! ## Negotiation success and fail-closed decisions -/

/-- A successful content/history query retains exactly one current
request-indexed authorization and one capability scope judgment for the same
request.  It carries the actual canonical pre-cell but no post-state. -/
structure QuerySuccess
    {M : Hyperdocument.Materializer Digest}
    (config : QueryConfig) (portal : Portal) (authState : AuthState)
    (pre : Hyperdocument.Cell M) (declaration : QueryDeclaration)
    (request : Request .object) (capability : Capability .object) : Type where
  requestExact : request = declaration.toRequest config
  interfaceExact : declaration.argument.interfaceId =
    declaration.argument.query.requiredInterface
  queryWellFormed : declaration.argument.query.WellFormed
  authorization : Authorized portal authState request
  capabilityAdmissible : capability.Admissible authState request
  preRootExact : request.preStateRoot = pre.root
  contentOwned : match declaration.argument.query with
    | .content query => query.OwnedBy declaration.argument.document pre.logical
    | .history _ => True

/-- Action negotiation retains the existing exact operation request and pure
declaration.  Valid operation evidence and `AcceptedCellEffect` construction
remain later obligations; there is still no post-state here. -/
structure ActionSuccess
    {M : Hyperdocument.Materializer Digest}
    (config : HyperdocumentOperations.Config)
    (portal : Portal) (authState : AuthState)
    (pre : Hyperdocument.Cell M) (invocation : ActionInvocation)
    (request : Request .object) (capability : Capability .object) : Type where
  requestExact : request = invocation.declaration.toRequest config
  interfaceExact : invocation.interfaceId = contentMutationV1
  declarationCanonical : invocation.declaration.Canonical config
  authorization : Authorized portal authState request
  capabilityAdmissible : capability.Admissible authState request
  preRootExact : request.preStateRoot = pre.root

inductive Invocation where
  | query (declaration : QueryDeclaration)
  | action (invocation : ActionInvocation)

def Invocation.Success
    {M : Hyperdocument.Materializer Digest}
    (queryConfig : QueryConfig)
    (actionConfig : HyperdocumentOperations.Config)
    (portal : Portal) (authState : AuthState) (pre : Hyperdocument.Cell M)
    (request : Request .object) (capability : Capability .object) :
    Invocation → Type
  | .query declaration =>
      QuerySuccess queryConfig portal authState pre declaration request capability
  | .action invocation =>
      ActionSuccess actionConfig portal authState pre invocation request capability

/-- Existential capability selection occurs only in the successful branch. -/
structure Negotiated
    {M : Hyperdocument.Materializer Digest}
    (queryConfig : QueryConfig)
    (actionConfig : HyperdocumentOperations.Config)
    (portal : Portal) (authState : AuthState) (pre : Hyperdocument.Cell M)
    (invocation : Invocation) (request : Request .object) : Type where
  capability : Capability .object
  success : invocation.Success queryConfig actionConfig portal authState pre
    request capability

inductive RejectReason where
  | unsupportedInterface
  | malformedHistorySlice
  | requestMismatch
  | unauthorized
  | outsideCapabilityScope
  | stalePreRoot
  | crossDocumentRead
  deriving DecidableEq, Repr

/-- Rejection contains only a reason.  In particular it cannot return a
capability, canonical post-state, activation handle, or callback. -/
inductive Decision
    {M : Hyperdocument.Materializer Digest}
    (queryConfig : QueryConfig)
    (actionConfig : HyperdocumentOperations.Config)
    (portal : Portal) (authState : AuthState) (pre : Hyperdocument.Cell M)
    (invocation : Invocation) (request : Request .object) : Type where
  | rejected (reason : RejectReason) :
      Decision queryConfig actionConfig portal authState pre invocation request
  | accepted
      (negotiated : Negotiated queryConfig actionConfig portal authState pre
        invocation request) :
      Decision queryConfig actionConfig portal authState pre invocation request

/-! ## Exact retained-request projections -/

namespace QuerySuccess

variable
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {declaration : QueryDeclaration}
    {request : Request .object} {capability : Capability .object}

@[simp] theorem target_exact
    (success : QuerySuccess config portal authState pre declaration request
      capability) :
    request.target =
      (⟨declaration.argument.document.digest.value⟩ : ResourceId .object) := by
  simpa [QueryDeclaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.target)
      success.requestExact

@[simp] theorem verb_exact
    (success : QuerySuccess config portal authState pre declaration request
      capability) :
    request.verb = Verb.observeObject := by
  simpa [QueryDeclaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.verb)
      success.requestExact

@[simp] theorem argsDigest_exact
    (success : QuerySuccess config portal authState pre declaration request
      capability) :
    request.argsDigest = config.argumentDigest declaration.argument := by
  simpa [QueryDeclaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.argsDigest)
      success.requestExact

/-- Direct reads expose only the pure canonical projection. -/
def contentView
    (query : ContentQuery)
    (_success : QuerySuccess config portal authState pre
      { declaration with argument :=
          { declaration.argument with query := .content query } }
      request capability) : query.View :=
  query.project pre.logical

end QuerySuccess

namespace ActionSuccess

variable
    {M : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {invocation : ActionInvocation}
    {request : Request .object} {capability : Capability .object}

@[simp] theorem target_exact
    (success : ActionSuccess config portal authState pre invocation request
      capability) :
    request.target =
      (⟨invocation.declaration.intent.document.digest.value⟩ :
        ResourceId .object) := by
  simpa [HyperdocumentOperations.Declaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.target)
      success.requestExact

@[simp] theorem verb_exact
    (success : ActionSuccess config portal authState pre invocation request
      capability) :
    request.verb = Verb.mutateObject := by
  simpa [HyperdocumentOperations.Declaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.verb)
      success.requestExact

@[simp] theorem argsDigest_exact
    (success : ActionSuccess config portal authState pre invocation request
      capability) :
    request.argsDigest =
      (invocation.declaration.operationId config).digest := by
  simpa [HyperdocumentOperations.Declaration.toRequest] using
    congrArg (fun candidate : Request .object => candidate.argsDigest)
      success.requestExact

end ActionSuccess

/-! ## Negative teeth -/

theorem no_query_success_wrong_interface
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {declaration : QueryDeclaration}
    {request : Request .object} {capability : Capability .object}
    (wrong : declaration.argument.interfaceId ≠
      declaration.argument.query.requiredInterface) :
    IsEmpty (QuerySuccess config portal authState pre declaration request
      capability) :=
  ⟨fun success => wrong success.interfaceExact⟩

theorem no_query_success_reserved_version
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {declaration : QueryDeclaration}
    {request : Request .object} {capability : Capability .object}
    (reserved : declaration.argument.interfaceId.version = .reservedV2) :
    IsEmpty (QuerySuccess config portal authState pre declaration request
      capability) := by
  apply no_query_success_wrong_interface
  intro equal
  have versionEqual := congrArg InterfaceId.version equal
  rw [reserved] at versionEqual
  have requiredV1 :
      declaration.argument.query.requiredInterface.version = .v1 := by
    cases declaration.argument.query <;> rfl
  exact InterfaceVersion.noConfusion (versionEqual.trans requiredV1)

theorem no_query_success_outside_scope
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {declaration : QueryDeclaration}
    {request : Request .object} {capability : Capability .object}
    (outside :
      (⟨declaration.argument.document.digest.value⟩ : ResourceId .object) ∉
        capability.scope.targets) :
    IsEmpty (QuerySuccess config portal authState pre declaration request
      capability) := by
  constructor
  intro success
  apply outside
  simpa [success.target_exact] using success.capabilityAdmissible.scope.target

theorem no_query_success_wrong_target
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {declaration : QueryDeclaration}
    {request : Request .object} {capability : Capability .object}
    (wrong : request.target ≠
      (⟨declaration.argument.document.digest.value⟩ : ResourceId .object)) :
    IsEmpty (QuerySuccess config portal authState pre declaration request
      capability) :=
  ⟨fun success => wrong success.target_exact⟩

theorem no_action_success_wrong_version
    {M : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {invocation : ActionInvocation}
    {request : Request .object} {capability : Capability .object}
    (wrong : invocation.interfaceId.version ≠ .v1) :
    IsEmpty (ActionSuccess config portal authState pre invocation request
      capability) := by
  constructor
  intro success
  apply wrong
  simpa [contentMutationV1] using
    congrArg InterfaceId.version success.interfaceExact

theorem no_action_success_outside_scope
    {M : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {invocation : ActionInvocation}
    {request : Request .object} {capability : Capability .object}
    (outside :
      (⟨invocation.declaration.intent.document.digest.value⟩ :
        ResourceId .object) ∉ capability.scope.targets) :
    IsEmpty (ActionSuccess config portal authState pre invocation request
      capability) := by
  constructor
  intro success
  apply outside
  simpa [success.target_exact] using success.capabilityAdmissible.scope.target

theorem no_action_success_wrong_target
    {M : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {pre : Hyperdocument.Cell M} {invocation : ActionInvocation}
    {request : Request .object} {capability : Capability .object}
    (wrong : request.target ≠
      (⟨invocation.declaration.intent.document.digest.value⟩ :
        ResourceId .object)) :
    IsEmpty (ActionSuccess config portal authState pre invocation request
      capability) :=
  ⟨fun success => wrong success.target_exact⟩

/-- Constructor disjointness is the formal fail-closed tooth: the rejected
branch cannot be reinterpreted as a successful negotiation. -/
theorem rejected_ne_accepted
    {M : Hyperdocument.Materializer Digest}
    {queryConfig : QueryConfig}
    {actionConfig : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState} {pre : Hyperdocument.Cell M}
    {invocation : Invocation} {request : Request .object}
    (reason : RejectReason)
    (negotiated : Negotiated queryConfig actionConfig portal authState pre
      invocation request) :
    Decision.rejected reason ≠ Decision.accepted negotiated := by
  intro equal
  cases equal

/-! ## Version reads require an exact content-addressed event value -/

/-- Pure exact projection for a version query.  `StoredVersionEvent` proves
content addressing and causal well-formedness, but it does not prove membership
in an admitted history.  This structure deliberately contains no finality,
persistence, availability, or global-index claim. -/
structure VersionProjection
    (scheme : CausalVersionDag.ContentAddressing)
    (document : DocumentId) (id : VersionEventId) where
  stored : StoredVersionEvent scheme
  keyExact : stored.key = id
  documentExact : stored.record.document = document

@[simp] theorem VersionProjection.record_key_exact
    {scheme : CausalVersionDag.ContentAddressing}
    {document : DocumentId} {id : VersionEventId}
    (projection : VersionProjection scheme document id) :
    projection.stored.key = id :=
  projection.keyExact

#print axioms ContentQuery.lens
#print axioms QueryConfig.decode_encode_argument
#print axioms no_query_success_wrong_interface
#print axioms no_query_success_reserved_version
#print axioms no_query_success_outside_scope
#print axioms no_query_success_wrong_target
#print axioms no_action_success_wrong_version
#print axioms no_action_success_outside_scope
#print axioms no_action_success_wrong_target
#print axioms rejected_ne_accepted

end Minidregg.Theory.HyperdocumentInterface
