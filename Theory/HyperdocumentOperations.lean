/-
# Theory.HyperdocumentOperations -- first-order accepted content effects

The action grammar below is the sole source of Hyperdocument content patches.
Declarations are first-order data.  They derive one exact typed write list,
footprint, effect digest, request, eager nullifier, and canonical post through
`AcceptedCellEffect`; no callback supplies a post-state or semantic decision.

Mutable content stores the staged `OperationId`.  A final causal event is built
only after this content effect has an actual post root and is appended through
the separate event-log family.
-/
import Theory.HyperdocumentOperationIntent
import Theory.StableRanges

namespace Minidregg.Theory.HyperdocumentOperations

open IndexedProgram
open TypedAuthorization
open Hyperdocument
open HyperdocumentOperationIntent

set_option autoImplicit false

/-! ## First-order action payloads -/

structure CreatePayload where
  documentId : DocumentId
  rootElementId : ElementId
  schema : Digest
  rootBody : ElementBody
  deriving DecidableEq

structure EditAtomPayload where
  atomId : AtomId
  before : AtomRecord
  kind : AtomKind
  payload : List UInt8
  tombstone : Bool
  deriving DecidableEq, Repr

structure LinkPayload where
  id : LinkId
  sourceDocument : DocumentId
  source : Option StableRange
  target : LinkTarget
  relation : Digest
  deriving DecidableEq

/-- A transclusion always writes its durable reference and the matching forward
link in the same content patch.  Backlinks remain derived history. -/
structure TranscludePayload where
  id : TransclusionId
  forwardLinkId : LinkId
  hostDocument : DocumentId
  source : Option StableRange
  reference : StoredTransclusionRef
  relation : Digest
  disclosurePolicy : Digest
  deriving DecidableEq

structure MarkPayload where
  id : MarkId
  document : DocumentId
  range : StableRange
  kind : Digest
  payload : List UInt8
  visibilityPolicy : Digest
  deriving DecidableEq, Repr

structure AnnotatePayload where
  id : AnnotationId
  document : DocumentId
  range : Option StableRange
  body : DocumentId
  visibilityPolicy : Digest
  deriving DecidableEq, Repr

inductive Action where
  | create (payload : CreatePayload)
  | editAtom (payload : EditAtomPayload)
  | link (payload : LinkPayload)
  | transclude (payload : TranscludePayload)
  | mark (payload : MarkPayload)
  | annotate (payload : AnnotatePayload)

inductive ActionTag where
  | create | edit | link | transclude | mark | annotate
  deriving DecidableEq, Repr

def Action.tag : Action -> ActionTag
  | .create _ => .create
  | .editAtom _ => .edit
  | .link _ => .link
  | .transclude _ => .transclude
  | .mark _ => .mark
  | .annotate _ => .annotate

def Action.document : Action -> DocumentId
  | .create payload => payload.documentId
  | .editAtom payload => payload.before.document
  | .link payload => payload.sourceDocument
  | .transclude payload => payload.hostDocument
  | .mark payload => payload.document
  | .annotate payload => payload.document

/-! ## Exact typed writes -/

structure ExactWrite (space : Namespace) where
  key : Key space
  expected : Option (Value space)
  replacement : Value space

structure PackedWrite where
  space : Namespace
  write : ExactWrite space

def PackedWrite.address (write : PackedWrite) : Address :=
  ⟨write.space, write.write.key⟩

def PackedWrite.toFieldWrite (write : PackedWrite) :
    CellState.FieldWrite cellSchema where
  field := write.address
  value := some write.write.replacement

def createWrites (operation : OperationId) (author : PrincipalRef)
    (payload : CreatePayload) : List PackedWrite :=
  [ ⟨.documents,
      { key := payload.documentId
        expected := none
        replacement :=
          { rootElement := payload.rootElementId
            schema := payload.schema
            createdBy := author
            createdAt := operation } }⟩,
    ⟨.elements,
      { key := payload.rootElementId
        expected := none
        replacement :=
          { document := payload.documentId
            parent := none
            body := payload.rootBody
            createdBy := author
            createdAt := operation
            tombstonedAt := none } }⟩ ]

def editAtomWrites (operation : OperationId)
    (payload : EditAtomPayload) : List PackedWrite :=
  [ ⟨.atoms,
      { key := payload.atomId
        expected := some payload.before
        replacement :=
          { payload.before with
            kind := payload.kind
            payload := payload.payload
            tombstonedAt :=
              if payload.tombstone then some operation
              else payload.before.tombstonedAt } }⟩ ]

def linkRecord (operation : OperationId) (author : PrincipalRef)
    (payload : LinkPayload) : LinkRecord :=
  { sourceDocument := payload.sourceDocument
    source := payload.source
    target := payload.target
    relation := payload.relation
    author := author
    operation := operation
    tombstonedAt := none }

def linkWrites (operation : OperationId) (author : PrincipalRef)
    (payload : LinkPayload) : List PackedWrite :=
  [ ⟨.links,
      { key := payload.id
        expected := none
        replacement := linkRecord operation author payload }⟩ ]

def transclusionRecord (operation : OperationId) (author : PrincipalRef)
    (payload : TranscludePayload) : TransclusionRecord :=
  { hostDocument := payload.hostDocument
    reference := payload.reference
    author := author
    operation := operation
    disclosurePolicy := payload.disclosurePolicy
    tombstonedAt := none }

def transclusionForwardLink (operation : OperationId) (author : PrincipalRef)
    (payload : TranscludePayload) : LinkRecord :=
  { sourceDocument := payload.hostDocument
    source := payload.source
    target := .transclusion payload.id payload.reference
    relation := payload.relation
    author := author
    operation := operation
    tombstonedAt := none }

def transcludeWrites (operation : OperationId) (author : PrincipalRef)
    (payload : TranscludePayload) : List PackedWrite :=
  [ ⟨.transclusions,
      { key := payload.id
        expected := none
        replacement := transclusionRecord operation author payload }⟩,
    ⟨.links,
      { key := payload.forwardLinkId
        expected := none
        replacement := transclusionForwardLink operation author payload }⟩ ]

def markRecord (operation : OperationId) (author : PrincipalRef)
    (payload : MarkPayload) : MarkRecord :=
  { document := payload.document
    range := payload.range
    kind := payload.kind
    payload := payload.payload
    author := author
    operation := operation
    visibilityPolicy := payload.visibilityPolicy
    tombstonedAt := none }

def markWrites (operation : OperationId) (author : PrincipalRef)
    (payload : MarkPayload) : List PackedWrite :=
  [ ⟨.marks,
      { key := payload.id
        expected := none
        replacement := markRecord operation author payload }⟩ ]

def annotationRecord (operation : OperationId) (author : PrincipalRef)
    (payload : AnnotatePayload) : AnnotationRecord :=
  { document := payload.document
    range := payload.range
    body := payload.body
    author := author
    operation := operation
    visibilityPolicy := payload.visibilityPolicy
    tombstonedAt := none }

def annotateWrites (operation : OperationId) (author : PrincipalRef)
    (payload : AnnotatePayload) : List PackedWrite :=
  [ ⟨.annotations,
      { key := payload.id
        expected := none
        replacement := annotationRecord operation author payload }⟩ ]

/-! ## Canonical declaration, intent and request -/

structure RequestEnvelope where
  federation : FederationId
  subjectKeyEpoch : Epoch
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  cost : Nat
  deriving DecidableEq, Repr

structure Declaration where
  intent : OperationIntent
  request : RequestEnvelope
  action : Action

/-- All codecs/digest functions are family-wide data.  There are no per-effect
callbacks and no equality-reflection/CR premise. -/
structure Config where
  actionCodec : LawfulCodec Action
  declarationCodec : LawfulCodec Declaration
  requestCodec : LawfulCodec (Request .object)
  intentAddressing : HyperdocumentOperationIntent.Addressing
  effectDerivation : DigestDerivation
  requestDerivation : DigestDerivation
  requestDomain : Digest
  semanticRelation : Digest

def Declaration.operationId (config : Config) (declaration : Declaration) :
    OperationId :=
  HyperdocumentOperationIntent.operationId
    config.intentAddressing declaration.intent

def Action.packedWrites (operation : OperationId) (author : PrincipalRef) :
    Action → List PackedWrite
  | .create payload => createWrites operation author payload
  | .editAtom payload => editAtomWrites operation payload
  | .link payload => linkWrites operation author payload
  | .transclude payload => transcludeWrites operation author payload
  | .mark payload => markWrites operation author payload
  | .annotate payload => annotateWrites operation author payload

def Declaration.packedWrites (config : Config)
    (declaration : Declaration) : List PackedWrite :=
  let operation := declaration.operationId config
  let author := declaration.intent.author
  declaration.action.packedWrites operation author

def Declaration.fieldWrites (config : Config)
    (declaration : Declaration) : List (CellState.FieldWrite cellSchema) :=
  (declaration.packedWrites config).map PackedWrite.toFieldWrite

def Declaration.patch (config : Config) (declaration : Declaration) :
    CellState.Patch cellSchema Digest where
  expectedPreRoot := declaration.intent.expectedContentRoot
  fieldFootprint :=
    (declaration.fieldWrites config).map CellState.FieldWrite.field |>.toFinset
  resourceFootprint := ∅
  fieldWrites := declaration.fieldWrites config
  resourceWrites := []

@[simp] theorem Declaration.patch_namedFields
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedFields =
      (declaration.patch config).fieldFootprint :=
  rfl

@[simp] theorem Declaration.patch_namedResources
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedResources =
      (declaration.patch config).resourceFootprint := by
  simp [Declaration.patch, CellState.Patch.namedResources]

def Declaration.effectDigest (config : Config)
    (declaration : Declaration) : Digest :=
  config.effectDerivation.digestBytes
    (config.declarationCodec.encode declaration)

def Declaration.toRequest (config : Config) (declaration : Declaration) :
    Request .object where
  domain := config.requestDomain
  semantics := config.semanticRelation
  federation := declaration.request.federation
  subject := declaration.intent.author.subject
  subjectKeyEpoch := declaration.request.subjectKeyEpoch
  target := ⟨declaration.intent.document.digest.value⟩
  verb := .mutateObject
  argsDigest := (declaration.operationId config).digest
  effectsDigest := declaration.effectDigest config
  nonce := declaration.intent.nonce
  height := declaration.request.height
  preStateRoot := declaration.intent.expectedContentRoot
  policyId := declaration.request.policyId
  policyEpoch := declaration.request.policyEpoch
  cost := declaration.request.cost

def Declaration.requestId (config : Config) (declaration : Declaration) : Digest :=
  config.requestDerivation.digestBytes
    (config.requestCodec.encode (declaration.toRequest config))

/-- Pure declaration coherence: action bytes and target document are not
caller-selected twins. -/
structure Declaration.Canonical (config : Config)
    (declaration : Declaration) where
  actionBytesExact : declaration.intent.actionBytes =
    config.actionCodec.encode declaration.action
  documentExact : declaration.action.document = declaration.intent.document
  objectCapability : declaration.intent.author.capabilityKind = .object

/-! ## Exact pre-state and stable-range validity -/

def PackedWrite.ExpectedAt
    (pre : CellState.LogicalState cellSchema) (write : PackedWrite) : Prop :=
  pre.fields write.address = write.write.expected

def Declaration.ExpectedAt (config : Config)
    (pre : CellState.LogicalState cellSchema)
    (declaration : Declaration) : Prop :=
  ∀ write, write ∈ declaration.packedWrites config → write.ExpectedAt pre

def storedPointPresentInDocument
    (pre : CellState.LogicalState cellSchema)
    (document : DocumentId) (point : StablePoint) : Prop :=
  ∃ run,
    lookup pre .runs point.run = some run ∧
    run.document = document ∧
    match point.neighbor with
    | none => run.atoms = []
    | some atomId =>
        atomId ∈ run.atoms ∧
        ∃ atom, lookup pre .atoms atomId = some atom ∧ atom.document = document

/-! This is storage membership validation around the one canonical
`StableRanges.HyperdocumentAdapter` realization.  It does not define endpoint
transport or a second range calculus. -/
structure StoredRangeValidAt
    (pre : CellState.LogicalState cellSchema)
    (document : DocumentId) (range : StableRange) : Prop where
  realizationStoredExact :
    (StableRanges.HyperdocumentAdapter.realizeRange range).stored = range
  start : storedPointPresentInDocument pre document range.start
  finish : storedPointPresentInDocument pre document range.finish

def Action.RangesValidAt
    (pre : CellState.LogicalState cellSchema)
    (action : Action) : Prop :=
  match action with
  | .link payload =>
      ∀ range, payload.source = some range →
        StoredRangeValidAt pre payload.sourceDocument range
  | .transclude payload =>
      ∀ range, payload.source = some range →
        StoredRangeValidAt pre payload.hostDocument range
  | .mark payload => StoredRangeValidAt pre payload.document payload.range
  | .annotate payload =>
      ∀ range, payload.range = some range →
        StoredRangeValidAt pre payload.document range
  | _ => True

/-- Complete semantic validation at the exact canonical pre-cell.  Generic
`CellState.validate` alone does not check expected old values or ranges. -/
structure ValidOperation
    {M : Hyperdocument.Materializer Digest}
    (config : Config) (pre : Hyperdocument.Cell M)
    (declaration : Declaration) where
  canonical : declaration.Canonical config
  preRootExact : declaration.intent.expectedContentRoot = pre.root
  writesUnique :
    ((declaration.packedWrites config).map PackedWrite.address).Nodup
  expectedExact : declaration.ExpectedAt config pre.logical
  rangesValid : declaration.action.RangesValidAt pre.logical

def authenticatedObjectHead
    {M : CredentialAuthorityState.Materializer}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell M}
    {height : Height} {principalRef : PrincipalRef}
    (principal : AuthenticatedPrincipal projection authorityPre height principalRef)
    (objectKind : principalRef.capabilityKind = .object) : Capability .object :=
  objectKind ▸ principal.stored.head

/-! ## The one AcceptedCellEffect family -/

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by simp

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) -> Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

def family
    {M : Hyperdocument.Materializer Digest}
    (config : Config) :
    SemanticEffectFamily cellSchema M Nat where
  Declaration := Declaration
  declarationCodec := config.declarationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => PLift (declaration.Canonical config)
  effectDigest := Declaration.effectDigest config
  patch := fun declaration _ => declaration.patch config
  nullifier := fun declaration _ => some declaration.intent.nonce
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- Same-canonical-authority accepted content effect.  The request is derived
from the declaration, and the named principal path is current and admissible
for that exact request. -/
structure Accepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (config : Config)
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentPre : Hyperdocument.Cell MDoc)
    (portal : Portal)
    (declaration : Declaration) : Type where
  principal : AuthenticatedPrincipal projection authorityPre
    declaration.request.height declaration.intent.author
  semantic : ValidOperation config documentPre declaration
  namedCapabilityAdmissible :
    (authenticatedObjectHead principal
      semantic.canonical.objectCapability).Admissible
    (CredentialAuthorityState.authState projection authorityPre)
    (declaration.toRequest config)
  accepted : AcceptedCellEffect
    (portal := portal)
    (authState := CredentialAuthorityState.authState projection authorityPre)
    (family config) (declaration.toRequest config) documentPre declaration ()

def accept
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (principal : AuthenticatedPrincipal projection authorityPre
      declaration.request.height declaration.intent.author)
    (semantic : ValidOperation config documentPre declaration)
    (namedCapabilityAdmissible :
      (authenticatedObjectHead principal
        semantic.canonical.objectCapability).Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (authorization : Authorized portal
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (validated : CellState.ValidatedPatch
      MDoc documentPre (declaration.patch config)) :
    Accepted config projection authorityPre documentPre portal declaration where
  principal := principal
  semantic := semantic
  namedCapabilityAdmissible := namedCapabilityAdmissible
  accepted :=
    { authorization := authorization
      effectsDigestBound := rfl
      preRootBound := semantic.preRootExact
      modeEvidence := ⟨semantic.canonical⟩
      validated := validated
      disclosure := .sealed
      disclosureAllowed := trivial }

/-! ## Exact causal event projection -/

/-- The final causal event determined by one accepted content effect.

This projection belongs beside the accepted semantic effect: its pre-root is
the exact input cell and its post-root is the sole verifier-minted post.  The
Kernel event-log layer stores this record, but does not get to reinterpret or
reconstruct it. -/
def Accepted.versionEventRecord
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    VersionEventRecord :=
  { historyDomain := declaration.intent.historyDomain
    document := declaration.intent.document
    schema := declaration.intent.schema
    semanticVersion := declaration.intent.semanticVersion
    operation := declaration.operationId config
    parents := declaration.intent.parents
    preStateRoot := documentPre.root
    postStateRoot := accepted.accepted.prepared.post.root
    requestId := declaration.requestId config
    effectId := declaration.effectDigest config
    author := declaration.intent.author }

/-- The request-neutral causal preimage is derived from that same record. -/
def Accepted.causalPreimage
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    CausalVersionDag.EventPreimage :=
  accepted.versionEventRecord.toCausalPreimage

@[simp] theorem Accepted.causalPreimage_pre_root
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    accepted.causalPreimage.preStateRoot = documentPre.root :=
  rfl

@[simp] theorem Accepted.causalPreimage_post_root
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    accepted.causalPreimage.postStateRoot =
      accepted.accepted.prepared.post.root :=
  rfl

/-! ## Exact post containment and receipt projection -/

theorem applyFieldWrites_member_of_nodup
    (writes : List (CellState.FieldWrite cellSchema))
    (fields : CellState.FieldStore cellSchema)
    (nodup : (writes.map CellState.FieldWrite.field).Nodup)
    (write : CellState.FieldWrite cellSchema) (member : write ∈ writes) :
    CellState.applyFieldWrites writes fields write.field = write.value := by
  induction writes generalizing fields with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      simp only [List.mem_cons] at member
      rw [CellState.applyFieldWrites]
      rcases member with rfl | member
      · rw [CellState.applyFieldWrites_frame]
        · simpa [CellState.FieldStore.read] using
            (CellState.FieldStore.read_assign_self fields write.field write.value)
        · simpa using nodup.1
      · exact induction (fields.assign head.field head.value)
          nodup.2 member

theorem Accepted.post_contains_fieldWrite
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration)
    (write : CellState.FieldWrite cellSchema)
    (member : write ∈ declaration.fieldWrites config) :
    accepted.accepted.prepared.post.logical.fields write.field = write.value := by
  have writesUnique :
      ((declaration.fieldWrites config).map
        CellState.FieldWrite.field).Nodup := by
    simpa [Declaration.fieldWrites, List.map_map, Function.comp_def,
      PackedWrite.toFieldWrite] using accepted.semantic.writesUnique
  exact applyFieldWrites_member_of_nodup
    (declaration.fieldWrites config) documentPre.logical.fields
    writesUnique write member

theorem Accepted.post_contains_link
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration)
    (payload : LinkPayload) (actionExact : declaration.action = .link payload) :
    lookup accepted.accepted.prepared.post.logical .links payload.id =
      some (linkRecord (declaration.operationId config)
        declaration.intent.author payload) := by
  have contains := accepted.post_contains_fieldWrite
    (PackedWrite.toFieldWrite
      ⟨.links,
        { key := payload.id
          expected := none
          replacement := linkRecord (declaration.operationId config)
            declaration.intent.author payload }⟩)
    (by
      unfold Declaration.fieldWrites Declaration.packedWrites
      apply List.mem_map_of_mem
      rw [actionExact]
      simp [Action.packedWrites, linkWrites])
  exact contains

theorem Accepted.post_contains_transclusion
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration)
    (payload : TranscludePayload)
    (actionExact : declaration.action = .transclude payload) :
    lookup accepted.accepted.prepared.post.logical .transclusions payload.id =
      some (transclusionRecord (declaration.operationId config)
        declaration.intent.author payload) := by
  have contains := accepted.post_contains_fieldWrite
    (PackedWrite.toFieldWrite
      ⟨.transclusions,
        { key := payload.id
          expected := none
          replacement := transclusionRecord (declaration.operationId config)
            declaration.intent.author payload }⟩)
    (by
      unfold Declaration.fieldWrites Declaration.packedWrites
      apply List.mem_map_of_mem
      rw [actionExact]
      simp [Action.packedWrites, transcludeWrites])
  exact contains

theorem Accepted.post_contains_transclusion_forward_link
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration)
    (payload : TranscludePayload)
    (actionExact : declaration.action = .transclude payload) :
    lookup accepted.accepted.prepared.post.logical .links payload.forwardLinkId =
      some (transclusionForwardLink (declaration.operationId config)
        declaration.intent.author payload) := by
  have contains := accepted.post_contains_fieldWrite
    (PackedWrite.toFieldWrite
      ⟨.links,
        { key := payload.forwardLinkId
          expected := none
          replacement := transclusionForwardLink (declaration.operationId config)
            declaration.intent.author payload }⟩)
    (by
      unfold Declaration.fieldWrites Declaration.packedWrites
      apply List.mem_map_of_mem
      rw [actionExact]
      simp [Action.packedWrites, transcludeWrites])
  exact contains

/-- Runtime/display receipt projection only.  History evidence must retain
`accepted.accepted` itself through `AcceptedCellEffectHistory`. -/
def Accepted.receiptEvent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    ReceiptEvent (family (M := MDoc) config) :=
  accepted.accepted.toReceiptEvent

@[simp] theorem Accepted.request_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration) :
    accepted.accepted.toReceiptEvent.request = declaration.toRequest config :=
  rfl

/-- info: 'Minidregg.Theory.HyperdocumentOperations.Declaration.patch_namedFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Declaration.patch_namedFields
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_fieldWrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_fieldWrite
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_link
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_transclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_transclusion
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_transclusion_forward_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_transclusion_forward_link
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.request_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.request_exact

end Minidregg.Theory.HyperdocumentOperations
