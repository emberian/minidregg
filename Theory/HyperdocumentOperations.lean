/-
# Theory.HyperdocumentOperations -- first-order accepted content effects

The action grammar below is the sole source of Hyperdocument content patches.
Declarations are first-order data.  They derive one guarded `Store.Patch`
(every write guarded by its exact expected prior value, absence included),
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
open Minidregg.Theory.Store (Op Patch)

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

/-! ## Exact guarded writes -/

/-- The guarded operation installing `replacement` at `key` when the address
holds exactly `expected`: an overwrite guarded by the present value, or an
allocation guarded by absence.  This is the one guarded-write primitive,
`Store.Op`; there is no document-local write type. -/
def guardedSet (space : Namespace) (key : Key space)
    (expected : Option (Value space)) (replacement : Value space) : Op layout :=
  match expected with
  | some before => .write space key before replacement
  | none => .allocate space key replacement

@[simp] theorem guardedSet_address (space : Namespace) (key : Key space)
    (expected : Option (Value space)) (replacement : Value space) :
    (guardedSet space key expected replacement).address = ⟨space, key⟩ := by
  cases expected <;> rfl

@[simp] theorem guardedSet_writeAddress (space : Namespace) (key : Key space)
    (expected : Option (Value space)) (replacement : Value space) :
    (guardedSet space key expected replacement).writeAddress? = some ⟨space, key⟩ := by
  cases expected <;> rfl

@[simp] theorem guardedSet_apply (store : Store.Store layout) (space : Namespace)
    (key : Key space) (expected : Option (Value space)) (replacement : Value space) :
    (guardedSet space key expected replacement).apply store =
      store.set ⟨space, key⟩ (some replacement) := by
  cases expected <;> rfl

def createWrites (operation : OperationId) (author : PrincipalRef)
    (payload : CreatePayload) : Patch layout :=
  [ guardedSet .documents payload.documentId none
      { rootElement := payload.rootElementId
        schema := payload.schema
        createdBy := author
        createdAt := operation },
    guardedSet .elements payload.rootElementId none
      { document := payload.documentId
        parent := none
        body := payload.rootBody
        createdBy := author
        createdAt := operation
        tombstonedAt := none } ]

def editAtomRecord (operation : OperationId)
    (payload : EditAtomPayload) : AtomRecord :=
          { payload.before with
            kind := payload.kind
            payload := payload.payload
            tombstonedAt :=
              if payload.tombstone then some operation
              else payload.before.tombstonedAt }

def editAtomWrites (operation : OperationId)
    (payload : EditAtomPayload) : Patch layout :=
  [ guardedSet .atoms (payload.atomId) (some payload.before)
      (editAtomRecord operation payload) ]

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
    (payload : LinkPayload) : Patch layout :=
  [ guardedSet .links (payload.id) (none)
      (linkRecord operation author payload) ]

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
    (payload : TranscludePayload) : Patch layout :=
  [ guardedSet .transclusions (payload.id) (none)
      (transclusionRecord operation author payload),
    guardedSet .links (payload.forwardLinkId) (none)
      (transclusionForwardLink operation author payload) ]

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
    (payload : MarkPayload) : Patch layout :=
  [ guardedSet .marks (payload.id) (none)
      (markRecord operation author payload) ]

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
    (payload : AnnotatePayload) : Patch layout :=
  [ guardedSet .annotations (payload.id) (none)
      (annotationRecord operation author payload) ]

/-! ## Canonical declaration, intent and request -/

structure RequestEnvelope where
  federation : FederationId
  subjectKeyEpoch : Epoch
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  policyRevision : PolicyRevision
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

/-- The one guarded patch of an action. -/
def Action.ops (operation : OperationId) (author : PrincipalRef) :
    Action → Patch layout
  | .create payload => createWrites operation author payload
  | .editAtom payload => editAtomWrites operation payload
  | .link payload => linkWrites operation author payload
  | .transclude payload => transcludeWrites operation author payload
  | .mark payload => markWrites operation author payload
  | .annotate payload => annotateWrites operation author payload

/-- The declaration's guarded patch.  Its expected pre-root is
`intent.expectedContentRoot`, the index of the `ValidatedPatch` that accepts
it. -/
def Declaration.patch (config : Config) (declaration : Declaration) :
    Patch layout :=
  declaration.action.ops (declaration.operationId config) declaration.intent.author

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
  policyRevision := declaration.request.policyRevision
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

def storedPointPresentInDocument
    (pre : Store.Store layout)
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
    (pre : Store.Store layout)
    (document : DocumentId) (range : StableRange) : Prop where
  realizationStoredExact :
    (StableRanges.HyperdocumentAdapter.realizeRange range).stored = range
  start : storedPointPresentInDocument pre document range.start
  finish : storedPointPresentInDocument pre document range.finish

def Action.RangesValidAt
    (pre : Store.Store layout)
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

/-- Complete semantic validation at the exact canonical pre-cell: the root,
address uniqueness, the guards, and the stored ranges.  Generic
`CellState.validate` checks the root and guards but not ranges. -/
structure ValidOperation
    {M : Hyperdocument.Materializer Digest}
    (config : Config) (pre : Hyperdocument.Cell M)
    (declaration : Declaration) where
  canonical : declaration.Canonical config
  preRootExact : declaration.intent.expectedContentRoot = pre.root
  /-- Each address is written at most once, so every write's replacement is
  the value its address holds after the patch. -/
  writesUnique : ((declaration.patch config).map Op.address).Nodup
  /-- Every guard holds at the store its prefix produced: each expected prior
  value, absence included, is exact. -/
  guardsValid : Patch.ValidFrom pre.logical (declaration.patch config)
  rangesValid : declaration.action.RangesValidAt pre.logical

/-- Stored endpoints depend on the source-owned run and atom namespaces.
Changing unrelated content does not alter their meaning. -/
theorem StoredRangeValidAt.of_lookup_eq
    {before after : Store.Store layout}
    {document : DocumentId} {range : StableRange}
    (valid : StoredRangeValidAt before document range)
    (runs : ∀ key, lookup after .runs key = lookup before .runs key)
    (atoms : ∀ key, lookup after .atoms key = lookup before .atoms key) :
    StoredRangeValidAt after document range where
  realizationStoredExact := valid.realizationStoredExact
  start := by
    simpa only [storedPointPresentInDocument, runs, atoms] using valid.start
  finish := by
    simpa only [storedPointPresentInDocument, runs, atoms] using valid.finish

theorem Action.RangesValidAt.of_lookup_eq
    {before after : Store.Store layout} {action : Action}
    (valid : action.RangesValidAt before)
    (runs : ∀ key, lookup after .runs key = lookup before .runs key)
    (atoms : ∀ key, lookup after .atoms key = lookup before .atoms key) :
    action.RangesValidAt after := by
  cases action with
  | create _ => trivial
  | editAtom _ => trivial
  | link payload =>
      intro range exact
      exact StoredRangeValidAt.of_lookup_eq (valid range exact) runs atoms
  | transclude payload =>
      intro range exact
      exact StoredRangeValidAt.of_lookup_eq (valid range exact) runs atoms
  | mark payload => exact StoredRangeValidAt.of_lookup_eq valid runs atoms
  | annotate payload =>
      intro range exact
      exact StoredRangeValidAt.of_lookup_eq (valid range exact) runs atoms

/-- A range-bearing source action writes link/transclusion/mark/annotation
data and preserves its run/atom dependencies. The enduring range obligation
is therefore proved on the actual local post, ready for joint rechecking. -/
theorem ValidOperation.ranges_post
    {M : Hyperdocument.Materializer Digest}
    {config : Config} {pre : Hyperdocument.Cell M} {declaration : Declaration}
    (valid : ValidOperation config pre declaration)
    {expectedPreRoot : Digest}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot (declaration.patch config)) :
    declaration.action.RangesValidAt validated.apply.logical := by
  cases actionExact : declaration.action with
  | create payload => trivial
  | editAtom payload => trivial
  | link payload | transclude payload | mark payload | annotate payload =>
      rw [← actionExact]
      apply valid.rangesValid.of_lookup_eq
      all_goals
        intro key
        apply Patch.run_frame
        simp [Declaration.patch, actionExact, Action.ops, linkWrites, transcludeWrites,
          markWrites, annotateWrites, Patch.writeFootprint]

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
    (config : Config) (pre : Hyperdocument.Cell M) :
    SemanticEffectFamily layout M Nat where
  Declaration := Declaration
  declarationCodec := config.declarationCodec
  pre := pre
  request := fun declaration => ⟨.object, declaration.toRequest config⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => PLift (ValidOperation config pre declaration)
  Postcondition := fun declaration _ post =>
    (declaration.patch config).ResultAt pre.logical post ∧
      declaration.action.RangesValidAt post
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
    (family config documentPre) (declaration.toRequest config) documentPre declaration ()

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
      MDoc documentPre (declaration.toRequest config).preStateRoot
      (declaration.patch config)) :
    Accepted config projection authorityPre documentPre portal declaration where
  principal := principal
  semantic := semantic
  namedCapabilityAdmissible := namedCapabilityAdmissible
  accepted :=
    { authorization := authorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      modeEvidence := ⟨semantic⟩
      validated := validated
      postcondition := ⟨validated.resultAt, semantic.ranges_post validated⟩
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

/-- In a patch that writes each address at most once, every guarded write's
replacement is the value its address holds after the run. -/
theorem run_guardedSet_of_nodup (patch : Patch layout) (store : Store.Store layout)
    (nodup : (patch.map Op.address).Nodup)
    {space : Namespace} {key : Key space}
    {expected : Option (Value space)} {replacement : Value space}
    (member : guardedSet space key expected replacement ∈ patch) :
    Patch.run store patch ⟨space, key⟩ = some replacement := by
  induction patch generalizing store with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rw [Patch.run_cons]
      rcases List.mem_cons.mp member with same | member
      · subst same
        rw [Patch.run_frame]
        · simp
        · intro written
          apply nodup.1
          have accessed := Patch.writeFootprint_subset_accessFootprint tail written
          simpa [Patch.accessFootprint] using accessed
      · exact induction (head.apply store) nodup.2 member

/-- Every guarded write of an accepted declaration is installed in the canonical
post. -/
theorem Accepted.post_contains_guardedSet
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted config projection authorityPre documentPre portal declaration)
    {space : Namespace} {key : Key space}
    {expected : Option (Value space)} {replacement : Value space}
    (member : guardedSet space key expected replacement ∈ declaration.patch config) :
    lookup accepted.accepted.prepared.post.logical space key = some replacement :=
  run_guardedSet_of_nodup (declaration.patch config) documentPre.logical
    accepted.semantic.writesUnique member

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
        declaration.intent.author payload) :=
  accepted.post_contains_guardedSet (space := .links) (expected := none)
    (by rw [Declaration.patch, actionExact]; simp [Action.ops, linkWrites])

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
        declaration.intent.author payload) :=
  accepted.post_contains_guardedSet (space := .transclusions) (expected := none)
    (by rw [Declaration.patch, actionExact]; simp [Action.ops, transcludeWrites])

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
        declaration.intent.author payload) :=
  accepted.post_contains_guardedSet (space := .links) (expected := none)
    (by rw [Declaration.patch, actionExact]; simp [Action.ops, transcludeWrites])

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
    ReceiptEvent (family (M := MDoc) config documentPre) :=
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

/-- info: 'Minidregg.Theory.HyperdocumentOperations.ValidOperation.ranges_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValidOperation.ranges_post
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_guardedSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_guardedSet
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_link
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_transclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_transclusion
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.post_contains_transclusion_forward_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains_transclusion_forward_link
/-- info: 'Minidregg.Theory.HyperdocumentOperations.Accepted.request_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.request_exact

end Minidregg.Theory.HyperdocumentOperations
