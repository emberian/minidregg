/-
# Theory.Hyperdocument -- canonical hyperdocument identity and state nucleus

This module fixes only the P0 semantic representation shared by later document
effects, history, transclusion, views, and indexes.  It deliberately defines no
edit grammar, merge algorithm, fetch procedure, backlink oracle, or admission
shortcut.

Identifier *preimages* have a concrete versioned, domain-separated codec.  A
deployment may derive a typed digest from those bytes, but no injectivity or
collision-resistance property is attached to that digest function.  The
document store is one dependent sparse namespace and is definitionally mapped
to the canonical `CellState` shape.  A lawful cell codec commits every typed
value at the byte level; root binding remains a separate cryptographic claim.

**KNOWN VACUOUS (2026-08-10).**  `Materializer Root` below is
`CellState.Materializer cellSchema Root`, whose codec must inject the ENTIRE
`LogicalState cellSchema` into `List UInt8`.  `Address` is infinite and the
value type is `Option (Value _)`, which has at least two inhabitants, so that
state space is uncountable.
`Theory.MaterializerCardinality.hyperdocumentMaterializer_isEmpty` proves
`Materializer Digest` is EMPTY, so every theorem here and downstream that
quantifies over a document `Cell` is vacuously true.  The namespaces and their
semantics are not the problem; the total function in `LogicalState` is.
-/
import Theory.CausalVersionDag
import Theory.CredentialAuthorityState

namespace Minidregg.Theory.Hyperdocument

open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState

set_option autoImplicit false

universe u

/-! ## Versioned, domain-separated identifier preimages -/

/-- Codec versions are constructors, not host-supplied numbers.  A future
version therefore requires an explicit new constructor and migration rule. -/
inductive CodecVersion where
  | v1
  deriving DecidableEq, Repr

/-- Every semantic identifier class has a distinct preimage domain. -/
inductive IdDomain where
  | document
  | atom
  | run
  | element
  | field
  | conflict
  | link
  | transclusion
  | mark
  | annotation
  | versionEvent
  | operationIntent
  deriving DecidableEq, Repr

def CodecVersion.tag : CodecVersion -> UInt8
  | .v1 => 1

def IdDomain.tag : IdDomain -> UInt8
  | .document => 1
  | .atom => 2
  | .run => 3
  | .element => 4
  | .field => 5
  | .conflict => 6
  | .link => 7
  | .transclusion => 8
  | .mark => 9
  | .annotation => 10
  | .versionEvent => 11
  | .operationIntent => 12

theorem IdDomain.tag_injective : Function.Injective IdDomain.tag := by
  intro left right equal
  cases left <;> cases right <;> simp [IdDomain.tag] at equal ⊢

/-- The semantic payload from which a typed digest identifier may be derived.
The payload is already canonical application data; the codec below adds the
fixed Dregg/version/domain envelope. -/
structure IdPreimage (version : CodecVersion) (domain : IdDomain) where
  payload : List UInt8
  deriving DecidableEq, Repr

/-- `DR`, the codec version, and the semantic domain precede every payload. -/
def preimageHeader (version : CodecVersion) (domain : IdDomain) : List UInt8 :=
  [68, 82, version.tag, domain.tag]

def encodePreimage {version : CodecVersion} {domain : IdDomain}
    (preimage : IdPreimage version domain) : List UInt8 :=
  preimageHeader version domain ++ preimage.payload

def decodePreimage (version : CodecVersion) (domain : IdDomain)
    (bytes : List UInt8) : Option (IdPreimage version domain) :=
  match bytes with
  | 68 :: 82 :: versionTag :: domainTag :: payload =>
      if versionTag = version.tag ∧ domainTag = domain.tag then
        some ⟨payload⟩
      else
        none
  | _ => none

@[simp] theorem decodePreimage_encodePreimage
    {version : CodecVersion} {domain : IdDomain}
    (preimage : IdPreimage version domain) :
    decodePreimage version domain (encodePreimage preimage) = some preimage := by
  cases version
  simp [decodePreimage, encodePreimage, preimageHeader]

/-- The concrete canonical codec for one version/domain pair. -/
def preimageCodec (version : CodecVersion) (domain : IdDomain) :
    LawfulCodec (IdPreimage version domain) where
  encode := encodePreimage
  decode := decodePreimage version domain
  decode_encode := decodePreimage_encodePreimage

/-- Every lawful codec is injective at its encoded-byte boundary. -/
theorem lawfulCodec_encode_injective {alpha : Type u}
    (codec : LawfulCodec alpha) : Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

theorem preimageCodec_encode_injective
    (version : CodecVersion) (domain : IdDomain) :
    Function.Injective (preimageCodec version domain).encode :=
  lawfulCodec_encode_injective (preimageCodec version domain)

/-- Equal canonical preimage bytes force the same semantic namespace.  This is
a byte-level domain-separation theorem, not a digest collision theorem. -/
theorem preimage_encoding_domain_injective
    {version : CodecVersion} {leftDomain rightDomain : IdDomain}
    (left : IdPreimage version leftDomain)
    (right : IdPreimage version rightDomain)
    (equal : encodePreimage left = encodePreimage right) :
    leftDomain = rightDomain := by
  have tagsEqual := congrArg
    (fun bytes : List UInt8 => (bytes.drop 3).head?) equal
  have : leftDomain.tag = rightDomain.tag := by
    simpa [encodePreimage, preimageHeader] using tagsEqual
  exact IdDomain.tag_injective this

/-- Distinct identifier domains have disjoint canonical preimage encodings. -/
theorem preimage_encodings_disjoint
    {version : CodecVersion} {leftDomain rightDomain : IdDomain}
    (different : leftDomain = rightDomain -> False)
    (left : IdPreimage version leftDomain)
    (right : IdPreimage version rightDomain) :
    encodePreimage left = encodePreimage right -> False := by
  intro equal
  exact different (preimage_encoding_domain_injective left right equal)

/-- Typed digest identifier.  Domain and codec version are retained in its
type even though the digest carrier is shared. -/
structure Identifier (version : CodecVersion) (domain : IdDomain) where
  digest : Digest
  deriving DecidableEq, Repr

/-- A deployment's digest operation.  There is intentionally no binding,
injectivity, collision-resistance, or cryptographic-strength proof field. -/
structure DigestDerivation where
  digestBytes : List UInt8 -> Digest

def deriveIdentifier (derivation : DigestDerivation)
    {version : CodecVersion} {domain : IdDomain}
    (preimage : IdPreimage version domain) : Identifier version domain :=
  ⟨derivation.digestBytes (encodePreimage preimage)⟩

/-- Version migration is explicit data plus an exact preimage translation.
No migration from v1 is asserted merely because the type exists. -/
structure MigrationRule (sourceVersion targetVersion : CodecVersion) where
  migrate : (domain : IdDomain) ->
    IdPreimage sourceVersion domain -> IdPreimage targetVersion domain

abbrev DocumentId := Identifier .v1 .document
abbrev AtomId := Identifier .v1 .atom
abbrev RunId := Identifier .v1 .run
abbrev ElementId := Identifier .v1 .element
abbrev FieldId := Identifier .v1 .field
abbrev ConflictId := Identifier .v1 .conflict
abbrev LinkId := Identifier .v1 .link
abbrev TransclusionId := Identifier .v1 .transclusion
abbrev MarkId := Identifier .v1 .mark
abbrev AnnotationId := Identifier .v1 .annotation
abbrev VersionEventId := Identifier .v1 .versionEvent
/-- Pre-commit provenance identity.  Its canonical preimage is defined by the
operation layer and excludes post-state roots, request ids, and final version
event ids. -/
abbrev OperationId := Identifier .v1 .operationIntent

/-! ## Authenticated author principals -/

/-- First-order reference to the subject and capability slot naming an author.
Authentication is the indexed type below, not this record by itself. -/
structure PrincipalRef where
  subject : SubjectId
  capabilityKind : ResourceKind
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

/-- Small structural tag used only for the canonical principal identity below.
This is not a hash or an authorization judgment. -/
def resourceKindPrincipalTag : ResourceKind -> Nat
  | .object => 0
  | .account => 1
  | .program => 2

/-- The author identity retained by causal history is the exact typed subject. -/
def PrincipalRef.authorId (principal : PrincipalRef) : Digest :=
  ⟨principal.subject.value⟩

/-- Canonical injective packing of capability kind and capability id.

The pair `(authorId, principalId)` therefore retains every field of
`PrincipalRef`; it is not an arbitrary caller-supplied provenance label. -/
def PrincipalRef.principalId (principal : PrincipalRef) : Digest :=
  ⟨3 * principal.capabilityId.value +
    resourceKindPrincipalTag principal.capabilityKind⟩

/-- The two causal identities determine the complete typed principal reference. -/
theorem PrincipalRef.eq_of_history_ids
    {left right : PrincipalRef}
    (author : left.authorId = right.authorId)
    (principal : left.principalId = right.principalId) :
    left = right := by
  cases left with
  | mk leftSubject leftKind leftCapability =>
    cases right with
    | mk rightSubject rightKind rightCapability =>
      simp only [PrincipalRef.authorId, PrincipalRef.principalId] at author principal
      cases leftSubject
      cases rightSubject
      cases leftCapability
      cases rightCapability
      cases leftKind <;> cases rightKind <;>
        simp_all [resourceKindPrincipalTag] <;> omega

/-- A principal authenticated against one exact canonical authority cell at one
height.  The stored lineage is opened from the typed capability slot and all
current epoch, validity-window, holder, and revocation facts are proof fields.
This is a credential path, not a signature verifier or operation admission. -/
structure AuthenticatedPrincipal
    {M : CredentialAuthorityState.Materializer}
    (projection : ProjectionUniverse) (authorityCell : Cell M)
    (height : Height) (principal : PrincipalRef) : Type where
  stored : StoredCapability principal.capabilityKind
  opened : readCapability authorityCell principal.capabilityKind
      principal.capabilityId = some stored
  idBound : stored.head.id = principal.capabilityId
  holderBound : stored.head.holder = .subject principal.subject
  lineage : LineageValid stored
  validFrom : stored.head.notBefore ≤ height
  validUntil : height ≤ stored.head.notAfter
  issuerCurrent : stored.head.issuerEpoch =
    (authState projection authorityCell).issuerEpoch stored.head.issuer
  policyCurrent : stored.head.policyEpoch =
    (authState projection authorityCell).policyEpoch stored.head.policyId
  selfNotRevoked : RevocationKey.capability stored.head.id ∉
    (authState projection authorityCell).revoked
  ancestorsNotRevoked : ∀ ancestor, ancestor ∈ stored.head.ancestors →
    RevocationKey.capability ancestor ∉
      (authState projection authorityCell).revoked
  channelsNotRevoked : ∀ channel, channel ∈ stored.head.channels →
    RevocationKey.channel channel ∉
      (authState projection authorityCell).revoked

/-! ## Typed hyperdocument values -/

inductive AtomKind where
  | text
  | inlineObject (schema : Digest)
  deriving DecidableEq, Repr

structure AtomRecord where
  document : DocumentId
  kind : AtomKind
  payload : List UInt8
  createdBy : PrincipalRef
  createdAt : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

structure RunRecord where
  document : DocumentId
  atoms : List AtomId
  createdBy : PrincipalRef
  createdAt : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

/-- An embed is a typed document reference.  Fetch and disclosure semantics are
deliberately absent from this P0 representation. -/
structure EmbedRef where
  document : DocumentId
  element : Option ElementId
  snapshot : Option VersionEventId
  deriving DecidableEq, Repr

inductive ElementBody where
  | container (children : List ElementId)
  | runs (runs : List RunId)
  | embed (reference : EmbedRef)
  | opaque (schema : Digest) (payload : List UInt8)
  deriving DecidableEq, Repr

structure ElementRecord where
  document : DocumentId
  parent : Option ElementId
  body : ElementBody
  createdBy : PrincipalRef
  createdAt : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

inductive AnchorBias where
  | before
  | after
  deriving DecidableEq, Repr

/-- Canonical behavior when the atom neighboring a stored endpoint dies.
Preference policies may select only an exact predecessor/successor committed by
the accepted delete event; they do not authorize a renderer to search for a
replacement. -/
inductive EndpointDeathPolicy where
  | invalidate
  | keepTombstone
  | preferPrevious
  | preferNext
  | preferPreviousThenNext
  | preferNextThenPrevious
  deriving DecidableEq, Repr

/-- Canonical stored/wire endpoint data names a neighboring atom identity
rather than a byte offset and commits its behavior if that atom dies.
`Theory.StableRanges` owns the operational transport semantics and realizes
this record definitionally; this record is not a second range calculus. -/
structure StablePoint where
  run : RunId
  neighbor : Option AtomId
  bias : AnchorBias
  death : EndpointDeathPolicy
  deriving DecidableEq, Repr

/-- Canonical stored/wire range data.  Its interpretation goes through the
exact `Theory.StableRanges` adapter. -/
structure StableRange where
  start : StablePoint
  finish : StablePoint
  deriving DecidableEq, Repr

inductive MergeRegime where
  | exclusive
  | join
  | multiValue
  | additiveCounter
  | orderedSequence
  deriving DecidableEq, Repr

inductive FieldType where
  | text
  | natural
  | flag
  | digest
  | reference (domain : IdDomain)
  | opaque (schema : Digest)
  deriving DecidableEq, Repr

def FieldType.Value : FieldType -> Type
  | .text => List UInt8
  | .natural => Nat
  | .flag => Bool
  | .digest => Digest
  | .reference domain => Identifier .v1 domain
  | .opaque _ => List UInt8

inductive FieldOwner where
  | document (id : DocumentId)
  | element (id : ElementId)
  deriving DecidableEq, Repr

structure FieldKey where
  owner : FieldOwner
  name : Digest
  deriving DecidableEq, Repr

/-- Field values retain their type and merge declaration in canonical state. -/
structure FieldRecord where
  valueType : FieldType
  value : valueType.Value
  merge : MergeRegime
  writtenBy : PrincipalRef
  writtenAt : OperationId

structure ConflictAlternative where
  valueType : FieldType
  value : valueType.Value
  author : PrincipalRef
  operation : OperationId

/-- Concurrent values remain representable with their provenance.  Resolution
is a later authority-sensitive operation, not a projection performed here. -/
structure ConflictRecord where
  field : FieldKey
  base : Option VersionEventId
  alternatives : List ConflictAlternative
  regime : MergeRegime
  recordedAt : OperationId

inductive TransclusionMode where
  | snapshot
  | live
  deriving DecidableEq, Repr

/-- First-order identity of the exact source version named by a transclusion.
The object, receipt/history entry, and semantic state/value roots are distinct;
none can be reconstructed from a URI or from another root by convention. -/
structure StoredSourceIdentity where
  historyDomain : Digest
  objectRoot : Digest
  historyEntryRoot : Digest
  semanticRoot : Digest
  deriving DecidableEq, Repr

inductive StoredOpeningShape where
  | value
  | range
  deriving DecidableEq, Repr

/-- First-order descriptor of an opening whose coordinate and cell carriers
are selected only by the named codec/relation.  The hyperdocument schema does
not pretend that an arbitrary proof field `F` fits a fixed value namespace.

`canonicalDescriptor` is the full codec output for the later generic opening;
`openingCommitment` binds those bytes under the named deployment commitment.
The exact lawful codec and commitment function are supplied by an assurance
`OpeningRepresentation`, not by a Rust parser. -/
structure OpeningDescriptor where
  shape : StoredOpeningShape
  openingCodecId : Digest
  openingRelationId : Digest
  canonicalDescriptor : List UInt8
  openingCommitment : Digest
  deriving DecidableEq, Repr

/-- Canonical disclosure vocabulary shared by scope and capability ceiling. -/
structure DisclosureAtom where
  namespaceId : Digest
  payload : List UInt8
  deriving DecidableEq, Repr

/-- The complete durable reference identity needed by a transclusion opening,
chain weld, or authenticated reverse index.  Provenance of the act which stores
it lives in `TransclusionRecord`; all target identity lives here so a forward
link can commit the same object without copying a lossy subset. -/
structure StoredTransclusionRef where
  referenceRoot : Digest
  source : StoredSourceIdentity
  opening : OpeningDescriptor
  mode : TransclusionMode
  disclosureScope : Finset DisclosureAtom
  capabilityCeiling : Finset DisclosureAtom
  deriving DecidableEq

inductive LinkTarget where
  | document (id : DocumentId)
  | element (id : ElementId)
  | range (document : DocumentId) (range : StableRange)
  | transclusion (id : TransclusionId) (reference : StoredTransclusionRef)
  | external (scheme authority path : List UInt8)
  deriving DecidableEq

/-- A forward link stores the complete transclusion reference when that is its
target.  Backlinks are derived from accepted `LinkRecord` history events; this
record is not itself a mutable reverse-index row. -/
structure LinkRecord where
  sourceDocument : DocumentId
  source : Option StableRange
  target : LinkTarget
  relation : Digest
  author : PrincipalRef
  operation : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq

/-- Canonical stored transclusion plus provenance of the storage event.  Fetch,
finality, PCS/CR/ROM evidence, chain welds, and accepted-effect admission remain
proof fields in the assurance layer, but every datum they bind is present here. -/
structure TransclusionRecord where
  hostDocument : DocumentId
  reference : StoredTransclusionRef
  author : PrincipalRef
  operation : OperationId
  disclosurePolicy : Digest
  tombstonedAt : Option OperationId
  deriving DecidableEq

structure MarkRecord where
  document : DocumentId
  range : StableRange
  kind : Digest
  payload : List UInt8
  author : PrincipalRef
  operation : OperationId
  visibilityPolicy : Digest
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

structure AnnotationRecord where
  document : DocumentId
  range : Option StableRange
  body : DocumentId
  author : PrincipalRef
  operation : OperationId
  visibilityPolicy : Digest
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

/-- Final causal event data lives in the separate append-only event-log cell,
not in the mutable document cell below.  Its `operation` was derived before
the content transition; only this final record binds projected pre/post roots
and request/effect ids.  Consequently content never contains the final event
id whose preimage names its post root. -/
structure VersionEventRecord where
  historyDomain : Digest
  document : DocumentId
  schema : CausalVersionDag.SchemaRef
  semanticVersion : Nat
  operation : OperationId
  parents : List VersionEventId
  preStateRoot : Digest
  postStateRoot : Digest
  requestId : Digest
  effectId : Digest
  author : PrincipalRef
  deriving DecidableEq, Repr

namespace VersionEventRecord

/-- Total exact projection into the one generic causal semantic preimage.

Every semantic field is projected from stored data.  The document digest is the
history stream, parent event ids become the canonical parent frontier, and the
two provenance digests are derived injectively from the typed principal. -/
def toCausalPreimage (event : VersionEventRecord) :
    CausalVersionDag.EventPreimage where
  historyDomain := event.historyDomain
  streamId := event.document.digest
  schema := event.schema
  semanticVersion := event.semanticVersion
  semanticObjectRoot := event.operation.digest
  preStateRoot := event.preStateRoot
  postStateRoot := event.postStateRoot
  parentFrontier := event.parents.map Identifier.digest
  authorId := event.author.authorId
  principalId := event.author.principalId
  requestId := event.requestId
  effectId := event.effectId

/-- Reconstruct stored typed data from a causal preimage and the typed author.
The converse theorem below requires that the preimage contains the identities
canonically derived from that author. -/
def ofCausalPreimage (author : PrincipalRef)
    (event : CausalVersionDag.EventPreimage) : VersionEventRecord where
  historyDomain := event.historyDomain
  document := ⟨event.streamId⟩
  schema := event.schema
  semanticVersion := event.semanticVersion
  operation := ⟨event.semanticObjectRoot⟩
  parents := event.parentFrontier.map Identifier.mk
  preStateRoot := event.preStateRoot
  postStateRoot := event.postStateRoot
  requestId := event.requestId
  effectId := event.effectId
  author := author

/-- Stored event -> causal preimage -> stored event is exact. -/
@[simp] theorem ofCausalPreimage_toCausalPreimage
    (event : VersionEventRecord) :
    ofCausalPreimage event.author event.toCausalPreimage = event := by
  cases event
  simp [ofCausalPreimage, toCausalPreimage, List.map_map, Function.comp_def]

/-- A causal preimage in the typed-author image round-trips exactly. -/
theorem toCausalPreimage_ofCausalPreimage
    (author : PrincipalRef) (event : CausalVersionDag.EventPreimage)
    (authorExact : event.authorId = author.authorId)
    (principalExact : event.principalId = author.principalId) :
    (ofCausalPreimage author event).toCausalPreimage = event := by
  cases event
  simp_all [ofCausalPreimage, toCausalPreimage, List.map_map,
    Function.comp_def]

/-- No two stored hyperdocument events project to the same causal preimage. -/
theorem toCausalPreimage_injective :
    Function.Injective toCausalPreimage := by
  intro left right equal
  have authorIdEqual := congrArg CausalVersionDag.EventPreimage.authorId equal
  have principalIdEqual :=
    congrArg CausalVersionDag.EventPreimage.principalId equal
  have authorsEqual : left.author = right.author :=
    PrincipalRef.eq_of_history_ids authorIdEqual principalIdEqual
  calc
    left = ofCausalPreimage left.author left.toCausalPreimage :=
      (ofCausalPreimage_toCausalPreimage left).symm
    _ = ofCausalPreimage left.author right.toCausalPreimage :=
      congrArg (ofCausalPreimage left.author) equal
    _ = ofCausalPreimage right.author right.toCausalPreimage :=
      congrArg (fun author => ofCausalPreimage author right.toCausalPreimage)
        authorsEqual
    _ = right := ofCausalPreimage_toCausalPreimage right

/-- Causal parent-frontier well-formedness is the sole stored parent-order law;
Hyperdocument does not define a second DAG validity predicate. -/
abbrev CausallyWellFormed (event : VersionEventRecord) : Prop :=
  event.toCausalPreimage.WellFormed

end VersionEventRecord

/-! ## Exact weld to the generic causal history -/

/-- Canonical domain-separated preimage for one typed version-event id. -/
def versionEventIdPreimage
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage)
    (event : VersionEventRecord) : IdPreimage .v1 .versionEvent :=
  ⟨eventCodec.encode event.toCausalPreimage⟩

/-- The typed version-event preimage remains injective before digesting. -/
theorem versionEventIdPreimage_injective
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage) :
    Function.Injective (versionEventIdPreimage eventCodec) := by
  intro left right equal
  apply VersionEventRecord.toCausalPreimage_injective
  apply lawfulCodec_encode_injective eventCodec
  exact congrArg IdPreimage.payload equal

/-- Turn the lawful causal-event codec and Hyperdocument digest derivation into
the generic causal addressing scheme.  The fixed `DR/v1/versionEvent` envelope
is included before the abstract digest operation. -/
def causalVersionAddressing
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage)
    (derivation : DigestDerivation) : CausalVersionDag.ContentAddressing where
  codec := eventCodec
  digestBytes := fun bytes =>
    derivation.digestBytes
      (encodePreimage (IdPreimage.mk (version := .v1)
        (domain := .versionEvent) bytes))

/-- Derive the typed stored key from the exact same domain-separated causal
bytes used by `causalVersionAddressing`. -/
def deriveVersionEventId
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage)
    (derivation : DigestDerivation) (event : VersionEventRecord) :
    VersionEventId :=
  deriveIdentifier derivation (versionEventIdPreimage eventCodec event)

@[simp] theorem deriveVersionEventId_address_exact
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage)
    (derivation : DigestDerivation) (event : VersionEventRecord) :
    (deriveVersionEventId eventCodec derivation event).digest =
      (causalVersionAddressing eventCodec derivation).address
        event.toCausalPreimage :=
  rfl

/-- Proof token for one canonical sparse-store version event.

Its typed key is the address of its exact causal preimage, and its parent list
already satisfies the generic canonical-frontier law.  This is causal identity,
not consensus or finality. -/
structure StoredVersionEvent
    (scheme : CausalVersionDag.ContentAddressing) where
  key : VersionEventId
  record : VersionEventRecord
  wellFormed : record.CausallyWellFormed
  keyExact : key.digest = scheme.address record.toCausalPreimage

namespace StoredVersionEvent

/-- The ordinary construction path derives the typed key; callers supply no
identity or semantic override fields. -/
def derive
    (eventCodec : LawfulCodec CausalVersionDag.EventPreimage)
    (derivation : DigestDerivation) (record : VersionEventRecord)
    (wellFormed : record.CausallyWellFormed) :
    StoredVersionEvent (causalVersionAddressing eventCodec derivation) where
  key := deriveVersionEventId eventCodec derivation record
  record := record
  wellFormed := wellFormed
  keyExact := deriveVersionEventId_address_exact eventCodec derivation record

/-- Exact adapter into the generic addressed causal event. -/
def toAddressedEvent
    {scheme : CausalVersionDag.ContentAddressing}
    (stored : StoredVersionEvent scheme) :
    CausalVersionDag.AddressedEvent scheme where
  preimage := stored.record.toCausalPreimage
  entryId := stored.key.digest
  entryIdExact := stored.keyExact
  wellFormed := stored.wellFormed

@[simp] theorem toAddressedEvent_preimage
    {scheme : CausalVersionDag.ContentAddressing}
    (stored : StoredVersionEvent scheme) :
    stored.toAddressedEvent.preimage = stored.record.toCausalPreimage :=
  rfl

@[simp] theorem toAddressedEvent_entryId
    {scheme : CausalVersionDag.ContentAddressing}
    (stored : StoredVersionEvent scheme) :
    stored.toAddressedEvent.entryId = stored.key.digest :=
  rfl

/-- Attach the concrete event-family evidence without introducing a parallel
history judgment.  Parent compatibility and append validity remain the generic
`CausalVersionDag.SemanticFamily` / `ValidAppend` types. -/
def toVerifiedEvent
    {State : Type u} {scheme : CausalVersionDag.ContentAddressing}
    {family : CausalVersionDag.SemanticFamily State}
    (stored : StoredVersionEvent scheme)
    (semantics : family.Evidence stored.record.toCausalPreimage) :
    CausalVersionDag.VerifiedEvent scheme family where
  addressed := stored.toAddressedEvent
  semantics := semantics

/-- Equal typed keys bind equal stored semantic events only under the explicit
ideal binding premise of the selected address scheme. -/
theorem record_eq_of_key_eq
    {scheme : CausalVersionDag.ContentAddressing}
    (binding : scheme.BindingPremise)
    {left right : StoredVersionEvent scheme}
    (sameKey : left.key = right.key) :
    left.record = right.record := by
  apply VersionEventRecord.toCausalPreimage_injective
  exact CausalVersionDag.AddressedEvent.preimage_eq_of_entryId_eq binding
    (left := left.toAddressedEvent) (right := right.toAddressedEvent)
    (congrArg Identifier.digest sameKey)

end StoredVersionEvent

structure DocumentRecord where
  rootElement : ElementId
  schema : Digest
  createdBy : PrincipalRef
  createdAt : OperationId
  deriving DecidableEq, Repr

/-! ## One dependent document namespace and exact CellState mapping -/

inductive Namespace where
  | documents
  | atoms
  | runs
  | elements
  | fields
  | conflicts
  | links
  | transclusions
  | marks
  | annotations
  deriving DecidableEq, Repr

/-- P0 storage discipline declarations.  The separate event-log adapter uses
`appendOnly`; every namespace in this mutable document cell is currently RAM.
Enforcement belongs to accepted sparse operations, not this value schema. -/
inductive StorageDiscipline where
  | mutable
  | appendOnly
  deriving DecidableEq, Repr

def Namespace.discipline : Namespace -> StorageDiscipline
  | _ => .mutable

def Key : Namespace -> Type
  | .documents => DocumentId
  | .atoms => AtomId
  | .runs => RunId
  | .elements => ElementId
  | .fields => FieldKey
  | .conflicts => ConflictId
  | .links => LinkId
  | .transclusions => TransclusionId
  | .marks => MarkId
  | .annotations => AnnotationId

def Value : (space : Namespace) -> Type
  | .documents => DocumentRecord
  | .atoms => AtomRecord
  | .runs => RunRecord
  | .elements => ElementRecord
  | .fields => FieldRecord
  | .conflicts => ConflictRecord
  | .links => LinkRecord
  | .transclusions => TransclusionRecord
  | .marks => MarkRecord
  | .annotations => AnnotationRecord

instance keyDecidableEq (space : Namespace) : DecidableEq (Key space) := by
  cases space <;> simp only [Key] <;> infer_instance

abbrev Address := Sigma Key

instance : DecidableEq Address := inferInstance

/-- Namespace tags are structurally disjoint even when their underlying digest
carriers contain the same number. -/
theorem address_namespace_eq_of_eq
    {leftSpace rightSpace : Namespace}
    (leftKey : Key leftSpace) (rightKey : Key rightSpace)
    (equal : (Sigma.mk leftSpace leftKey : Address) =
      Sigma.mk rightSpace rightKey) :
    leftSpace = rightSpace :=
  congrArg Sigma.fst equal

theorem addresses_disjoint
    {leftSpace rightSpace : Namespace}
    (different : leftSpace = rightSpace -> False)
    (leftKey : Key leftSpace) (rightKey : Key rightSpace) :
    (Sigma.mk leftSpace leftKey : Address) = Sigma.mk rightSpace rightKey -> False := by
  intro equal
  exact different (address_namespace_eq_of_eq leftKey rightKey equal)

/-- The semantic sparse store: absence is represented only by `none`. -/
abbrev SparseStore :=
  (space : Namespace) -> Key space -> Option (Value space)

/-- The exact canonical cell schema.  There is no untyped extension map or
parallel resource table; each packed address has its dependent optional value. -/
def cellSchema : CellState.Schema where
  Field := Address
  FieldType := fun address => Option (Value address.1)
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq cellSchema.Field := by
  change DecidableEq Address
  infer_instance

instance : DecidableEq cellSchema.Resource := by
  change DecidableEq Empty
  infer_instance

/-- Sparse namespace storage becomes canonical cell state without translation
or a host-authored root. -/
def SparseStore.toCellState (store : SparseStore) :
    CellState.LogicalState cellSchema where
  fields := fun address => store address.1 address.2
  resources := fun resource => nomatch resource

/-- The inverse projection reads the exact dependent field. -/
def SparseStore.ofCellState (state : CellState.LogicalState cellSchema) :
    SparseStore :=
  fun space key => state.fields ⟨space, key⟩

@[simp] theorem SparseStore.ofCellState_toCellState (store : SparseStore) :
    SparseStore.ofCellState store.toCellState = store := by
  funext space key
  rfl

@[simp] theorem SparseStore.toCellState_ofCellState
    (state : CellState.LogicalState cellSchema) :
    (SparseStore.ofCellState state).toCellState = state := by
  cases state with
  | mk fields resources =>
      have resourcesUnique : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      subst resources
      rfl

abbrev Materializer (Root : Type) := CellState.Materializer cellSchema Root
abbrev Cell {Root : Type} (materializer : Materializer Root) :=
  CellState.Materialized materializer

def lookup (state : CellState.LogicalState cellSchema)
    (space : Namespace) (key : Key space) : Option (Value space) :=
  state.fields ⟨space, key⟩

/-- Every stored semantic value opens from the exact canonical bytes. -/
@[simp] theorem CellState.Materialized.decode_bytes
    {Root : Type} {materializer : Materializer Root}
    (cell : Cell materializer) :
    materializer.codec.decode cell.bytes = some cell.logical :=
  materializer.codec.decode_encode cell.logical

/-- Commitment tooth: if any typed address has a semantically different value,
the canonical encodings differ.  This follows from codec round-trip alone and
makes all fields above byte-committed.  It deliberately concludes nothing
about roots, because root binding is cryptographic evidence outside P0. -/
theorem semantically_effective_field_change_changes_canonical_bytes
    {Root : Type} (materializer : Materializer Root)
    (left right : CellState.LogicalState cellSchema)
    (address : Address)
    (changed : left.fields address = right.fields address -> False) :
    materializer.codec.encode left = materializer.codec.encode right -> False := by
  intro encodedEqual
  have stateEqual : left = right :=
    lawfulCodec_encode_injective materializer.codec encodedEqual
  exact changed (congrArg (fun state => state.fields address) stateEqual)

/-- info: 'Minidregg.Theory.Hyperdocument.decodePreimage_encodePreimage' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms decodePreimage_encodePreimage
/-- info: 'Minidregg.Theory.Hyperdocument.preimageCodec_encode_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms preimageCodec_encode_injective
/-- info: 'Minidregg.Theory.Hyperdocument.preimage_encodings_disjoint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms preimage_encodings_disjoint
/-- info: 'Minidregg.Theory.Hyperdocument.SparseStore.ofCellState_toCellState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseStore.ofCellState_toCellState
/-- info: 'Minidregg.Theory.Hyperdocument.SparseStore.toCellState_ofCellState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseStore.toCellState_ofCellState
/-- info: 'Minidregg.Theory.Hyperdocument.semantically_effective_field_change_changes_canonical_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantically_effective_field_change_changes_canonical_bytes

end Minidregg.Theory.Hyperdocument
