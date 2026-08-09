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
-/
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

/-! ## Authenticated author principals -/

/-- First-order reference to the subject and capability slot naming an author.
Authentication is the indexed type below, not this record by itself. -/
structure PrincipalRef where
  subject : SubjectId
  capabilityKind : ResourceKind
  capabilityId : CapabilityId
  deriving DecidableEq, Repr

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
  createdAt : VersionEventId
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

structure RunRecord where
  document : DocumentId
  atoms : List AtomId
  createdBy : PrincipalRef
  createdAt : VersionEventId
  tombstonedAt : Option VersionEventId
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
  createdAt : VersionEventId
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

inductive AnchorBias where
  | before
  | after
  deriving DecidableEq, Repr

/-- Canonical stored/wire endpoint data names a neighboring atom identity
rather than a byte offset.  `Theory.StableRanges` owns the richer operational
endpoint/death semantics; an exact adapter to that model is required before
range operations land.  This record is not a second range calculus. -/
structure StablePoint where
  run : RunId
  neighbor : Option AtomId
  bias : AnchorBias
  deriving DecidableEq, Repr

/-- Canonical stored/wire range data.  Its interpretation must go through the
future exact `Theory.StableRanges` adapter mentioned above. -/
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
  writtenAt : VersionEventId

structure ConflictAlternative where
  valueType : FieldType
  value : valueType.Value
  author : PrincipalRef
  event : VersionEventId

/-- Concurrent values remain representable with their provenance.  Resolution
is a later authority-sensitive operation, not a projection performed here. -/
structure ConflictRecord where
  field : FieldKey
  base : Option VersionEventId
  alternatives : List ConflictAlternative
  regime : MergeRegime
  recordedAt : VersionEventId

inductive LinkTarget where
  | document (id : DocumentId)
  | element (id : ElementId)
  | range (document : DocumentId) (range : StableRange)
  | external (scheme authority path : List UInt8)
  deriving DecidableEq, Repr

structure LinkRecord where
  sourceDocument : DocumentId
  source : Option StableRange
  target : LinkTarget
  relation : Digest
  author : PrincipalRef
  event : VersionEventId
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

inductive TransclusionMode where
  | snapshot (event : VersionEventId)
  | live
  deriving DecidableEq, Repr

/-- Durable transclusion identity and provenance only.  Chain weld, fetch,
release, and non-amplification judgments intentionally do not appear here. -/
structure TransclusionRecord where
  hostDocument : DocumentId
  targetDocument : DocumentId
  targetRange : Option StableRange
  mode : TransclusionMode
  author : PrincipalRef
  event : VersionEventId
  disclosurePolicy : Digest
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

structure MarkRecord where
  document : DocumentId
  range : StableRange
  kind : Digest
  payload : List UInt8
  author : PrincipalRef
  event : VersionEventId
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

structure AnnotationRecord where
  document : DocumentId
  range : Option StableRange
  body : DocumentId
  author : PrincipalRef
  event : VersionEventId
  tombstonedAt : Option VersionEventId
  deriving DecidableEq, Repr

structure VersionEventRecord where
  document : DocumentId
  parents : List VersionEventId
  baseRoot : Digest
  effectDigest : Digest
  author : PrincipalRef
  deriving DecidableEq, Repr

structure DocumentRecord where
  rootElement : ElementId
  schema : Digest
  createdBy : PrincipalRef
  createdAt : VersionEventId
  deriving DecidableEq, Repr

/-! ## One dependent sparse namespace and exact CellState mapping -/

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
  | versionEvents
  deriving DecidableEq, Repr

/-- P0 storage discipline declarations.  Enforcement belongs to accepted
sparse operations, not this value schema. -/
inductive StorageDiscipline where
  | mutable
  | appendOnly
  deriving DecidableEq, Repr

def Namespace.discipline : Namespace -> StorageDiscipline
  | .versionEvents => .appendOnly
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
  | .versionEvents => VersionEventId

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
  | .versionEvents => VersionEventRecord

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

#print axioms decodePreimage_encodePreimage
#print axioms preimageCodec_encode_injective
#print axioms preimage_encodings_disjoint
#print axioms SparseStore.ofCellState_toCellState
#print axioms SparseStore.toCellState_ofCellState
#print axioms semantically_effective_field_change_changes_canonical_bytes

end Minidregg.Theory.Hyperdocument
