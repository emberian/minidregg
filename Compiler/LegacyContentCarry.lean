/- Exact content-v3/Store2 carry from audited source 3b1f628a. Old wire
meanings are frozen below, not decoded by the target's ElementBody/Mark codec.
Text/record attribution remains unchanged. New tree positions preserve the old
native client's numeric atom order; unsupported old reference/mark authority
is retained as explicitly legacy metadata, never invented target permission. -/
import Compiler.LegacyStoreCarry
import Compiler.NativeHostCodec
import Kernel.ContentResource

namespace Minidregg.Compiler.LegacyContentCarry

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.HyperdocumentCodec

set_option autoImplicit false

namespace Legacy

structure EmbedRef where
  document : DocumentId
  atom : AtomId
  revision : OperationId
  mode : TransclusionMode
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

def embedRefStream : StreamCodec EmbedRef :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (identifierStream .v1 .atom)
        (StreamCodec.product (identifierStream .v1 .operationIntent) transclusionModeStream)))
    (fun value => (value.document, value.atom, value.revision, value.mode))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; rfl)

def elementBodyTag : ElementBody -> Nat
  | .container _ => 0
  | .runs _ => 1
  | .embed _ => 2
  | .opaque _ _ => 3

def elementBodyStream : StreamCodec ElementBody where
  encode value :=
    StreamCodec.nat.encode (elementBodyTag value) ++
      match value with
      | .container children =>
          (StreamCodec.list (identifierStream .v1 .element)).encode children
      | .runs runs => (StreamCodec.list (identifierStream .v1 .run)).encode runs
      | .embed reference => embedRefStream.encode reference
      | .opaque schema payload =>
          digestStream.encode schema ++ bytesStream.encode payload
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => do
        let (children, suffix) ←
          (StreamCodec.list (identifierStream .v1 .element)).decodePrefix afterTag
        some (.container children, suffix)
    | 1 => do
        let (runs, suffix) ←
          (StreamCodec.list (identifierStream .v1 .run)).decodePrefix afterTag
        some (.runs runs, suffix)
    | 2 => do
        let (reference, suffix) ← embedRefStream.decodePrefix afterTag
        some (.embed reference, suffix)
    | _ => do
        let (schema, afterSchema) ← digestStream.decodePrefix afterTag
        let (payload, suffix) ← bytesStream.decodePrefix afterSchema
        some (.opaque schema payload, suffix)
  decodePrefix_encode := by
    intro value suffix
    cases value <;>
      simp [elementBodyTag, List.append_assoc,
        StreamCodec.nat.decodePrefix_encode,
        (StreamCodec.list (identifierStream .v1 .element)).decodePrefix_encode,
        (StreamCodec.list (identifierStream .v1 .run)).decodePrefix_encode,
        embedRefStream.decodePrefix_encode, digestStream.decodePrefix_encode,
        bytesStream.decodePrefix_encode]

def elementRecordStream : StreamCodec ElementRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.option (identifierStream .v1 .element))
        (StreamCodec.product elementBodyStream
          (StreamCodec.product principalRefStream
            (StreamCodec.product (identifierStream .v1 .operationIntent)
              (StreamCodec.option
                (identifierStream .v1 .operationIntent)))))))
    (fun record =>
      (record.document, record.parent, record.body, record.createdBy,
        record.createdAt, record.tombstonedAt))
    (fun wire =>
      ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
        wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro record; rfl)

def markRecordStream : StreamCodec MarkRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product storedStableRangeStream
        (StreamCodec.product digestStream
          (StreamCodec.product bytesStream
            (StreamCodec.product principalRefStream
              (StreamCodec.product (identifierStream .v1 .operationIntent)
                (StreamCodec.product digestStream
                  (StreamCodec.option (identifierStream .v1 .operationIntent)))))))))
    (fun record => (record.document, record.range, record.kind, record.payload,
      record.author, record.operation, record.visibilityPolicy, record.tombstonedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1,
      wire.2.2.2.2.2.1, wire.2.2.2.2.2.2.1, wire.2.2.2.2.2.2.2⟩)
    (by intro record; rfl)


/-- Frozen legacy atom kinds; new confidential kinds are never accepted under
this old wire identity. -/
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
  revision : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

def atomKindTag : AtomKind -> Nat
  | .text => 0
  | .inlineObject _ => 1

def atomKindPayload : AtomKind -> List UInt8
  | .text => []
  | .inlineObject schema => digestStream.encode schema

def atomKindStream : StreamCodec AtomKind where
  encode value := StreamCodec.nat.encode (atomKindTag value) ++ atomKindPayload value
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => some (.text, afterTag)
    | _ => do
        let (schema, suffix) ← digestStream.decodePrefix afterTag
        some (.inlineObject schema, suffix)
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | text => simp [atomKindTag, atomKindPayload, StreamCodec.nat.decodePrefix_encode]
    | inlineObject schema =>
        simp [atomKindTag, atomKindPayload, List.append_assoc,
          StreamCodec.nat.decodePrefix_encode, digestStream.decodePrefix_encode]

def atomRecordStream : StreamCodec AtomRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product atomKindStream
        (StreamCodec.product bytesStream
          (StreamCodec.product principalRefStream
            (StreamCodec.product (identifierStream .v1 .operationIntent)
              (StreamCodec.product (identifierStream .v1 .operationIntent)
                (StreamCodec.option (identifierStream .v1 .operationIntent))))))))
    (fun value => (value.document, value.kind, value.payload, value.createdBy,
      value.createdAt, value.revision, value.tombstonedAt))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2.1, tuple.2.2.2.2.2.2⟩)
    (by intro value; rfl)

def AtomRecord.toCurrent (record : AtomRecord) : Hyperdocument.AtomRecord :=
  { document := record.document
    kind := match record.kind with | .text => .text | .inlineObject schema => .inlineObject schema
    payload := record.payload
    createdBy := record.createdBy
    createdAt := record.createdAt
    revision := record.revision
    tombstonedAt := record.tombstonedAt }

inductive AnnotationBody where
  | inline (bytes : List UInt8)
  | reference (document : DocumentId)
  deriving DecidableEq, Repr

structure AnnotationRecord where
  document : DocumentId
  anchor : Hyperdocument.AnnotationAnchor
  body : AnnotationBody
  author : PrincipalRef
  operation : OperationId
  visibilityPolicy : Digest
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

def annotationBodyStream : StreamCodec AnnotationBody :=
  StreamCodec.xmap (StreamCodec.sum bytesStream (identifierStream .v1 .document))
    (fun | .inline bytes => .inl bytes | .reference document => .inr document)
    (fun | .inl bytes => .inline bytes | .inr document => .reference document)
    (by intro body; cases body <;> rfl)

def annotationRecordStream : StreamCodec AnnotationRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product HyperdocumentCell.annotationAnchorStream
        (StreamCodec.product annotationBodyStream
          (StreamCodec.product principalRefStream
            (StreamCodec.product (identifierStream .v1 .operationIntent)
              (StreamCodec.product digestStream
                (StreamCodec.option (identifierStream .v1 .operationIntent))))))))
    (fun record => (record.document, record.anchor, record.body, record.author,
      record.operation, record.visibilityPolicy, record.tombstonedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1,
      wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro record; rfl)

def AnnotationRecord.toCurrent (record : AnnotationRecord) : Hyperdocument.AnnotationRecord :=
  { document := record.document
    anchor := record.anchor
    body := match record.body with | .inline bytes => .inline bytes | .reference document => .reference document
    author := record.author
    operation := record.operation
    visibilityPolicy := record.visibilityPolicy
    tombstonedAt := record.tombstonedAt }


def Value : Hyperdocument.Namespace → Type
  | .elements => ElementRecord
  | .marks => MarkRecord
  | .documents => Hyperdocument.DocumentRecord
  | .atoms => AtomRecord
  | .runs => Hyperdocument.RunRecord
  | .fields => Hyperdocument.FieldRecord
  | .conflicts => Hyperdocument.ConflictRecord
  | .links => Hyperdocument.LinkRecord
  | .transclusions => Hyperdocument.TransclusionRecord
  | .annotations => AnnotationRecord
  | .blinding => Digest

instance valueDecidableEq (space : Hyperdocument.Namespace) : DecidableEq (Value space) := by
  cases space <;> simp only [Value] <;> infer_instance

abbrev layout : Store.Layout.{0, 0, 0} where
  Namespace := Hyperdocument.Namespace
  Key := Hyperdocument.Key
  Value := Value
  discipline := fun _ => .ram

def valueStream : (space : Hyperdocument.Namespace) → StreamCodec (Value space)
  | .elements => elementRecordStream
  | .marks => markRecordStream
  | .documents => HyperdocumentCell.documentRecordStream
  | .atoms => atomRecordStream
  | .runs => HyperdocumentCell.runRecordStream
  | .fields => HyperdocumentCell.fieldRecordStream
  | .conflicts => HyperdocumentCell.conflictRecordStream
  | .links => HyperdocumentCell.linkRecordStream
  | .transclusions => HyperdocumentCell.transclusionRecordStream
  | .annotations => annotationRecordStream
  | .blinding => digestStream

def recordVersion : Hyperdocument.Namespace → String
  | .atoms | .elements | .annotations => "v2"
  | _ => "v1"

/-- Exact old descriptor: Store2 framing comes from LegacyStoreCarry, while
this freezes the old content-v3 record meaning and its per-namespace ids. -/
def wire : StoreCodec.Wire layout where
  name := "minidregg/hyperdocument-content/v3"
  namespaces := [.documents, .atoms, .runs, .elements, .fields, .conflicts, .links,
    .transclusions, .marks, .annotations, .blinding]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := HyperdocumentCell.namespaceStream
  keyStream := HyperdocumentCell.contentKeyStream
  valueStream := valueStream
  keyCodecId space := s!"hyperdocument-key/{HyperdocumentCell.namespaceTag space}/v1"
  valueCodecId space := s!"hyperdocument-record/{HyperdocumentCell.namespaceTag space}/{recordVersion space}"
  blinding := some ⟨.blinding, ()⟩

end Legacy

abbrev LegacyStore := Store Legacy.layout
abbrev CurrentStore := Store Hyperdocument.layout

private def digest (tag : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash tag.toUTF8.toList bytes).digest

/-- A malformed RangeOpening prefix on purpose: nat0, run0, illegal optional
neighbor tag2. Current range interpretation must fail for every legacy body. -/
def referenceFrame : List UInt8 :=
  [255, 255, 2] ++ "DREGG/CARRY/LEGACY-ATOM-REFERENCE/v1".toUTF8.toList

def referenceCodec := NativeHostCodec.framed referenceFrame Legacy.embedRefStream

def referenceCarrier (reference : Legacy.EmbedRef) : StoredTransclusionRef :=
  let bytes := referenceCodec.encode reference
  let commitment := digest "DREGG.CARRY.LEGACY-REFERENCE/v1" bytes
  { referenceRoot := commitment
    -- These zeros mean no source-world/history proof was supplied. They are
    -- never exposed as such a proof; the dedicated domain/codec is metadata.
    source := ⟨digest "DREGG.CARRY.HISTORY-DOMAIN/v1" "legacy-reference-only".toUTF8.toList,
      ⟨0⟩, ⟨0⟩, commitment⟩
    opening := ⟨.value,
      digest "DREGG.CARRY.OPENING-CODEC/v1" "legacy-atom-reference".toUTF8.toList,
      digest "DREGG.CARRY.OPENING-RELATION/v1" "metadata-not-authority".toUTF8.toList,
      bytes, commitment⟩
    mode := reference.mode
    disclosureScope := ∅
    capabilityCeiling := ∅ }

/-- A reader may show these identifiers as a preserved link. Expansion needs
its own current source disclosure authority; snapshot expansion additionally
needs the retained historical interpreter. This function grants neither. -/
def inspectReference (value : StoredTransclusionRef) : Option Legacy.EmbedRef := do
  let reference ← referenceCodec.decode value.opening.canonicalDescriptor
  if referenceCarrier reference = value then some reference else none

theorem inspectReference_roundtrip (reference : Legacy.EmbedRef) :
    inspectReference (referenceCarrier reference) = some reference := by
  simp [inspectReference, referenceCarrier, referenceCodec.decode_encode]

/-- Concrete rejection pole, not merely distinct codec labels: the deployed
current range-opening parser itself refuses every legacy-reference carrier. -/
theorem legacy_reference_is_not_current_range (reference : Legacy.EmbedRef) :
    Minidregg.Kernel.ContentResource.openingOfReference (referenceCarrier reference) = none := by
  rfl

def markFrame : List UInt8 := "DREGG/CARRY/LEGACY-MARK/v1".toUTF8.toList
def markCodec := NativeHostCodec.framed markFrame
  (StreamCodec.product (identifierStream .v1 .mark) Legacy.markRecordStream)

def markCarrier (identifier : MarkId) (record : Legacy.MarkRecord) : AnnotationRecord :=
  ⟨record.document, .range record.range, .inline (markCodec.encode (identifier, record)),
    record.author, record.operation, record.visibilityPolicy, record.tombstonedAt⟩

/-- An old kind digest and payload are not guessed to be bold/code/link.
The exact old mark remains a range annotation with original policy/attribution. -/
def inspectMark (value : AnnotationRecord) : Option (MarkId × Legacy.MarkRecord) := do
  let .inline bytes := value.body | none
  let pair ← markCodec.decode bytes
  if markCarrier pair.1 pair.2 = value then some pair else none

theorem inspectMark_roundtrip (identifier : MarkId) (record : Legacy.MarkRecord) :
    inspectMark (markCarrier identifier record) = some (identifier, record) := by
  simp [inspectMark, markCarrier, markCodec.decode_encode]

def elementArchiveFrame : List UInt8 := "DREGG/CARRY/LEGACY-ELEMENT/v1".toUTF8.toList
def elementArchiveCodec := NativeHostCodec.framed elementArchiveFrame
  (StreamCodec.product (identifierStream .v1 .element) Legacy.elementRecordStream)
def elementArchiveName : Digest := digest "DREGG.CARRY.FIELD/v1" "legacy-element".toUTF8.toList

def elementArchive (identifier : ElementId) (record : Legacy.ElementRecord) : FieldRecord :=
  { valueType := .opaque elementArchiveName
    value := elementArchiveCodec.encode (identifier, record)
    merge := .exclusive
    writtenBy := record.createdBy
    writtenAt := record.createdAt }

def inspectElement : FieldRecord → Option (ElementId × Legacy.ElementRecord)
  | value@⟨.opaque schema, bytes, _, _, _⟩ => do
      if schema != elementArchiveName then none else do
        let pair ← elementArchiveCodec.decode bytes
        if elementArchive pair.1 pair.2 = value then some pair else none
  | _ => none

theorem inspectElement_roundtrip (identifier : ElementId) (record : Legacy.ElementRecord) :
    inspectElement (elementArchive identifier record) = some (identifier, record) := by
  simp [inspectElement, elementArchive, elementArchiveCodec.decode_encode]

/-- Both old root metadata and the materialized numeric text order are visible
in current authorized inspection. Original raw content also remains unchanged
inside the carried prefix; no historical byte stream is overwritten. -/
structure DocumentCarry where
  original : Option DocumentRecord
  root : ElementId
  atoms : List AtomId
  /-- Attribution copied from the source document, first numeric atom, or source element;
  it is not a newly authenticated author and confers no document ownership. -/
  sourceAttribution : PrincipalRef
  carryOperation : OperationId
  deriving DecidableEq

def documentCarryStream : StreamCodec DocumentCarry :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.option HyperdocumentCell.documentRecordStream)
      (StreamCodec.product (identifierStream .v1 .element)
        (StreamCodec.product (StreamCodec.list (identifierStream .v1 .atom))
          (StreamCodec.product principalRefStream (identifierStream .v1 .operationIntent)))))
    (fun record => (record.original, record.root, record.atoms,
      record.sourceAttribution, record.carryOperation))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def documentCarryName : Digest := digest "DREGG.CARRY.FIELD/v1" "legacy-document-tree".toUTF8.toList
def documentCarryCodec := NativeHostCodec.framed
  "DREGG/CARRY/LEGACY-DOCUMENT-TREE/v1".toUTF8.toList documentCarryStream

def documentCarrier (value : DocumentCarry) : FieldRecord :=
  { valueType := .opaque documentCarryName
    value := documentCarryCodec.encode value
    merge := .exclusive
    writtenBy := value.sourceAttribution
    writtenAt := value.carryOperation }

def inspectDocument : FieldRecord → Option DocumentCarry
  | value@⟨.opaque schema, bytes, _, _, _⟩ => do
      if schema != documentCarryName then none else do
        let record ← documentCarryCodec.decode bytes
        if documentCarrier record = value then some record else none
  | _ => none

theorem inspectDocument_roundtrip (record : DocumentCarry) :
    inspectDocument (documentCarrier record) = some record := by
  simp [inspectDocument, documentCarrier, documentCarryCodec.decode_encode]

/-- Read-only metadata projection. This is not a DocumentRecord and is never
an input to documentOwner. Consumers must first obtain current content read
permission before exposing it, just as for the underlying atoms and fields. -/
def carriedDocument (store : CurrentStore) (document : DocumentId) : Option DocumentCarry := do
  let field ← store ⟨.fields, ⟨.document document, documentCarryName⟩⟩
  let carried ← inspectDocument field
  let root ← store ⟨.elements, carried.root⟩
  if root.document = document ∧ root.parent = none then some carried else none

/-- Current structural order, with an explicit metadata-only root for old
atom-only or element-only stores. No synthetic document row or owner is introduced. -/
def documentOrder (store : CurrentStore) (document : DocumentId) : List ElementId :=
  match store ⟨.documents, document⟩ with
  | some _ => Minidregg.Kernel.ContentResource.documentOrder store document
  | none =>
      match carriedDocument store document with
      | some carried =>
          if carried.original.isNone then
            (Minidregg.Kernel.ContentResource.walk
              (Minidregg.Kernel.ContentResource.treeFuel store) store carried.root).tail
          else []
      | none => []

private def need {α : Type} (message : String) : Option α → Except String α
  | none => .error message
  | some value => .ok value

private def allocate (store : CurrentStore) (entry : Entry Hyperdocument.layout) :
    Except String CurrentStore := do
  if (store entry.1).isSome then throw "legacy content carry generated-address collision"
  return store.set entry.1 (some entry.2)

private def generatedId (tag : String) (height : Nat) (identifier : Digest) : Digest :=
  digest tag ((StreamCodec.product StreamCodec.nat digestStream).encode (height, identifier))

private def liftBody (identifier : ElementId) (record : Legacy.ElementRecord)
    (height : Nat) (store : CurrentStore) : Except String (ElementBody × CurrentStore) := do
  match record.body with
  | .container children => return (.container children, store)
  | .runs runs => return (.runs runs, store)
  | .opaque schema payload => return (.opaque schema payload, store)
  | .embed reference =>
      let transclusion : TransclusionId :=
        ⟨generatedId "DREGG.CARRY.LEGACY-TRANSCLUSION/v1" height identifier.digest⟩
      let stored : TransclusionRecord := ⟨record.document, referenceCarrier reference,
        record.createdBy, record.createdAt, ⟨0⟩, record.tombstonedAt⟩
      let next ← allocate store ⟨⟨.transclusions, transclusion⟩, stored⟩
      return (.embed transclusion, next)

private def preserveUnchanged (entry : Entry Legacy.layout) (store : CurrentStore) : CurrentStore :=
  match entry with
  | ⟨⟨.documents, key⟩, value⟩ => store.set ⟨.documents, key⟩ (some value)
  | ⟨⟨.atoms, key⟩, value⟩ => store.set ⟨.atoms, key⟩ (some value.toCurrent)
  | ⟨⟨.runs, key⟩, value⟩ => store.set ⟨.runs, key⟩ (some value)
  | ⟨⟨.fields, key⟩, value⟩ => store.set ⟨.fields, key⟩ (some value)
  | ⟨⟨.conflicts, key⟩, value⟩ => store.set ⟨.conflicts, key⟩ (some value)
  | ⟨⟨.links, key⟩, value⟩ => store.set ⟨.links, key⟩ (some value)
  | ⟨⟨.transclusions, key⟩, value⟩ => store.set ⟨.transclusions, key⟩ (some value)
  | ⟨⟨.annotations, key⟩, value⟩ => store.set ⟨.annotations, key⟩ (some value.toCurrent)
  | ⟨⟨.blinding, key⟩, value⟩ => store.set ⟨.blinding, key⟩ (some value)
  | ⟨⟨.elements, _⟩, _⟩ | ⟨⟨.marks, _⟩, _⟩ => store

private def documents (entries : List (Entry Legacy.layout)) : List (DocumentId × DocumentRecord) :=
  entries.filterMap fun entry => match entry with
    | ⟨⟨.documents, identifier⟩, record⟩ => some (identifier, record)
    | _ => none

private def atoms (entries : List (Entry Legacy.layout)) : List (AtomId × AtomRecord) :=
  (entries.filterMap fun entry => match entry with
    | ⟨⟨.atoms, identifier⟩, record⟩ => some (identifier, record.toCurrent)
    | _ => none).mergeSort (fun left right => decide (left.1.digest.value ≤ right.1.digest.value))

private def elements (entries : List (Entry Legacy.layout)) : List (ElementId × Legacy.ElementRecord) :=
  entries.filterMap fun entry => match entry with
    | ⟨⟨.elements, identifier⟩, record⟩ => some (identifier, record)
    | _ => none

private def migrate (height : Nat) (old : LegacyStore) (raw : List UInt8) : Except String CurrentStore := do
  let entries := StoreCodec.entries Legacy.wire old
  let originalDocuments := documents entries
  let originalAtoms := atoms entries
  let originalElements := elements entries
  let revision : OperationId := ⟨digest "DREGG.CARRY.CONTENT-REVISION/v1"
    (StreamCodec.nat.encode height ++ raw)⟩
  let mut current := entries.foldl (fun store entry => preserveUnchanged entry store) (0 : CurrentStore)
  for (identifier, record) in originalElements do
    let (body, withReferences) ← liftBody identifier record height current
    current := withReferences
    let converted : ElementRecord := ⟨record.document, record.parent, body,
      record.createdBy, record.createdAt, revision, record.tombstonedAt⟩
    current ← allocate current ⟨⟨.elements, identifier⟩, converted⟩
    current ← allocate current ⟨⟨.fields, ⟨.element identifier, elementArchiveName⟩⟩,
      elementArchive identifier record⟩
  for entry in entries do
    match entry with
    | ⟨⟨.marks, identifier⟩, record⟩ =>
        let key : AnnotationId :=
          ⟨generatedId "DREGG.CARRY.LEGACY-MARK-ANNOTATION/v1" height identifier.digest⟩
        current ← allocate current ⟨⟨.annotations, key⟩, markCarrier identifier record⟩
    | _ => pure ()
  for (identifier, record) in originalAtoms do
    -- Retained atom records themselves are never rewritten or renumbered.
    let retained : Option AtomRecord := current ⟨.atoms, identifier⟩
    if retained != some record then throw "legacy content atom changed"
  let documentIds := (originalDocuments.map Prod.fst ++
    originalAtoms.map (fun entry => entry.2.document) ++
    originalElements.map (fun entry => entry.2.document)).eraseDups
  for document in documentIds do
    let original := (originalDocuments.find? (fun entry => entry.1 == document)).map Prod.snd
    let sourceAttribution ← match original with
      | some record => pure record.createdBy
      | none =>
          match originalAtoms.find? (fun entry => entry.2.document == document) with
          | some first => pure first.2.createdBy
          | none => do
              let first ← need "legacy document has no original source attribution"
                (originalElements.find? (fun entry => entry.2.document == document))
              pure first.2.createdBy
    let root : ElementId :=
      ⟨generatedId "DREGG.CARRY.CONTENT-ROOT/v1" height document.digest⟩
    let selected := originalAtoms.filter fun entry => entry.2.document == document
    let mut children : List ElementId := []
    for (atom, record) in selected do
      let leaf : ElementId :=
        ⟨generatedId "DREGG.CARRY.CONTENT-ATOM-LEAF/v1" height atom.digest⟩
      current ← allocate current ⟨⟨.elements, leaf⟩,
        ⟨document, some root, .atom atom, record.createdBy, revision, revision, none⟩⟩
      children := children ++ [leaf]
    -- Old quotes were independent element records, not text atoms. They
    -- remain reference-only leaves after the unchanged numeric text order.
    for (element, oldRecord) in originalElements do
      if oldRecord.document == document then
        match oldRecord.body with
        | .embed _ =>
            let converted ← need "legacy content embed vanished" (current ⟨.elements, element⟩)
            current := current.set ⟨.elements, element⟩ (some { converted with parent := some root })
            children := children ++ [element]
        | _ => pure ()
    current ← allocate current ⟨⟨.elements, root⟩,
      ⟨document, none, .container children, sourceAttribution, revision, revision, none⟩⟩
    match original with
    | some record =>
        current := current.set ⟨.documents, document⟩ (some { record with rootElement := root })
    | none => pure ()
    current ← allocate current ⟨⟨.fields, ⟨.document document, documentCarryName⟩⟩,
      documentCarrier ⟨original, root, selected.map Prod.fst, sourceAttribution, revision⟩⟩
  -- The old birth blinding becomes the target ratchet's predecessor. Exactly
  -- one step is taken at carry height; old writes are not retroactively ratcheted.
  return Store.Patch.run current (HyperdocumentCell.contentBlinding.patch current height)

/-- Closed source-role converter. Input is the bare canonical Store2 content-v3
payload; the enclosing carry validates the actual source capsule and wraps the
result through the target registry/lifecycle codec and law. -/
def convertPayload (height : Nat) (bytes : List UInt8) : Except String CurrentStore := do
  let old ← need "legacy content carry requires exact Store2/content-v3 bytes"
    (LegacyStoreCarry.decodeV2 Legacy.wire bytes)
  let current ← migrate height old bytes
  if !decide (CanonicalCellRegistry.ContentLaw current) then
    throw "legacy content conversion violates target document locality"
  return current

end Minidregg.Compiler.LegacyContentCarry
