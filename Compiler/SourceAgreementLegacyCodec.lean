/- Read-only source projection of LegacyContentCarry's exact metadata codecs.
No migration, admission, ownership or new historical authority is introduced. -/
import Compiler.NativeHostCodec
import Kernel.ContentResource
namespace Minidregg.Compiler.SourceAgreementLegacyCodec
open Minidregg.Theory Minidregg.Theory.Store Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.HyperdocumentCodec
set_option autoImplicit false
namespace Legacy
structure EmbedRef where
  document : DocumentId
  atom : AtomId
  revision : OperationId
  mode : TransclusionMode
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



end Legacy
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
  simp only [inspectDocument, documentCarrier, bne_self_eq_false,
    Bool.false_eq_true, if_false, documentCarryCodec.decode_encode,
    bind, Option.bind, if_true]

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


end Minidregg.Compiler.SourceAgreementLegacyCodec
