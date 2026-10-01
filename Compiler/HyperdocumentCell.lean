/-
# Compiler.HyperdocumentCell -- the hyperdocument cells on the one store codec

Three cells carry a hyperdocument, each a `Store` over its own layout and each
materialized by the generic `StoreCodec` at the declared wire below:

* **content** -- `Hyperdocument.layout`: ten typed namespaces (documents, atoms,
  runs, elements, fields, conflicts, links, transclusions, marks, annotations).
  A document has as many entries in each namespace as it has; there is no page,
  slot, overflow list or page epoch.
* **event log** -- `HyperdocumentEventLog.Sparse.layout`: one append-only
  namespace of version events.
* **link index** -- `indexLayout capacity`: the bounded semantic index of
  `Kernel.HyperdocumentIndexSync` (both causal checkpoints, the sync cursor,
  and one source entry and one derived row per slot).  Its capacity is the
  semantic model's, committed by the layout's key codec ids; it is not a wire
  page capacity, and the cell carries exactly the snapshot
  (`snapshotOfStore_storeOfSnapshot`).

This replaces `Compiler.HyperdocumentContentPageMaterializer` (a sixteen-entry
page with a four-slot core and a twelve-entry overflow list),
`Compiler.HyperdocumentEventPageMaterializer` (a four-slot event page) and
`Compiler.HyperdocumentIndexPageMaterializer` (a four-slot index page).  Cells
written with any of their `LOOM/…` frames refuse to decode here
(`retired_page_frames_refused`).  The content page's cross-page `ForwardTarget`
routing is gone with the pages: a link's target is the canonical `LinkTarget`.
-/
import Compiler.HyperdocumentCodec
import Compiler.StoreCodec
import Kernel.HyperdocumentEventLog
import Kernel.HyperdocumentIndexSync

namespace Minidregg.Compiler.HyperdocumentCell

open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory.Store (Entry)
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Content records -/

def documentRecordStream : StreamCodec DocumentRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .element)
      (StreamCodec.product digestStream
        (StreamCodec.product principalRefStream
          (identifierStream .v1 .operationIntent))))
    (fun record =>
      (record.rootElement, record.schema, record.createdBy, record.createdAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro record; rfl)

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

def runRecordStream : StreamCodec RunRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.list (identifierStream .v1 .atom))
        (StreamCodec.product principalRefStream
          (StreamCodec.product (identifierStream .v1 .operationIntent)
            (StreamCodec.option (identifierStream .v1 .operationIntent))))))
    (fun record => (record.document, record.atoms, record.createdBy,
      record.createdAt, record.tombstonedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro record; rfl)

def linkRecordStream : StreamCodec LinkRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.option storedStableRangeStream)
        (StreamCodec.product linkTargetStream
          (StreamCodec.product digestStream
            (StreamCodec.product principalRefStream
              (StreamCodec.product (identifierStream .v1 .operationIntent)
                (StreamCodec.option (identifierStream .v1 .operationIntent))))))))
    (fun record => (record.sourceDocument, record.source, record.target,
      record.relation, record.author, record.operation, record.tombstonedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1,
      wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro record; rfl)

def fieldOwnerStream : StreamCodec FieldOwner :=
  StreamCodec.xmap
    (StreamCodec.sum (identifierStream .v1 .document) (identifierStream .v1 .element))
    (fun owner => match owner with
      | .document document => .inl document
      | .element element => .inr element)
    (fun wire => match wire with
      | .inl document => .document document
      | .inr element => .element element)
    (by intro owner; cases owner <;> rfl)

def fieldKeyStream : StreamCodec FieldKey :=
  StreamCodec.xmap (StreamCodec.product fieldOwnerStream digestStream)
    (fun key => (key.owner, key.name))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro key; rfl)

def idDomainOfTag : UInt8 → Option IdDomain
  | 1 => some .document
  | 2 => some .atom
  | 3 => some .run
  | 4 => some .element
  | 5 => some .field
  | 6 => some .conflict
  | 7 => some .link
  | 8 => some .transclusion
  | 9 => some .mark
  | 10 => some .annotation
  | 11 => some .versionEvent
  | 12 => some .operationIntent
  | _ => none

theorem idDomainOfTag_tag (domain : IdDomain) : idDomainOfTag domain.tag = some domain := by
  cases domain <;> rfl

def idDomainStream : StreamCodec IdDomain where
  encode domain := [domain.tag]
  decodePrefix
    | tag :: suffix => (idDomainOfTag tag).map fun domain => (domain, suffix)
    | [] => none
  decodePrefix_encode := by
    intro domain suffix
    simp [idDomainOfTag_tag]

def fieldTypeStream : StreamCodec FieldType where
  encode
    | .text => [0]
    | .natural => [1]
    | .flag => [2]
    | .digest => [3]
    | .reference domain => 4 :: idDomainStream.encode domain
    | .opaque schema => 5 :: digestStream.encode schema
  decodePrefix
    | 0 :: suffix => some (.text, suffix)
    | 1 :: suffix => some (.natural, suffix)
    | 2 :: suffix => some (.flag, suffix)
    | 3 :: suffix => some (.digest, suffix)
    | 4 :: bytes => do
        let (domain, suffix) ← idDomainStream.decodePrefix bytes
        some (.reference domain, suffix)
    | 5 :: bytes => do
        let (schema, suffix) ← digestStream.decodePrefix bytes
        some (.opaque schema, suffix)
    | _ => none
  decodePrefix_encode := by
    intro fieldType suffix
    cases fieldType <;>
      first
        | rfl
        | simp [idDomainStream.decodePrefix_encode, digestStream.decodePrefix_encode]

def fieldValueStream : (fieldType : FieldType) → StreamCodec fieldType.Value
  | .text => bytesStream
  | .natural => StreamCodec.nat
  | .flag => StreamCodec.bool
  | .digest => digestStream
  | .reference domain => identifierStream .v1 domain
  | .opaque _ => bytesStream

/-- A typed field value: its type, then its value under that type's codec. -/
def typedValueStream : StreamCodec (Σ fieldType : FieldType, fieldType.Value) :=
  FiniteDependentMapCodec.entryStream fieldTypeStream fieldValueStream

def mergeRegimeStream : StreamCodec MergeRegime where
  encode
    | .exclusive => [0]
    | .join => [1]
    | .multiValue => [2]
    | .additiveCounter => [3]
    | .orderedSequence => [4]
  decodePrefix
    | 0 :: suffix => some (.exclusive, suffix)
    | 1 :: suffix => some (.join, suffix)
    | 2 :: suffix => some (.multiValue, suffix)
    | 3 :: suffix => some (.additiveCounter, suffix)
    | 4 :: suffix => some (.orderedSequence, suffix)
    | _ => none
  decodePrefix_encode := by intro regime suffix; cases regime <;> rfl

def fieldRecordStream : StreamCodec FieldRecord :=
  StreamCodec.xmap
    (StreamCodec.product typedValueStream
      (StreamCodec.product mergeRegimeStream
        (StreamCodec.product principalRefStream (identifierStream .v1 .operationIntent))))
    (fun record => (⟨record.valueType, record.value⟩, record.merge, record.writtenBy,
      record.writtenAt))
    (fun wire => ⟨wire.1.1, wire.1.2, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro record; rfl)

def conflictAlternativeStream : StreamCodec ConflictAlternative :=
  StreamCodec.xmap
    (StreamCodec.product typedValueStream
      (StreamCodec.product principalRefStream (identifierStream .v1 .operationIntent)))
    (fun alternative => (⟨alternative.valueType, alternative.value⟩, alternative.author,
      alternative.operation))
    (fun wire => ⟨wire.1.1, wire.1.2, wire.2.1, wire.2.2⟩)
    (by intro alternative; rfl)

def conflictRecordStream : StreamCodec ConflictRecord :=
  StreamCodec.xmap
    (StreamCodec.product fieldKeyStream
      (StreamCodec.product (StreamCodec.option (identifierStream .v1 .versionEvent))
        (StreamCodec.product (StreamCodec.list conflictAlternativeStream)
          (StreamCodec.product mergeRegimeStream (identifierStream .v1 .operationIntent)))))
    (fun record => (record.field, record.base, record.alternatives, record.regime,
      record.recordedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro record; rfl)

def transclusionRecordStream : StreamCodec TransclusionRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product storedTransclusionRefStream
        (StreamCodec.product principalRefStream
          (StreamCodec.product (identifierStream .v1 .operationIntent)
            (StreamCodec.product digestStream
              (StreamCodec.option (identifierStream .v1 .operationIntent)))))))
    (fun record => (record.hostDocument, record.reference, record.author, record.operation,
      record.disclosurePolicy, record.tombstonedAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1,
      wire.2.2.2.2.2⟩)
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

def annotationAnchorStream : StreamCodec AnnotationAnchor :=
  StreamCodec.xmap
    (StreamCodec.option (StreamCodec.sum storedStableRangeStream
      (StreamCodec.product (identifierStream .v1 .atom) (identifierStream .v1 .operationIntent))))
    (fun | .document => none | .range range => some (.inl range)
         | .atom atom revision => some (.inr (atom, revision)))
    (fun | none => .document | some (.inl range) => .range range
         | some (.inr (atom, revision)) => .atom atom revision)
    (by intro anchor; cases anchor <;> rfl)

def annotationBodyStream : StreamCodec AnnotationBody :=
  StreamCodec.xmap (StreamCodec.sum bytesStream (identifierStream .v1 .document))
    (fun | .inline bytes => .inl bytes | .reference document => .inr document)
    (fun | .inl bytes => .inline bytes | .inr document => .reference document)
    (by intro body; cases body <;> rfl)

def annotationRecordStream : StreamCodec AnnotationRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product annotationAnchorStream
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

/-! ## The content wire -/

def namespaceTag : Hyperdocument.Namespace → UInt8
  | .documents => 0
  | .atoms => 1
  | .runs => 2
  | .elements => 3
  | .fields => 4
  | .conflicts => 5
  | .links => 6
  | .transclusions => 7
  | .marks => 8
  | .annotations => 9

def namespaceOfTag : UInt8 → Option Hyperdocument.Namespace
  | 0 => some .documents
  | 1 => some .atoms
  | 2 => some .runs
  | 3 => some .elements
  | 4 => some .fields
  | 5 => some .conflicts
  | 6 => some .links
  | 7 => some .transclusions
  | 8 => some .marks
  | 9 => some .annotations
  | _ => none

def namespaceStream : StreamCodec Hyperdocument.Namespace where
  encode space := [namespaceTag space]
  decodePrefix
    | tag :: suffix => (namespaceOfTag tag).map fun space => (space, suffix)
    | [] => none
  decodePrefix_encode := by
    intro space suffix
    cases space <;> rfl

def contentKeyStream : (space : Hyperdocument.Namespace) → StreamCodec (Hyperdocument.Key space)
  | .documents => identifierStream .v1 .document
  | .atoms => identifierStream .v1 .atom
  | .runs => identifierStream .v1 .run
  | .elements => identifierStream .v1 .element
  | .fields => fieldKeyStream
  | .conflicts => identifierStream .v1 .conflict
  | .links => identifierStream .v1 .link
  | .transclusions => identifierStream .v1 .transclusion
  | .marks => identifierStream .v1 .mark
  | .annotations => identifierStream .v1 .annotation

def contentValueStream :
    (space : Hyperdocument.Namespace) → StreamCodec (Hyperdocument.Value space)
  | .documents => documentRecordStream
  | .atoms => atomRecordStream
  | .runs => runRecordStream
  | .elements => elementRecordStream
  | .fields => fieldRecordStream
  | .conflicts => conflictRecordStream
  | .links => linkRecordStream
  | .transclusions => transclusionRecordStream
  | .marks => markRecordStream
  | .annotations => annotationRecordStream

def contentNamespaces : List Hyperdocument.Namespace :=
  [.documents, .atoms, .runs, .elements, .fields, .conflicts, .links,
    .transclusions, .marks, .annotations]

/-- Record codec version per namespace.  v2: atoms carry `revision`, an
element's embed names an atom at a revision with a mode, and an annotation
carries an anchor and an inline-or-reference body.  The layout digest in every
cell frame covers these ids, so a v1 content cell refuses to load. -/
def contentRecordVersion : Hyperdocument.Namespace → String
  | .atoms | .elements | .annotations => "v2"
  | _ => "v1"

def contentWire : Wire Hyperdocument.layout where
  name := "minidregg/hyperdocument-content/v2"
  namespaces := contentNamespaces
  namespaces_complete := by intro space; cases space <;> simp [contentNamespaces]
  namespaceStream := namespaceStream
  keyStream := contentKeyStream
  valueStream := contentValueStream
  keyCodecId space := s!"hyperdocument-key/{namespaceTag space}/v1"
  valueCodecId space := s!"hyperdocument-record/{namespaceTag space}/{contentRecordVersion space}"

/-- The content cell materializer. -/
def contentMaterializer : Hyperdocument.Materializer Digest :=
  StoreCodec.materializer contentWire

/-! ### A document has as many links as it has -/

/-- One link record, reused at every link id of the witness. -/
def sampleLink : LinkRecord where
  sourceDocument := ⟨⟨100⟩⟩
  source := none
  target := .document ⟨⟨200⟩⟩
  relation := ⟨1⟩
  author := ⟨⟨7⟩, .object, ⟨11⟩⟩
  operation := ⟨⟨300⟩⟩
  tombstonedAt := none

def linkEntry (index : Nat) : Entry Hyperdocument.layout :=
  ⟨⟨.links, (⟨⟨index⟩⟩ : LinkId)⟩, sampleLink⟩

/-- A document cell holding exactly the links `0 … size-1`. -/
def linksStore (size : Nat) : Store.Store Hyperdocument.layout :=
  fromEntries ((List.range size).map linkEntry)

private theorem linkEntry_addresses (size : Nat) :
    ((List.range size).map linkEntry).map Sigma.fst =
      (List.range size).map fun index =>
        (⟨.links, (⟨⟨index⟩⟩ : LinkId)⟩ : Store.Address Hyperdocument.layout) := by
  rw [List.map_map]
  rfl

theorem linksStore_support_card (size : Nat) : (linksStore size).support.card = size := by
  have support : (linksStore size).support =
      ((List.range size).map fun index =>
        (⟨.links, (⟨⟨index⟩⟩ : LinkId)⟩ : Store.Address Hyperdocument.layout)).toFinset := by
    ext address
    rw [DFinsupp.mem_support_toFun, List.mem_toFinset, ← linkEntry_addresses]
    exact (fromEntries_apply_eq_none_iff _ address).not.trans not_not
  rw [support, List.toFinset_card_of_nodup]
  · rw [List.length_map]
    exact List.length_range
  · apply List.Nodup.map _ List.nodup_range
    intro left right same
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at same
    cases same
    rfl

/-- **No page capacity.**  A document cell with any number of links has exactly
that many present addresses and round-trips through the content codec.  (The
deleted content page refused the seventeenth entry.) -/
theorem links_unbounded (size : Nat) :
    (linksStore size).support.card = size ∧
      contentMaterializer.codec.decode (contentMaterializer.codec.encode (linksStore size)) =
        some (linksStore size) :=
  ⟨linksStore_support_card size, decode_encode contentWire _⟩

theorem links_17 :
    (linksStore 17).support.card = 17 ∧
      contentMaterializer.codec.decode (contentMaterializer.codec.encode (linksStore 17)) =
        some (linksStore 17) :=
  links_unbounded 17

/-! ## The event-log wire -/

open Minidregg.Kernel.HyperdocumentEventLog

/-- First-order wire tuple for the generic causal event preimage. -/
abbrev EventPreimageTuple :=
  Digest × Digest × SchemaRef × Nat × Digest × Digest × Digest × List Digest ×
    Digest × Digest × Digest × Digest

def eventPreimageTupleStream : StreamCodec EventPreimageTuple :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product schemaRefStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product (StreamCodec.list digestStream)
            (StreamCodec.product digestStream (StreamCodec.product digestStream
              (StreamCodec.product digestStream digestStream))))))))))

def eventPreimageStream : StreamCodec EventPreimage :=
  StreamCodec.xmap eventPreimageTupleStream
    (fun event => ⟨event.historyDomain, event.streamId, event.schema,
      event.semanticVersion, event.semanticObjectRoot, event.preStateRoot,
      event.postStateRoot, event.parentFrontier, event.authorId, event.principalId,
      event.requestId, event.effectId⟩)
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2.1,
      tuple.2.2.2.2.2.1, tuple.2.2.2.2.2.2.1, tuple.2.2.2.2.2.2.2.1,
      tuple.2.2.2.2.2.2.2.2.1, tuple.2.2.2.2.2.2.2.2.2.1, tuple.2.2.2.2.2.2.2.2.2.2.1,
      tuple.2.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro event; rfl)

/-- A stored event is its complete causal preimage plus the typed author needed
to reconstruct `VersionEventRecord`. -/
def versionEventRecordStream : StreamCodec VersionEventRecord :=
  StreamCodec.xmap
    (StreamCodec.product eventPreimageStream principalRefStream)
    (fun event => (event.toCausalPreimage, event.author))
    (fun wire => VersionEventRecord.ofCausalPreimage wire.2 wire.1)
    VersionEventRecord.ofCausalPreimage_toCausalPreimage

def eventNamespaceStream : StreamCodec Sparse.layout.Namespace where
  encode _ := []
  decodePrefix bytes := some (.events, bytes)
  decodePrefix_encode := by intro space suffix; cases space; rfl

def eventWire : Wire Sparse.layout where
  name := "minidregg/hyperdocument-events/v1"
  namespaces := [.events]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := eventNamespaceStream
  keyStream := fun _ => identifierStream .v1 .versionEvent
  valueStream := fun _ => versionEventRecordStream
  keyCodecId := fun _ => "version-event-id/digest"
  valueCodecId := fun _ => "version-event-record/v1"

/-- The event-log cell materializer. -/
def eventMaterializer : Sparse.Materializer Digest := StoreCodec.materializer eventWire

/-- The deployed event-id derivation: cSHAKE256 under the version-event
customization over the typed, domain-separated event preimage.  A recorded
event's key is `eventScheme.address` of its causal preimage; the registry's
event-history law checks it on every loaded and final log. -/
def eventCustomization : List UInt8 := "LOOM.HDOC.VERSION.EVENT/v1".toUTF8.toList

def eventDerivation : DigestDerivation where
  digestBytes bytes := (Sp800185Cshake256.hash eventCustomization bytes).digest

def eventScheme : ContentAddressing :=
  causalVersionAddressing eventPreimageStream.toLawful eventDerivation

/-! ## The link-index wire -/

open Minidregg.Kernel.HyperdocumentIndexSync

inductive IndexSpace where
  | checkpoints
  | cursor
  | source
  | derived
  deriving DecidableEq, Repr

def IndexSpace.Key (capacity : Nat) : IndexSpace → Type
  | .checkpoints => Bool
  | .cursor => Unit
  | .source => Fin capacity
  | .derived => Fin capacity

def IndexSpace.Value : IndexSpace → Type
  | .checkpoints => CausalCheckpoint
  | .cursor => SyncCursor
  | .source => SourceEntry
  | .derived => IndexedRow

instance IndexSpace.keyDecEq (capacity : Nat) :
    (space : IndexSpace) → DecidableEq (IndexSpace.Key capacity space)
  | .checkpoints => inferInstanceAs (DecidableEq Bool)
  | .cursor => inferInstanceAs (DecidableEq Unit)
  | .source => inferInstanceAs (DecidableEq (Fin capacity))
  | .derived => inferInstanceAs (DecidableEq (Fin capacity))

instance IndexSpace.valueDecEq : (space : IndexSpace) → DecidableEq (IndexSpace.Value space)
  | .checkpoints => inferInstanceAs (DecidableEq CausalCheckpoint)
  | .cursor => inferInstanceAs (DecidableEq SyncCursor)
  | .source => inferInstanceAs (DecidableEq SourceEntry)
  | .derived => inferInstanceAs (DecidableEq IndexedRow)

/-- The index layout.  `false`/`true` under `checkpoints` are the source and
index checkpoints.  Everything is RAM: an index is rebuilt in place. -/
abbrev indexLayout (capacity : Nat) : Store.Layout.{0, 0, 0} where
  Namespace := IndexSpace
  Key := IndexSpace.Key capacity
  Value := IndexSpace.Value
  discipline := fun _ => .ram

def finStream (capacity : Nat) : StreamCodec (Fin capacity) where
  encode slot := StreamCodec.nat.encode slot.val
  decodePrefix bytes := do
    let (value, suffix) ← StreamCodec.nat.decodePrefix bytes
    if bound : value < capacity then some (⟨value, bound⟩, suffix) else none
  decodePrefix_encode := by
    intro slot suffix
    simp [StreamCodec.nat.decodePrefix_encode, slot.isLt]

def checkpointStream : StreamCodec CausalCheckpoint :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product (identifierStream .v1 .document)
        (StreamCodec.product
          (StreamCodec.option (identifierStream .v1 .versionEvent))
          StreamCodec.nat)))
    (fun checkpoint => (checkpoint.historyDomain, checkpoint.document,
      checkpoint.head, checkpoint.sequence))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro checkpoint; rfl)

def cursorStream : StreamCodec SyncCursor :=
  StreamCodec.xmap (StreamCodec.product checkpointStream StreamCodec.nat)
    (fun cursor => (cursor.checkpoint, cursor.nextSlot))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro cursor; rfl)

def sourceEntryStream : StreamCodec SourceEntry :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .link) linkRecordStream)
    (fun entry => (entry.linkId, entry.record))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro entry; rfl)

def indexedRowStream : StreamCodec IndexedRow :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .link)
      (StreamCodec.product (identifierStream .v1 .document)
        (StreamCodec.product (StreamCodec.option storedStableRangeStream)
          (StreamCodec.product linkTargetStream
            (StreamCodec.product digestStream
              (identifierStream .v1 .operationIntent))))))
    (fun row => (row.linkId, row.sourceDocument, row.sourceRange, row.target,
      row.relation, row.operation))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1,
      wire.2.2.2.2.2⟩)
    (by intro row; rfl)

def indexSpaceStream : StreamCodec IndexSpace where
  encode
    | .checkpoints => [0]
    | .cursor => [1]
    | .source => [2]
    | .derived => [3]
  decodePrefix
    | 0 :: suffix => some (.checkpoints, suffix)
    | 1 :: suffix => some (.cursor, suffix)
    | 2 :: suffix => some (.source, suffix)
    | 3 :: suffix => some (.derived, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def indexKeyStream (capacity : Nat) :
    (space : IndexSpace) → StreamCodec (IndexSpace.Key capacity space)
  | .checkpoints => StreamCodec.bool
  | .cursor => unitStream
  | .source => finStream capacity
  | .derived => finStream capacity

def indexValueStream : (space : IndexSpace) → StreamCodec (IndexSpace.Value space)
  | .checkpoints => checkpointStream
  | .cursor => cursorStream
  | .source => sourceEntryStream
  | .derived => indexedRowStream

def indexWire (capacity : Nat) : Wire (indexLayout capacity) where
  name := "minidregg/hyperdocument-link-index/v1"
  namespaces := [.checkpoints, .cursor, .source, .derived]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := indexSpaceStream
  keyStream := indexKeyStream capacity
  valueStream := indexValueStream
  keyCodecId
    | .checkpoints => "bool"
    | .cursor => "unit/empty"
    | .source => s!"fin/{capacity}"
    | .derived => s!"fin/{capacity}"
  valueCodecId
    | .checkpoints => "causal-checkpoint/v1"
    | .cursor => "sync-cursor/v1"
    | .source => "link-source-entry/v1"
    | .derived => "link-indexed-row/v1"

def indexMaterializer (capacity : Nat) : CellState.Materializer (indexLayout capacity) Digest :=
  StoreCodec.materializer (indexWire capacity)

/-! ### The index cell carries exactly one semantic snapshot -/

instance IndexSpace.fintype : Fintype IndexSpace where
  elems := {.checkpoints, .cursor, .source, .derived}
  complete := by intro space; cases space <;> simp

instance IndexSpace.keyFintype (capacity : Nat) :
    (space : IndexSpace) → Fintype (IndexSpace.Key capacity space)
  | .checkpoints => inferInstanceAs (Fintype Bool)
  | .cursor => inferInstanceAs (Fintype Unit)
  | .source => inferInstanceAs (Fintype (Fin capacity))
  | .derived => inferInstanceAs (Fintype (Fin capacity))

/-- The value a snapshot places at each index address. -/
def snapshotValue {capacity : Nat} (snapshot : Snapshot capacity) :
    (address : Store.Address (indexLayout capacity)) →
      Option ((indexLayout capacity).Value address.1)
  | ⟨.checkpoints, key⟩ =>
      some (show CausalCheckpoint from
        if (show Bool from key) then snapshot.indexCheckpoint else snapshot.sourceCheckpoint)
  | ⟨.cursor, _⟩ => some (show SyncCursor from snapshot.cursor)
  | ⟨.source, slot⟩ => (snapshot.corpus (show Fin capacity from slot) : Option SourceEntry)
  | ⟨.derived, slot⟩ => (snapshot.index (show Fin capacity from slot) : Option IndexedRow)

/-- The index cell of a snapshot: every index address holds the snapshot's
value there (all index keys are finite). -/
def storeOfSnapshot {capacity : Nat} (snapshot : Snapshot capacity) :
    Store.Store (indexLayout capacity) :=
  DFinsupp.mk Finset.univ fun address => snapshotValue snapshot address.1

@[simp] theorem storeOfSnapshot_apply {capacity : Nat} (snapshot : Snapshot capacity)
    (address : Store.Address (indexLayout capacity)) :
    storeOfSnapshot snapshot address = snapshotValue snapshot address := by
  simp [storeOfSnapshot, DFinsupp.mk_apply]

/-- The semantic snapshot a store denotes, when its checkpoints and cursor are
present. -/
def snapshotOfStore {capacity : Nat} (store : Store.Store (indexLayout capacity)) :
    Option (Snapshot capacity) := do
  let source ← store ⟨.checkpoints, false⟩
  let index ← store ⟨.checkpoints, true⟩
  let cursor ← store ⟨.cursor, ()⟩
  some
    { sourceCheckpoint := source
      indexCheckpoint := index
      cursor := cursor
      corpus := fun slot => store ⟨.source, slot⟩
      index := fun slot => store ⟨.derived, slot⟩ }

/-- **The index cell denotes exactly its snapshot.** -/
theorem snapshotOfStore_storeOfSnapshot {capacity : Nat} (snapshot : Snapshot capacity) :
    snapshotOfStore (storeOfSnapshot snapshot) = some snapshot := by
  simp only [snapshotOfStore, storeOfSnapshot_apply]
  rfl

/-- Freshness classification survives the cell: the status of the stored
snapshot is the snapshot's status. -/
theorem stored_status {capacity : Nat} (snapshot : Snapshot capacity) :
    (snapshotOfStore (storeOfSnapshot snapshot)).map status = some (status snapshot) := by
  rw [snapshotOfStore_storeOfSnapshot]
  rfl

/-- Refuting pole: a store without its cursor denotes no snapshot. -/
theorem no_snapshot_without_cursor {capacity : Nat}
    (store : Store.Store (indexLayout capacity)) (missing : store ⟨.cursor, ()⟩ = none) :
    snapshotOfStore store = none := by
  simp only [snapshotOfStore]
  cases store ⟨.checkpoints, false⟩ <;> cases store ⟨.checkpoints, true⟩ <;>
    simp [missing]

/-! ## Retired page frames refuse to load -/

theorem retired_page_frames_refused (first : UInt8) (rest : List UInt8) (lFrame : first = 76) :
    contentMaterializer.codec.decode (first :: rest) = none ∧
      eventMaterializer.codec.decode (first :: rest) = none ∧
      ∀ capacity, (indexMaterializer capacity).codec.decode (first :: rest) = none := by
  subst lFrame
  exact ⟨decode_other_first_byte contentWire 76 rest (by decide),
    decode_other_first_byte eventWire 76 rest (by decide),
    fun capacity => decode_other_first_byte (indexWire capacity) 76 rest (by decide)⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.HyperdocumentCell.snapshotOfStore_storeOfSnapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapshotOfStore_storeOfSnapshot
/-- info: 'Minidregg.Compiler.HyperdocumentCell.links_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms links_unbounded
/-- info: 'Minidregg.Compiler.HyperdocumentCell.no_snapshot_without_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_snapshot_without_cursor
/-- info: 'Minidregg.Compiler.HyperdocumentCell.retired_page_frames_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_page_frames_refused

end Minidregg.Compiler.HyperdocumentCell
