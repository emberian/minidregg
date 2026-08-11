/-
# Compiler.HyperdocumentContentPageMaterializer -- bounded forward-link content

The canonical Hyperdocument cell is an unbounded dependent sparse map.  This
module chooses one concrete production shard for the forward-link workflow: a
four-slot page containing document, element, and link records.  The page has a
stable version/capacity frame, compact prefix codecs, and a Lean cSHAKE256 root
over the exact framed bytes.

Forward links use `ForwardTarget`, whose document/element/range constructors
carry an explicit `PageRef` (content domain, page number, expected page root).
Projection to `Hyperdocument.LinkRecord` retains the canonical semantic target;
the production page retains and root-commits physical cross-page routing.
Nothing silently treats a globally named element as local to this page.

The bounded page projects into the existing `Hyperdocument.cellSchema`; it is
not a replacement materializer for every unbounded Hyperdocument state.
Capacity exhaustion, duplicate canonical addresses, invalid pages, and wire
version mismatch are explicit.  Hash binding remains pair-scoped rather than
postulating an impossible global injection into a 256-bit range.
-/
import Compiler.HyperdocumentCodec
import Compiler.Sp800185Cshake256
import Theory.Hyperdocument

namespace Minidregg.Compiler.HyperdocumentContentPageMaterializer

open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

theorem lawfulCodec_encode_injective {alpha : Type}
    (codec : LawfulCodec alpha) : Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

/-! ## Exact content-record codecs -/

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

/-! ## Explicit cross-page forward targets -/

/-- Physical routing identity for a bounded page.  `expectedRoot` prevents a
page-number reuse from silently retargeting a stored forward link. -/
structure PageRef where
  contentDomain : Digest
  pageNumber : Nat
  expectedRoot : Digest
  deriving DecidableEq, Repr

def pageRefStream : StreamCodec PageRef :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat digestStream))
    (fun page => (page.contentDomain, page.pageNumber, page.expectedRoot))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro page; rfl)

/-- The bounded production target.  Every typed Hyperdocument target which may
live on another page carries its page reference in the constructor. -/
inductive ForwardTarget where
  | document (page : PageRef) (documentId : DocumentId)
  | element (page : PageRef) (elementId : ElementId)
  | range (page : PageRef) (targetDocument : DocumentId)
      (sourceRange : StableRange)
  | external (scheme authority path : List UInt8)
  deriving DecidableEq, Repr

def ForwardTarget.page? : ForwardTarget -> Option PageRef
  | .document page _ => some page
  | .element page _ => some page
  | .range page _ _ => some page
  | .external _ _ _ => none

def ForwardTarget.toCanonical : ForwardTarget -> LinkTarget
  | .document _ documentId => .document documentId
  | .element _ elementId => .element elementId
  | .range _ targetDocument sourceRange => .range targetDocument sourceRange
  | .external scheme authority path => .external scheme authority path

def forwardTargetStream : StreamCodec ForwardTarget where
  encode
    | .document page documentId =>
        0 :: pageRefStream.encode page ++
          (identifierStream .v1 .document).encode documentId
    | .element page elementId =>
        1 :: pageRefStream.encode page ++
          (identifierStream .v1 .element).encode elementId
    | .range page targetDocument sourceRange =>
        2 :: pageRefStream.encode page ++
          (identifierStream .v1 .document).encode targetDocument ++
          storedStableRangeStream.encode sourceRange
    | .external scheme authority path =>
        3 :: bytesStream.encode scheme ++ bytesStream.encode authority ++
          bytesStream.encode path
  decodePrefix
    | 0 :: bytes => do
        let (page, afterPage) <- pageRefStream.decodePrefix bytes
        let (documentId, suffix) <-
          (identifierStream .v1 .document).decodePrefix afterPage
        some (.document page documentId, suffix)
    | 1 :: bytes => do
        let (page, afterPage) <- pageRefStream.decodePrefix bytes
        let (elementId, suffix) <-
          (identifierStream .v1 .element).decodePrefix afterPage
        some (.element page elementId, suffix)
    | 2 :: bytes => do
        let (page, afterPage) <- pageRefStream.decodePrefix bytes
        let (targetDocument, afterDocument) <-
          (identifierStream .v1 .document).decodePrefix afterPage
        let (sourceRange, suffix) <-
          storedStableRangeStream.decodePrefix afterDocument
        some (.range page targetDocument sourceRange, suffix)
    | 3 :: bytes => do
        let (scheme, afterScheme) <- bytesStream.decodePrefix bytes
        let (authority, afterAuthority) <- bytesStream.decodePrefix afterScheme
        let (path, suffix) <- bytesStream.decodePrefix afterAuthority
        some (.external scheme authority path, suffix)
    | _ => none
  decodePrefix_encode := by
    intro target suffix
    cases target with
    | document page documentId =>
        simp [List.append_assoc, pageRefStream.decodePrefix_encode,
          (identifierStream .v1 .document).decodePrefix_encode]
    | element page elementId =>
        simp [List.append_assoc, pageRefStream.decodePrefix_encode,
          (identifierStream .v1 .element).decodePrefix_encode]
    | range page targetDocument sourceRange =>
        simp [List.append_assoc, pageRefStream.decodePrefix_encode,
          (identifierStream .v1 .document).decodePrefix_encode,
          storedStableRangeStream.decodePrefix_encode]
    | external scheme authority path =>
        simp [List.append_assoc, bytesStream.decodePrefix_encode]

/-- Bounded forward-link data retains cross-page routing before projecting to
the canonical `LinkRecord`. -/
structure ForwardLink where
  sourceDocument : DocumentId
  source : Option StableRange
  target : ForwardTarget
  relation : Digest
  author : PrincipalRef
  operation : OperationId
  tombstonedAt : Option OperationId
  deriving DecidableEq, Repr

def forwardLinkStream : StreamCodec ForwardLink :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.option storedStableRangeStream)
        (StreamCodec.product forwardTargetStream
          (StreamCodec.product digestStream
            (StreamCodec.product principalRefStream
              (StreamCodec.product (identifierStream .v1 .operationIntent)
                (StreamCodec.option
                  (identifierStream .v1 .operationIntent))))))))
    (fun link =>
      (link.sourceDocument, link.source, link.target, link.relation,
        link.author, link.operation, link.tombstonedAt))
    (fun wire =>
      ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
        wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro link; rfl)

def ForwardLink.toCanonical (link : ForwardLink) : LinkRecord where
  sourceDocument := link.sourceDocument
  source := link.source
  target := link.target.toCanonical
  relation := link.relation
  author := link.author
  operation := link.operation
  tombstonedAt := link.tombstonedAt

/-! ## Typed bounded entries and canonical projection -/

inductive Entry where
  | document (documentId : DocumentId) (record : DocumentRecord)
  | element (elementId : ElementId) (record : ElementRecord)
  | link (linkId : LinkId) (record : ForwardLink)
  deriving DecidableEq, Repr

def Entry.address : Entry -> Hyperdocument.Address
  | .document documentId _ => ⟨.documents, documentId⟩
  | .element elementId _ => ⟨.elements, elementId⟩
  | .link linkId _ => ⟨.links, linkId⟩

def Entry.LocalTo (documentId : DocumentId) : Entry -> Prop
  | .document storedDocument _ => storedDocument = documentId
  | .element _ record => record.document = documentId
  | .link _ record => record.sourceDocument = documentId

instance entryLocalToDecidable (documentId : DocumentId) (entry : Entry) :
    Decidable (entry.LocalTo documentId) := by
  cases entry <;> simp [Entry.LocalTo] <;> infer_instance

def entryStream : StreamCodec Entry where
  encode
    | .document documentId record =>
        0 :: (identifierStream .v1 .document).encode documentId ++
          documentRecordStream.encode record
    | .element elementId record =>
        1 :: (identifierStream .v1 .element).encode elementId ++
          elementRecordStream.encode record
    | .link linkId record =>
        2 :: (identifierStream .v1 .link).encode linkId ++
          forwardLinkStream.encode record
  decodePrefix
    | 0 :: bytes => do
        let (documentId, afterId) <-
          (identifierStream .v1 .document).decodePrefix bytes
        let (record, suffix) <- documentRecordStream.decodePrefix afterId
        some (.document documentId record, suffix)
    | 1 :: bytes => do
        let (elementId, afterId) <-
          (identifierStream .v1 .element).decodePrefix bytes
        let (record, suffix) <- elementRecordStream.decodePrefix afterId
        some (.element elementId record, suffix)
    | 2 :: bytes => do
        let (linkId, afterId) <-
          (identifierStream .v1 .link).decodePrefix bytes
        let (record, suffix) <- forwardLinkStream.decodePrefix afterId
        some (.link linkId record, suffix)
    | _ => none
  decodePrefix_encode := by
    intro entry suffix
    cases entry with
    | document documentId record =>
        simp [List.append_assoc,
          (identifierStream .v1 .document).decodePrefix_encode,
          documentRecordStream.decodePrefix_encode]
    | element elementId record =>
        simp [List.append_assoc,
          (identifierStream .v1 .element).decodePrefix_encode,
          elementRecordStream.decodePrefix_encode]
    | link linkId record =>
        simp [List.append_assoc,
          (identifierStream .v1 .link).decodePrefix_encode,
          forwardLinkStream.decodePrefix_encode]

def Entry.install (fields : FieldStore Hyperdocument.cellSchema.{0, 0}) :
    Entry -> FieldStore Hyperdocument.cellSchema.{0, 0}
  | .document documentId record => fields.write ⟨.documents, documentId⟩ record
  | .element elementId record => fields.write ⟨.elements, elementId⟩ record
  | .link linkId record => fields.write ⟨.links, linkId⟩ record.toCanonical

/-! ## Four-slot content pages and admission -/

structure Page where
  contentDomain : Digest
  document : DocumentId
  pageNumber : Nat
  slot0 : Option Entry
  slot1 : Option Entry
  slot2 : Option Entry
  slot3 : Option Entry
  deriving DecidableEq, Repr

abbrev PageTuple :=
  Digest × DocumentId × Nat × Option Entry × Option Entry × Option Entry ×
    Option Entry

def pageTupleStream : StreamCodec PageTuple :=
  StreamCodec.product digestStream
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option entryStream)
          (StreamCodec.product (StreamCodec.option entryStream)
            (StreamCodec.product (StreamCodec.option entryStream)
              (StreamCodec.option entryStream))))))

def pageTuple (page : Page) : PageTuple :=
  ⟨page.contentDomain, page.document, page.pageNumber, page.slot0, page.slot1,
    page.slot2, page.slot3⟩

def pageOfTuple (wire : PageTuple) : Page where
  contentDomain := wire.1
  document := wire.2.1
  pageNumber := wire.2.2.1
  slot0 := wire.2.2.2.1
  slot1 := wire.2.2.2.2.1
  slot2 := wire.2.2.2.2.2.1
  slot3 := wire.2.2.2.2.2.2

@[simp] theorem pageOfTuple_tuple (page : Page) :
    pageOfTuple (pageTuple page) = page :=
  rfl

def pageStream : StreamCodec Page :=
  StreamCodec.xmap pageTupleStream pageTuple pageOfTuple pageOfTuple_tuple

def Page.entries (page : Page) : List Entry :=
  [page.slot0, page.slot1, page.slot2, page.slot3].filterMap _root_.id

def Page.addresses (page : Page) : List Hyperdocument.Address :=
  page.entries.map Entry.address

def Page.Valid (page : Page) : Prop :=
  page.addresses.Nodup /\ page.entries.Forall (Entry.LocalTo page.document)

instance pageValidDecidable (page : Page) : Decidable page.Valid := by
  unfold Page.Valid
  infer_instance

def Page.Contains (page : Page) (entry : Entry) : Prop :=
  entry ∈ page.entries

instance pageContainsDecidable (page : Page) (entry : Entry) :
    Decidable (page.Contains entry) := by
  unfold Page.Contains
  infer_instance

@[simp] theorem Page.entries_length_le_four (page : Page) :
    page.entries.length ≤ 4 := by
  rcases page with
    ⟨contentDomain, document, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.entries]

def Page.Full (page : Page) : Prop :=
  page.slot0.isSome = true /\ page.slot1.isSome = true /\
    page.slot2.isSome = true /\ page.slot3.isSome = true

instance pageFullDecidable (page : Page) : Decidable page.Full := by
  unfold Page.Full
  infer_instance

def Page.insert? (page : Page) (entry : Entry) : Option Page :=
  match page.slot0 with
  | none => some { page with slot0 := some entry }
  | some _ =>
      match page.slot1 with
      | none => some { page with slot1 := some entry }
      | some _ =>
          match page.slot2 with
          | none => some { page with slot2 := some entry }
          | some _ =>
              match page.slot3 with
              | none => some { page with slot3 := some entry }
              | some _ => none

theorem Page.insert_none_iff_full (page : Page) (entry : Entry) :
    page.insert? entry = none <-> page.Full := by
  rcases page with
    ⟨contentDomain, document, pageNumber, slot0, slot1, slot2, slot3⟩
  cases slot0 <;> cases slot1 <;> cases slot2 <;> cases slot3 <;>
    simp [Page.insert?, Page.Full]

def Entry.Conflicts (entry : Entry) (page : Page) : Prop :=
  entry.address ∈ page.addresses

instance entryConflictsDecidable (entry : Entry) (page : Page) :
    Decidable (entry.Conflicts page) := by
  unfold Entry.Conflicts
  infer_instance

inductive InsertError where
  | invalidPage
  | duplicateAddress
  | full
  deriving DecidableEq, Repr

def Page.admitInsert (page : Page) (entry : Entry) :
    Except InsertError { post : Page // post.Valid } :=
  if _pageValid : page.Valid then
    if entry.Conflicts page then
      .error .duplicateAddress
    else if _local : entry.LocalTo page.document then
      match page.insert? entry with
      | none => .error .full
      | some post =>
          if postValid : post.Valid then .ok ⟨post, postValid⟩
          else .error .invalidPage
    else
      .error .invalidPage
  else
    .error .invalidPage

/-- Exact semantic projection into the canonical sparse Hyperdocument state. -/
def Page.toCanonicalState (page : Page) :
    LogicalState Hyperdocument.cellSchema.{0, 0} where
  fields := page.entries.foldl Entry.install 0
  resources := fun resource => nomatch resource

def Entry.routeFor? (linkId : LinkId) : Entry -> Option PageRef
  | .link storedLink record =>
      if storedLink = linkId then record.target.page? else none
  | _ => none

def routeEntries (linkId : LinkId) : List Entry -> Option PageRef
  | [] => none
  | entry :: entries =>
      match entry.routeFor? linkId with
      | some page => some page
      | none => routeEntries linkId entries

/-- Physical routing stays observable from the committed page. -/
def Page.routeForLink (page : Page) (linkId : LinkId) : Option PageRef :=
  routeEntries linkId page.entries

/-! ## Stable framed materialization -/

def schema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => Page
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

def stateOfOption : Option Page -> LogicalState schema
  | none =>
      { fields := 0
        resources := fun resource => nomatch resource }
  | some page =>
      { fields := (0 : FieldStore schema).write () page
        resources := fun resource => nomatch resource }

def pageAt (state : LogicalState schema) : Option Page := state.fields ()

theorem state_ext (state : LogicalState schema) :
    state = stateOfOption (pageAt state) := by
  cases state with
  | mk fields resources =>
      have resourcesExact :
          resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      cases present : fields () with
      | none =>
          have fieldsExact : fields = (0 : FieldStore schema) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [fieldsExact, resourcesExact]
          rfl
      | some page =>
          have fieldsExact :
              fields = (0 : FieldStore schema).write () page := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          rfl

def stateStream : StreamCodec (LogicalState schema) :=
  StreamCodec.xmap (StreamCodec.option pageStream) pageAt stateOfOption
    (by intro state; exact (state_ext state).symm)

/-- Stable marker: `LOOM/HDOC/CONTENTPAGE`, wire version 1, capacity 4. -/
def wireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 67, 79, 78, 84, 69, 78, 84, 80,
    65, 71, 69, 1, 4]

def decodeState : List UInt8 -> Option (LogicalState schema)
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 :: 67 :: 79 ::
      78 :: 84 :: 69 :: 78 :: 84 :: 80 :: 65 :: 71 :: 69 :: 1 :: 4 :: payload =>
      stateStream.toLawful.decode payload
  | _ => none

def stateCodec : LawfulCodec (LogicalState schema) where
  encode state := wireFrame ++ stateStream.encode state
  decode := decodeState
  decode_encode := by
    intro state
    change stateStream.toLawful.decode (stateStream.encode state) = some state
    exact stateStream.toLawful.decode_encode state

def rootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 67, 79, 78, 84, 69, 78, 84, 80,
    65, 71, 69, 46, 82, 79, 79, 84, 47, 118, 49]

theorem wire_and_root_domains_distinct : wireFrame ≠ rootCustomization := by
  decide

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : CellState.Materializer schema Digest where
  codec := stateCodec
  rootBytes := rootBytes

@[simp] theorem encode_absent :
    stateCodec.encode (stateOfOption none) = wireFrame ++ [0] :=
  rfl

@[simp] theorem encode_present (page : Page) :
    stateCodec.encode (stateOfOption (some page)) =
      wireFrame ++ 1 :: pageStream.encode page :=
  rfl

@[simp] theorem reject_wrong_version (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 67, 79, 78, 84, 69, 78,
        84, 80, 65, 71, 69, 2, 4] ++ payload) = none := by
  simp [decodeState]

@[simp] theorem reject_wrong_capacity (payload : List UInt8) :
    decodeState
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 67, 79, 78, 84, 69, 78,
        84, 80, 65, 71, 69, 1, 5] ++ payload) = none := by
  simp [decodeState]

/-! ## Pair-scoped collision-resistance boundary -/

structure Collision (left right : LogicalState schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) =
    rootBytes (stateCodec.encode right)

theorem collision_of_root_eq_of_ne
    {left right : LogicalState schema} (different : left ≠ right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) : Collision left right where
  statesDifferent := different
  bytesDifferent := by
    intro sameBytes
    apply different
    exact lawfulCodec_encode_injective stateCodec sameBytes
  rootsEqual := sameRoot

structure PairBindingPremise (left right : LogicalState schema) : Prop where
  noCollision : ¬ Collision left right

theorem state_eq_of_root_eq
    {left right : LogicalState schema}
    (binding : PairBindingPremise left right)
    (sameRoot : rootBytes (stateCodec.encode left) =
      rootBytes (stateCodec.encode right)) : left = right := by
  by_contra different
  exact binding.noCollision (collision_of_root_eq_of_ne different sameRoot)

/-! ## Closed genesis -> forward-link page update -/

def examplePrincipal : PrincipalRef := ⟨⟨7⟩, .object, ⟨11⟩⟩
def sourceDocument : DocumentId := ⟨⟨100⟩⟩
def rootElement : ElementId := ⟨⟨101⟩⟩
def forwardLinkId : LinkId := ⟨⟨102⟩⟩
def targetElement : ElementId := ⟨⟨201⟩⟩

def targetPage : PageRef where
  contentDomain := ⟨9000⟩
  pageNumber := 6
  expectedRoot := ⟨9006⟩

def documentRecord : DocumentRecord where
  rootElement := rootElement
  schema := ⟨1200⟩
  createdBy := examplePrincipal
  createdAt := ⟨⟨1300⟩⟩

def elementRecord : ElementRecord where
  document := sourceDocument
  parent := none
  body := .container []
  createdBy := examplePrincipal
  createdAt := ⟨⟨1300⟩⟩
  tombstonedAt := none

def forwardLink : ForwardLink where
  sourceDocument := sourceDocument
  source := none
  target := .element targetPage targetElement
  relation := ⟨1400⟩
  author := examplePrincipal
  operation := ⟨⟨1401⟩⟩
  tombstonedAt := none

def genesisPage : Page where
  contentDomain := ⟨8000⟩
  document := sourceDocument
  pageNumber := 0
  slot0 := some (.document sourceDocument documentRecord)
  slot1 := some (.element rootElement elementRecord)
  slot2 := none
  slot3 := none

def linkPage : Page where
  contentDomain := genesisPage.contentDomain
  document := genesisPage.document
  pageNumber := genesisPage.pageNumber
  slot0 := genesisPage.slot0
  slot1 := genesisPage.slot1
  slot2 := some (.link forwardLinkId forwardLink)
  slot3 := none

theorem genesisPage_valid : genesisPage.Valid := by
  decide

theorem linkPage_valid : linkPage.Valid := by
  decide

def genesisCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some genesisPage))

def linkCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some linkPage))

@[simp] theorem linkCell_bytes :
    linkCell.bytes = wireFrame ++ 1 :: pageStream.encode linkPage :=
  rfl

@[simp] theorem linkCell_root :
    linkCell.root =
      (Sp800185Cshake256.hash rootCustomization
        (wireFrame ++ 1 :: pageStream.encode linkPage)).digest :=
  rfl

@[simp] theorem link_post_lookup_exact :
    Hyperdocument.lookup linkPage.toCanonicalState .links forwardLinkId =
      some forwardLink.toCanonical := by
  simp [Hyperdocument.lookup, Page.toCanonicalState, Page.entries, linkPage,
    genesisPage, Entry.install, forwardLinkId]
  rfl

@[simp] theorem cross_page_route_exact :
    linkPage.routeForLink forwardLinkId = some targetPage := by
  simp [Page.routeForLink, routeEntries, Page.entries, linkPage, genesisPage,
    Entry.routeFor?, forwardLinkId, forwardLink, ForwardTarget.page?]

def linkPatch : CellState.Patch schema Digest where
  expectedPreRoot := genesisCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some linkPage }]
  resourceWrites := []

theorem linkPatch_accepted :
    ∃ validated : CellState.ValidatedPatch materializer genesisCell linkPatch,
      CellState.validate materializer genesisCell linkPatch =
        CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show linkPatch.expectedPreRoot = genesisCell.root from rfl)]
  rw [dif_pos
    (show linkPatch.fieldFootprint = linkPatch.namedFields by decide)]
  rw [dif_pos
    (show linkPatch.resourceFootprint = linkPatch.namedResources by decide)]
  exact ⟨_, rfl⟩

theorem accepted_post_exact
    (validated : CellState.ValidatedPatch materializer genesisCell linkPatch) :
    validated.apply = linkCell := by
  apply CellState.Materialized.ext
  change
    { fields := CellState.applyFieldWrites linkPatch.fieldWrites
        genesisCell.logical.fields
      resources := CellState.applyResourceWrites linkPatch.resourceWrites
        genesisCell.logical.resources } =
      stateOfOption (some linkPage)
  congr 1
  apply DFinsupp.ext
  intro field
  cases field
  simp [CellState.applyFieldWrites, linkPatch, genesisCell, stateOfOption,
    CellState.FieldStore.assign]

@[simp] theorem duplicate_link_rejected :
    linkPage.admitInsert (.link forwardLinkId forwardLink) =
      .error .duplicateAddress := by
  decide

def fullPage : Page where
  contentDomain := linkPage.contentDomain
  document := linkPage.document
  pageNumber := linkPage.pageNumber
  slot0 := linkPage.slot0
  slot1 := linkPage.slot1
  slot2 := linkPage.slot2
  slot3 := some (.element ⟨⟨103⟩⟩
    { elementRecord with parent := some rootElement })

theorem fullPage_valid : fullPage.Valid := by
  decide

theorem fullPage_full : fullPage.Full := by
  decide

@[simp] theorem fullPage_overflow_rejected :
    fullPage.admitInsert
      (.link ⟨⟨104⟩⟩ { forwardLink with relation := ⟨1402⟩ }) =
        .error .full := by
  decide

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.HyperdocumentContentPageMaterializer.pageOfTuple_tuple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms pageOfTuple_tuple
/-- info: 'Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateCodec
/-- info: 'Minidregg.Compiler.HyperdocumentContentPageMaterializer.collision_of_root_eq_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collision_of_root_eq_of_ne
/-- info: 'Minidregg.Compiler.HyperdocumentContentPageMaterializer.linkPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkPatch_accepted
/-- info: 'Minidregg.Compiler.HyperdocumentContentPageMaterializer.duplicate_link_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_link_rejected

end Minidregg.Compiler.HyperdocumentContentPageMaterializer
