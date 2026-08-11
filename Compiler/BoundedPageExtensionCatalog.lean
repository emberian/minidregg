/-
# Compiler.BoundedPageExtensionCatalog -- authenticated bounded-page catalog

The three concrete production shards -- Hyperdocument content pages, causal
event pages, and authority/policy pages -- are deliberately extensions rather
than silent changes to the base V1 manifest.  This module gives them one stable
catalog with exact schema, codec, controller, cSHAKE algorithm, wire-version,
capacity, wire-frame, and root-customization pins.

`controllerAtTag` is dependent: selecting a stable tag selects the exact page
state type and its actual lawful codec/root function.  The manifest metadata is
projected from that same controller, so a catalog row cannot name one codec
while dispatching another.

The authenticated catalog address retains canonical bytes together with their
exact Lean cSHAKE digest.  Therefore any effective pin/domain/capacity
substitution changes both canonical bytes and the content-address object.  We
make no claim that the 256-bit digest component alone changes: that would be a
collision-resistance claim, and no such premise appears here.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Compiler.HyperdocumentContentPageMaterializer
import Compiler.HyperdocumentEventPageMaterializer

namespace Minidregg.Compiler.BoundedPageExtensionCatalog

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev ContentPage :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page
abbrev EventPage :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page
abbrev AuthorityPage :=
  Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page

/-! ## Stable dependent controller registry -/

inductive PageKind where
  | content
  | eventHistory
  | authorityPolicy
  deriving DecidableEq, Repr

def PageKind.tag : PageKind -> UInt8
  | .content => 1
  | .eventHistory => 2
  | .authorityPolicy => 3

def kindAtTag : UInt8 -> Option PageKind
  | 1 => some .content
  | 2 => some .eventHistory
  | 3 => some .authorityPolicy
  | _ => none

@[simp] theorem kindAtTag_tag (kind : PageKind) :
    kindAtTag kind.tag = some kind := by
  cases kind <;> rfl

/-- The exact logical-state carrier selected by a stable page kind. -/
def PageKind.State : PageKind -> Type
  | .content => LogicalState
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.schema
  | .eventHistory => LogicalState
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.schema
  | .authorityPolicy => LogicalState
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.schema

/-- Stable deployment pins plus the actual Lean-owned codec and root function. -/
structure Controller (kind : PageKind) where
  schemaId : Digest
  pageCodecId : Digest
  controllerId : Digest
  rootAlgorithmId : Digest
  wireVersion : Nat
  capacity : Nat
  wireFrame : List UInt8
  rootCustomization : List UInt8
  codec : LawfulCodec kind.State
  rootBytes : List UInt8 -> Digest

def contentController : Controller .content where
  schemaId := ⟨91001⟩
  pageCodecId := ⟨92001⟩
  controllerId := ⟨94001⟩
  rootAlgorithmId := ⟨93001⟩
  wireVersion := 1
  capacity := 4
  wireFrame :=
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.wireFrame
  rootCustomization :=
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.rootCustomization
  codec := Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateCodec
  rootBytes :=
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.rootBytes

def eventHistoryController : Controller .eventHistory where
  schemaId := ⟨91002⟩
  pageCodecId := ⟨92002⟩
  controllerId := ⟨94002⟩
  rootAlgorithmId := ⟨93001⟩
  wireVersion := 1
  capacity := 4
  wireFrame := Minidregg.Compiler.HyperdocumentEventPageMaterializer.wireFrame
  rootCustomization :=
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.rootCustomization
  codec := Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateCodec
  rootBytes := Minidregg.Compiler.HyperdocumentEventPageMaterializer.rootBytes

def authorityPolicyController : Controller .authorityPolicy where
  schemaId := ⟨91003⟩
  pageCodecId := ⟨92003⟩
  controllerId := ⟨94003⟩
  rootAlgorithmId := ⟨93001⟩
  wireVersion := 1
  capacity := 4
  wireFrame :=
    Minidregg.Compiler.CredentialAuthorityPageMaterializer.wireFrame
  rootCustomization :=
    Minidregg.Compiler.CredentialAuthorityPageMaterializer.rootCustomization
  codec := Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateCodec
  rootBytes :=
    Minidregg.Compiler.CredentialAuthorityPageMaterializer.rootBytes

def controller : (kind : PageKind) -> Controller kind
  | .content => contentController
  | .eventHistory => eventHistoryController
  | .authorityPolicy => authorityPolicyController

abbrev PackedController := Sigma Controller

def controllerAtTag : UInt8 -> Option PackedController
  | 1 => some ⟨.content, contentController⟩
  | 2 => some ⟨.eventHistory, eventHistoryController⟩
  | 3 => some ⟨.authorityPolicy, authorityPolicyController⟩
  | _ => none

@[simp] theorem controllerAtTag_tag (kind : PageKind) :
    controllerAtTag kind.tag = some ⟨kind, controller kind⟩ := by
  cases kind <;> rfl

@[simp] theorem content_codec_lookup_exact :
    (controller .content).codec =
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateCodec :=
  rfl

@[simp] theorem event_codec_lookup_exact :
    (controller .eventHistory).codec =
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateCodec :=
  rfl

@[simp] theorem authority_codec_lookup_exact :
    (controller .authorityPolicy).codec =
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateCodec :=
  rfl

/-! ## Stable manifest rows and exact catalog lookup -/

structure CatalogEntry where
  kind : PageKind
  schemaId : Digest
  pageCodecId : Digest
  controllerId : Digest
  rootAlgorithmId : Digest
  wireVersion : Nat
  capacity : Nat
  wireFrame : List UInt8
  rootCustomization : List UInt8
  deriving DecidableEq, Repr

def Controller.catalogEntry {kind : PageKind}
    (selected : Controller kind) : CatalogEntry where
  kind := kind
  schemaId := selected.schemaId
  pageCodecId := selected.pageCodecId
  controllerId := selected.controllerId
  rootAlgorithmId := selected.rootAlgorithmId
  wireVersion := selected.wireVersion
  capacity := selected.capacity
  wireFrame := selected.wireFrame
  rootCustomization := selected.rootCustomization

structure Catalog where
  catalogVersion : Nat
  content : CatalogEntry
  eventHistory : CatalogEntry
  authorityPolicy : CatalogEntry
  deriving DecidableEq, Repr

def deployedCatalog : Catalog where
  catalogVersion := 1
  content := contentController.catalogEntry
  eventHistory := eventHistoryController.catalogEntry
  authorityPolicy := authorityPolicyController.catalogEntry

def Catalog.lookup (catalog : Catalog) : PageKind -> Option CatalogEntry
  | .content => some catalog.content
  | .eventHistory => some catalog.eventHistory
  | .authorityPolicy => some catalog.authorityPolicy

@[simp] theorem deployedCatalog_lookup_exact (kind : PageKind) :
    deployedCatalog.lookup kind = some (controller kind).catalogEntry := by
  cases kind <;> rfl

/-! ## Canonical catalog bytes -/

def pageKindStream : StreamCodec PageKind where
  encode
    | .content => [1]
    | .eventHistory => [2]
    | .authorityPolicy => [3]
  decodePrefix
    | 1 :: suffix => some (.content, suffix)
    | 2 :: suffix => some (.eventHistory, suffix)
    | 3 :: suffix => some (.authorityPolicy, suffix)
    | _ => none
  decodePrefix_encode := by
    intro kind suffix
    cases kind <;> rfl

abbrev CatalogEntryTuple :=
  PageKind × Digest × Digest × Digest × Digest × Nat × Nat × List UInt8 ×
    List UInt8

def catalogEntryTupleStream : StreamCodec CatalogEntryTuple :=
  StreamCodec.product pageKindStream
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product bytesStream bytesStream)))))))

def catalogEntryTuple (entry : CatalogEntry) : CatalogEntryTuple :=
  ⟨entry.kind, entry.schemaId, entry.pageCodecId, entry.controllerId,
    entry.rootAlgorithmId, entry.wireVersion, entry.capacity, entry.wireFrame,
    entry.rootCustomization⟩

def catalogEntryOfTuple (wire : CatalogEntryTuple) : CatalogEntry where
  kind := wire.1
  schemaId := wire.2.1
  pageCodecId := wire.2.2.1
  controllerId := wire.2.2.2.1
  rootAlgorithmId := wire.2.2.2.2.1
  wireVersion := wire.2.2.2.2.2.1
  capacity := wire.2.2.2.2.2.2.1
  wireFrame := wire.2.2.2.2.2.2.2.1
  rootCustomization := wire.2.2.2.2.2.2.2.2

@[simp] theorem catalogEntryOfTuple_tuple (entry : CatalogEntry) :
    catalogEntryOfTuple (catalogEntryTuple entry) = entry :=
  rfl

def catalogEntryStream : StreamCodec CatalogEntry :=
  StreamCodec.xmap catalogEntryTupleStream catalogEntryTuple
    catalogEntryOfTuple catalogEntryOfTuple_tuple

abbrev CatalogTuple := Nat × CatalogEntry × CatalogEntry × CatalogEntry

def catalogTupleStream : StreamCodec CatalogTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product catalogEntryStream
      (StreamCodec.product catalogEntryStream catalogEntryStream))

def catalogTuple (catalog : Catalog) : CatalogTuple :=
  ⟨catalog.catalogVersion, catalog.content, catalog.eventHistory,
    catalog.authorityPolicy⟩

def catalogOfTuple (wire : CatalogTuple) : Catalog where
  catalogVersion := wire.1
  content := wire.2.1
  eventHistory := wire.2.2.1
  authorityPolicy := wire.2.2.2

@[simp] theorem catalogOfTuple_tuple (catalog : Catalog) :
    catalogOfTuple (catalogTuple catalog) = catalog :=
  rfl

def catalogStream : StreamCodec Catalog :=
  StreamCodec.xmap catalogTupleStream catalogTuple catalogOfTuple
    catalogOfTuple_tuple

/-- Stable marker: `LOOM/EXTENSION/PAGECATALOG`, catalog wire version 1. -/
def catalogWireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 69, 88, 84, 69, 78, 83, 73, 79, 78, 47, 80, 65, 71,
    69, 67, 65, 84, 65, 76, 79, 71, 1]

def decodeCatalog : List UInt8 -> Option Catalog
  | 76 :: 79 :: 79 :: 77 :: 47 :: 69 :: 88 :: 84 :: 69 :: 78 :: 83 :: 73 ::
      79 :: 78 :: 47 :: 80 :: 65 :: 71 :: 69 :: 67 :: 65 :: 84 :: 65 :: 76 ::
      79 :: 71 :: 1 :: payload => catalogStream.toLawful.decode payload
  | _ => none

def catalogCodec : LawfulCodec Catalog where
  encode catalog := catalogWireFrame ++ catalogStream.encode catalog
  decode := decodeCatalog
  decode_encode := by
    intro catalog
    change catalogStream.toLawful.decode (catalogStream.encode catalog) =
      some catalog
    exact catalogStream.toLawful.decode_encode catalog

theorem catalogCodec_encode_injective :
    Function.Injective catalogCodec.encode := by
  intro left right equal
  have decoded := congrArg catalogCodec.decode equal
  rw [catalogCodec.decode_encode, catalogCodec.decode_encode] at decoded
  exact Option.some.inj decoded

/-! ## Authenticated content address, without a CR claim -/

def catalogAddressCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 69, 88, 84, 69, 78, 83, 73, 79, 78, 46, 80, 65, 71,
    69, 67, 65, 84, 65, 76, 79, 71, 46, 65, 68, 68, 82, 69, 83, 83, 47, 118,
    49]

structure ContentAddress where
  canonicalBytes : List UInt8
  digest : Digest
  digestExact : digest =
    (Sp800185Cshake256.hash catalogAddressCustomization canonicalBytes).digest

def Catalog.contentAddress (catalog : Catalog) : ContentAddress where
  canonicalBytes := catalogCodec.encode catalog
  digest :=
    (Sp800185Cshake256.hash catalogAddressCustomization
      (catalogCodec.encode catalog)).digest
  digestExact := rfl

theorem contentAddress_ne_of_catalog_ne {left right : Catalog}
    (different : left ≠ right) :
    left.contentAddress ≠ right.contentAddress := by
  intro sameAddress
  apply different
  apply catalogCodec_encode_injective
  exact congrArg ContentAddress.canonicalBytes sameAddress

/-! ## Any effective pin/domain/capacity substitution changes the address -/

inductive EntrySubstitution where
  | schemaId (replacement : Digest)
  | pageCodecId (replacement : Digest)
  | controllerId (replacement : Digest)
  | rootAlgorithmId (replacement : Digest)
  | wireVersion (replacement : Nat)
  | capacity (replacement : Nat)
  | wireFrame (replacement : List UInt8)
  | rootCustomization (replacement : List UInt8)
  deriving DecidableEq, Repr

def EntrySubstitution.apply (substitution : EntrySubstitution)
    (entry : CatalogEntry) : CatalogEntry :=
  match substitution with
  | .schemaId replacement => { entry with schemaId := replacement }
  | .pageCodecId replacement => { entry with pageCodecId := replacement }
  | .controllerId replacement => { entry with controllerId := replacement }
  | .rootAlgorithmId replacement => { entry with rootAlgorithmId := replacement }
  | .wireVersion replacement => { entry with wireVersion := replacement }
  | .capacity replacement => { entry with capacity := replacement }
  | .wireFrame replacement => { entry with wireFrame := replacement }
  | .rootCustomization replacement =>
      { entry with rootCustomization := replacement }

def EntrySubstitution.Changes (substitution : EntrySubstitution)
    (entry : CatalogEntry) : Prop :=
  match substitution with
  | .schemaId replacement => replacement ≠ entry.schemaId
  | .pageCodecId replacement => replacement ≠ entry.pageCodecId
  | .controllerId replacement => replacement ≠ entry.controllerId
  | .rootAlgorithmId replacement => replacement ≠ entry.rootAlgorithmId
  | .wireVersion replacement => replacement ≠ entry.wireVersion
  | .capacity replacement => replacement ≠ entry.capacity
  | .wireFrame replacement => replacement ≠ entry.wireFrame
  | .rootCustomization replacement => replacement ≠ entry.rootCustomization

theorem EntrySubstitution.apply_ne_of_changes
    (substitution : EntrySubstitution) (entry : CatalogEntry)
    (changes : substitution.Changes entry) :
    substitution.apply entry ≠ entry := by
  cases substitution with
  | schemaId replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.schemaId equal)
  | pageCodecId replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.pageCodecId equal)
  | controllerId replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.controllerId equal)
  | rootAlgorithmId replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.rootAlgorithmId equal)
  | wireVersion replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.wireVersion equal)
  | capacity replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.capacity equal)
  | wireFrame replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.wireFrame equal)
  | rootCustomization replacement =>
      intro equal
      exact changes (congrArg CatalogEntry.rootCustomization equal)

def Catalog.entry (catalog : Catalog) : PageKind -> CatalogEntry
  | .content => catalog.content
  | .eventHistory => catalog.eventHistory
  | .authorityPolicy => catalog.authorityPolicy

def Catalog.setEntry (catalog : Catalog) : PageKind -> CatalogEntry -> Catalog
  | .content, replacement => { catalog with content := replacement }
  | .eventHistory, replacement => { catalog with eventHistory := replacement }
  | .authorityPolicy, replacement =>
      { catalog with authorityPolicy := replacement }

@[simp] theorem Catalog.entry_setEntry (catalog : Catalog) (kind : PageKind)
    (replacement : CatalogEntry) :
    (catalog.setEntry kind replacement).entry kind = replacement := by
  cases kind <;> rfl

def Catalog.substitute (catalog : Catalog) (kind : PageKind)
    (substitution : EntrySubstitution) : Catalog :=
  catalog.setEntry kind (substitution.apply (catalog.entry kind))

theorem Catalog.substitute_ne_of_changes (catalog : Catalog) (kind : PageKind)
    (substitution : EntrySubstitution)
    (changes : substitution.Changes (catalog.entry kind)) :
    catalog.substitute kind substitution ≠ catalog := by
  intro sameCatalog
  have entryEqual := congrArg (fun selected => selected.entry kind) sameCatalog
  have appliedEqual :
      substitution.apply (catalog.entry kind) = catalog.entry kind := by
    simpa [Catalog.substitute] using entryEqual
  exact substitution.apply_ne_of_changes (catalog.entry kind) changes appliedEqual

theorem Catalog.substitution_changes_canonical_bytes
    (catalog : Catalog) (kind : PageKind)
    (substitution : EntrySubstitution)
    (changes : substitution.Changes (catalog.entry kind)) :
    catalogCodec.encode (catalog.substitute kind substitution) ≠
      catalogCodec.encode catalog := by
  intro sameBytes
  exact catalog.substitute_ne_of_changes kind substitution changes
    (catalogCodec_encode_injective sameBytes)

theorem Catalog.substitution_changes_contentAddress
    (catalog : Catalog) (kind : PageKind)
    (substitution : EntrySubstitution)
    (changes : substitution.Changes (catalog.entry kind)) :
    (catalog.substitute kind substitution).contentAddress ≠
      catalog.contentAddress :=
  contentAddress_ne_of_catalog_ne
    (catalog.substitute_ne_of_changes kind substitution changes)

/-! ## Positive extension bundle and cross-page reference validation -/

def contentPageRoot (page : ContentPage) : Digest :=
  (CellState.materialize
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
    (Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateOfOption
      (some page))).root

def targetDocumentId : DocumentId := ⟨⟨5100⟩⟩
def targetElementId : ElementId := ⟨⟨5101⟩⟩

def targetDocumentRecord : DocumentRecord where
  rootElement := targetElementId
  schema := ⟨5110⟩
  createdBy :=
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.examplePrincipal
  createdAt := ⟨⟨5111⟩⟩

def targetElementRecord : ElementRecord where
  document := targetDocumentId
  parent := none
  body := .container []
  createdBy :=
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.examplePrincipal
  createdAt := ⟨⟨5111⟩⟩
  tombstonedAt := none

def targetContentPage : ContentPage where
  contentDomain := ⟨5000⟩
  document := targetDocumentId
  pageNumber := 6
  slot0 := some (.document targetDocumentId targetDocumentRecord)
  slot1 := some (.element targetElementId targetElementRecord)
  slot2 := none
  slot3 := none

def positiveTargetRef :
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.PageRef where
  contentDomain := targetContentPage.contentDomain
  pageNumber := targetContentPage.pageNumber
  expectedRoot := contentPageRoot targetContentPage

def sourceForwardLink :
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.ForwardLink :=
  { Minidregg.Compiler.HyperdocumentContentPageMaterializer.forwardLink with
    target := .element positiveTargetRef targetElementId }

def sourceContentPage : ContentPage :=
  { Minidregg.Compiler.HyperdocumentContentPageMaterializer.genesisPage with
    slot2 := some (.link
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.forwardLinkId
      sourceForwardLink) }

theorem targetContentPage_valid : targetContentPage.Valid := by
  decide

theorem sourceContentPage_valid : sourceContentPage.Valid := by
  decide

def findContentPage (domain : Digest) (pageNumber : Nat) :
    List ContentPage -> Option ContentPage
  | [] => none
  | page :: pages =>
      if page.contentDomain = domain /\ page.pageNumber = pageNumber then
        some page
      else
        findContentPage domain pageNumber pages

def pageRefValidIn
    (reference :
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.PageRef)
    (pages : List ContentPage) : Prop :=
  match findContentPage reference.contentDomain reference.pageNumber pages with
  | none => False
  | some page => contentPageRoot page = reference.expectedRoot

def contentEntryRefs :
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Entry ->
      List Minidregg.Compiler.HyperdocumentContentPageMaterializer.PageRef
  | .link _ record => record.target.page?.toList
  | _ => []

def contentPageRefs (page : ContentPage) :
    List Minidregg.Compiler.HyperdocumentContentPageMaterializer.PageRef :=
  page.entries.flatMap contentEntryRefs

def CrossPageReferencesValid (pages : List ContentPage) : Prop :=
  ∀ page, page ∈ pages ->
    ∀ reference, reference ∈ contentPageRefs page ->
      pageRefValidIn reference pages

def positiveContentPages : List ContentPage :=
  [sourceContentPage, targetContentPage]

@[simp] theorem positive_target_reference_valid :
    pageRefValidIn positiveTargetRef positiveContentPages := by
  have sourceDomainNe :
      sourceContentPage.contentDomain ≠ targetContentPage.contentDomain := by
    decide
  simp [pageRefValidIn, findContentPage, positiveContentPages,
    positiveTargetRef, sourceDomainNe]

theorem positive_cross_page_references_valid :
    CrossPageReferencesValid positiveContentPages := by
  intro page pageMember reference referenceMember
  have pageExact :
      page = sourceContentPage ∨ page = targetContentPage := by
    simpa [positiveContentPages] using pageMember
  rcases pageExact with rfl | rfl
  · have referenceExact : reference = positiveTargetRef := by
      simpa [contentPageRefs, contentEntryRefs, sourceContentPage,
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.genesisPage,
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries,
        sourceForwardLink,
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.ForwardTarget.page?]
        using referenceMember
    subst reference
    exact positive_target_reference_valid
  · simp [contentPageRefs, contentEntryRefs, targetContentPage,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries]
      at referenceMember

structure ExtensionBundle where
  catalog : Catalog
  contentPages : List ContentPage
  eventPages : List EventPage
  authorityPages : List AuthorityPage
  contentValid : ∀ page, page ∈ contentPages -> page.Valid
  eventValid : ∀ page, page ∈ eventPages ->
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page.Valid page
  authorityValid : ∀ page, page ∈ authorityPages -> page.Valid
  crossPageReferencesValid : CrossPageReferencesValid contentPages

/-- Replace only the authenticated extension manifest; concrete page evidence is
unchanged and remains independently checked. -/
def ExtensionBundle.substituteManifest (bundle : ExtensionBundle)
    (kind : PageKind) (substitution : EntrySubstitution) : ExtensionBundle :=
  { bundle with catalog := bundle.catalog.substitute kind substitution }

def ExtensionBundle.manifestCanonicalBytes
    (bundle : ExtensionBundle) : List UInt8 :=
  catalogCodec.encode bundle.catalog

def ExtensionBundle.manifestAddress
    (bundle : ExtensionBundle) : ContentAddress :=
  bundle.catalog.contentAddress

def positiveBundle : ExtensionBundle where
  catalog := deployedCatalog
  contentPages := positiveContentPages
  eventPages :=
    [Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage]
  authorityPages :=
    [Minidregg.Compiler.CredentialAuthorityPageMaterializer.postPage]
  contentValid := by
    intro page member
    have pageExact :
        page = sourceContentPage ∨ page = targetContentPage := by
      simpa [positiveContentPages] using member
    rcases pageExact with rfl | rfl
    · exact sourceContentPage_valid
    · exact targetContentPage_valid
  eventValid := by
    intro page member
    simp only [List.mem_singleton] at member
    subst page
    exact Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage_valid
  authorityValid := by
    intro page member
    simp only [List.mem_singleton] at member
    subst page
    exact Minidregg.Compiler.CredentialAuthorityPageMaterializer.postPage_valid
  crossPageReferencesValid := positive_cross_page_references_valid

@[simp] theorem positiveBundle_catalog_exact :
    positiveBundle.catalog = deployedCatalog :=
  rfl

theorem positiveBundle_substitution_changes_canonical_bytes
    (kind : PageKind) (substitution : EntrySubstitution)
    (changes : substitution.Changes (positiveBundle.catalog.entry kind)) :
    (positiveBundle.substituteManifest kind substitution).manifestCanonicalBytes
      ≠ positiveBundle.manifestCanonicalBytes :=
  positiveBundle.catalog.substitution_changes_canonical_bytes kind substitution
    changes

theorem positiveBundle_substitution_changes_address
    (kind : PageKind) (substitution : EntrySubstitution)
    (changes : substitution.Changes (positiveBundle.catalog.entry kind)) :
    (positiveBundle.substituteManifest kind substitution).manifestAddress ≠
      positiveBundle.manifestAddress :=
  positiveBundle.catalog.substitution_changes_contentAddress kind substitution
    changes

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.BoundedPageExtensionCatalog.controllerAtTag_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controllerAtTag_tag
/-- info: 'Minidregg.Compiler.BoundedPageExtensionCatalog.catalogCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catalogCodec
/-- info: 'Minidregg.Compiler.BoundedPageExtensionCatalog.Catalog.substitution_changes_contentAddress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Catalog.substitution_changes_contentAddress
/-- info: 'Minidregg.Compiler.BoundedPageExtensionCatalog.positive_cross_page_references_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_cross_page_references_valid

end Minidregg.Compiler.BoundedPageExtensionCatalog
