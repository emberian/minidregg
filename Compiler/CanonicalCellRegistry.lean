/-
# Compiler.CanonicalCellRegistry — one executable receiving registry

The production registry of deployed cell roles.  Every role's materializer is
a `StoreCodec` cell at its layout (DATAMODEL B1): the hyperdocument content and
event-log cells (`HyperdocumentCell`), the one credential-authority cell
(`CredentialAuthorityCell`), the declared-effect cells (`DeclaredEffectCell`),
the canonical resource Book, and immutable policy source cells.  There are no
pages, shards or catalogue: the authority domain is one cell at the
deployment's pinned `authorityCellId`.

Kinds are semantic roles, even when their layout is shared.  Object/program/
account-metadata roles have source-owned field laws and typed dispatch.  No
such role may carry an `accountBalance` field: only the domain's configured
resource Book owns money.

`CellLaw` is an invariant for loaded and FINAL post cells, not only a birth
check.  `UserInitial` further refuses internal authority, Book and
event-history payloads.  Those cells are produced by their source-owned
semantic lowerings.  The registry supplies no public raw-state installation
endpoint.

**Domain.**  A store cell carries no in-cell domain tag: the cell's deployment
is the directory that holds it.  The one place a domain is semantic data is
the hyperdocument event record (`VersionEventRecord.historyDomain`, hashed into
the event id and supplied by the authoring request), so the event-history law
requires every recorded event to name this deployment's domain
(`foreign_domain_event_refused`).
-/
import Compiler.DeclaredEffectCell
import Compiler.CredentialAuthorityCell
import Compiler.HyperdocumentCell
import Compiler.CanonicalResourcePageMaterializer
import Compiler.ResourceBirthCodec
import Compiler.PolicySourceCell
import Kernel.PayCell
import Compiler.StreamCell
import Compiler.NockProgramCodec
import Kernel.ClockCell
import Theory.CanonicalResourceBookInvariant

namespace Minidregg.Compiler.CanonicalCellRegistry

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.Store (Store)

set_option autoImplicit false

inductive Kind where
  | content
  | eventHistory
  | authority
  | declaredObject
  | resourceBook
  | accountMetadata
  | declaredProgram
  | policySource
  /-- The deployment's pay cell (`Kernel.PayCell`): tariff, deposit address
  book and assignment. Time is the clock cell's. -/
  | pay
  /-- A dense append-only sequence log (`StreamCell`): a per-author stream. -/
  | stream
  /-- A Nock program cell (`NockProgramCodec`): jam + ABI, keyed by programId. -/
  | nockProgram
  /-- The deployment's one clock (`Kernel.ClockCell`): unix seconds and the
  last observed chain slot, advanced only by `ClockTickReceiver`. -/
  | clock
  deriving DecidableEq, Repr

def Kind.all : List Kind :=
  [.content, .eventHistory, .authority, .declaredObject,
    .resourceBook, .accountMetadata, .declaredProgram, .policySource, .pay, .stream, .nockProgram, .clock]

/-- Tags 1/2/3/5/6/8/9/10/11/12/13/14 are deployment pins. The final table across
lanes: 11 pay, 12 stream, 13 nockProgram, 14 clock.  Tag 3 is the one authority
cell (it was the authority page shard).  Tag 7 (the authority catalogue) is
retired and decodes to nothing; tag 4 was never assigned. -/
def Kind.tag : Kind → UInt8
  | .content => 1
  | .eventHistory => 2
  | .authority => 3
  | .declaredObject => 5
  | .resourceBook => 6
  | .accountMetadata => 8
  | .declaredProgram => 9
  | .policySource => PolicySourceCell.registryTag
  | .pay => 11
  | .stream => 12
  | .nockProgram => NockProgramCodec.registryTag
  | .clock => 14

def kindAtTag : UInt8 → Option Kind
  | 1 => some .content
  | 2 => some .eventHistory
  | 3 => some .authority
  | 5 => some .declaredObject
  | 6 => some .resourceBook
  | 8 => some .accountMetadata
  | 9 => some .declaredProgram
  | 10 => some .policySource
  | 11 => some .pay
  | 12 => some .stream
  | 13 => some .nockProgram
  | 14 => some .clock
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) : kindAtTag kind.tag = some kind := by
  cases kind <;> rfl

/-- The retired catalogue tag selects no role: a packed catalogue cell refuses
to decode. -/
theorem retired_catalogue_tag : kindAtTag 7 = none := rfl

/-- Store-cell wire versions.  Content, event and authority moved from page
frames to `StoreCodec` frames; authority v6 tags every capability scope's
target set (explicit or `under` a room); the Book's balance codec became the zigzag
integer codec; the declared roles moved in S2c. -/
def schemaRef : Kind → SchemaRef
  | .content => ⟨⟨91001⟩, 3⟩
  | .eventHistory => ⟨⟨91002⟩, 2⟩
  | .authority => ⟨⟨91003⟩, 7⟩
  | .declaredObject => ⟨⟨91004⟩, 2⟩
  | .resourceBook => ⟨⟨91005⟩, 3⟩
  | .accountMetadata => ⟨⟨91007⟩, 2⟩
  | .declaredProgram => ⟨⟨91008⟩, 2⟩
  | .policySource => ⟨⟨PolicySourceCell.schemaId⟩, PolicySourceCell.wireVersion⟩
  | .pay => ⟨⟨91010⟩, 3⟩
  | .stream => ⟨⟨91012⟩, 1⟩
  | .nockProgram => ⟨⟨NockProgramCodec.schemaId⟩, NockProgramCodec.wireVersion⟩
  | .clock => ⟨⟨91013⟩, 1⟩

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right same
  cases left <;> cases right <;>
    simp [schemaRef, PolicySourceCell.schemaId, PolicySourceCell.wireVersion,
      NockProgramCodec.schemaId, NockProgramCodec.wireVersion] at same ⊢

abbrev layout : Kind → Store.Layout.{0, 0, 0}
  | .content => Hyperdocument.layout
  | .eventHistory => Kernel.HyperdocumentEventLog.Sparse.layout
  | .authority => CredentialAuthorityState.layout
  | .declaredObject => EffectDeclaration.effectLayout
  | .resourceBook => CanonicalResourceKernel.layout
  | .accountMetadata => EffectDeclaration.effectLayout
  | .declaredProgram => EffectDeclaration.effectLayout
  | .policySource => PolicySourceCell.layout
  | .pay => Kernel.PayCell.layout
  | .stream => StreamCell.layout
  | .nockProgram => NockProgramCodec.layout
  | .clock => Kernel.ClockCell.layout

def materializer : (kind : Kind) → Materializer (layout kind) Digest
  | .content => HyperdocumentCell.contentMaterializer
  | .eventHistory => HyperdocumentCell.eventMaterializer
  | .authority => CredentialAuthorityCell.materializer
  | .declaredObject => DeclaredEffectCell.materializer
  | .resourceBook => CanonicalResourcePageMaterializer.materializer
  | .accountMetadata => DeclaredEffectCell.materializer
  | .declaredProgram => DeclaredEffectCell.materializer
  | .policySource => PolicySourceCell.materializer
  | .pay => Kernel.PayCell.materializer
  | .stream => StreamCell.materializer
  | .nockProgram => NockProgramCodec.materializer
  | .clock => Kernel.ClockCell.materializer

/-- The store wire of every kind whose materializer is the generic
`StoreCodec.materializer` (K-NARROW-HIDE): its salted root opens per entry. -/
def wire? : (kind : Kind) → Option (StoreCodec.Wire (layout kind))
  | .content => some HyperdocumentCell.contentWire
  | .eventHistory => some HyperdocumentCell.eventWire
  | .authority => some CredentialAuthorityCell.wire
  | .declaredObject => some DeclaredEffectCell.wire
  | .accountMetadata => some DeclaredEffectCell.wire
  | .declaredProgram => some DeclaredEffectCell.wire
  | .pay => some Kernel.PayCell.wire
  | .stream => some StreamCell.wire
  | .clock => some Kernel.ClockCell.wire
  | .resourceBook | .policySource | .nockProgram => none

/-- A kind with a store wire is materialized by it, so its cell root is that
wire's salted root. -/
theorem materializer_of_wire {kind : Kind} {wire : StoreCodec.Wire (layout kind)}
    (selected : wire? kind = some wire) : materializer kind = StoreCodec.materializer wire := by
  cases kind <;> simp [wire?] at selected <;> subst selected <;> rfl

/-- Whether a cell holds its hiding key. -/
def blinded : (kind : Kind) → Store (layout kind) → Bool
  | kind, store =>
      match wire? kind with
      | some wire => (StoreCodec.blindingKey wire store).isSome
      | none => false

/-- Whether an address is a kind's blinding address. -/
def isBlinding (kind : Kind) (address : Store.Address (layout kind)) : Bool :=
  match wire? kind with
  | some wire => decide (wire.blinding = some address)
  | none => false

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  layout := layout
  materializer := materializer
  rootBytes := ResourceBirthCodec.rootBytes

instance registryKindDecidableEq : DecidableEq registry.Kind :=
  inferInstanceAs (DecidableEq Kind)

/-- This is a source-fixed role mapping, never a caller-supplied callback.
Book is an internal account resource; accountMetadata is the user's identity. -/
def resourceKindOf : Kind → ResourceKind
  | .accountMetadata | .resourceBook => .account
  | .declaredProgram => .program
  | _ => .object

def factoryKind : Kind := .declaredObject

def sourceEncoding : ResourceBirth.SourceEncoding registry :=
  ResourceBirthCodec.sourceEncoding registry resourceKindOf

@[simp] theorem registry_content_materializer :
    registry.materializer .content = HyperdocumentCell.contentMaterializer := rfl
@[simp] theorem registry_event_materializer :
    registry.materializer .eventHistory = HyperdocumentCell.eventMaterializer := rfl
@[simp] theorem registry_authority_materializer :
    registry.materializer .authority = CredentialAuthorityCell.materializer := rfl
@[simp] theorem registry_book_materializer :
    registry.materializer .resourceBook = CanonicalResourcePageMaterializer.materializer := rfl
@[simp] theorem registry_factory_materializer :
    registry.materializer factoryKind = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_account_materializer :
    registry.materializer .accountMetadata = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_policy_source_materializer :
    registry.materializer .policySource = PolicySourceCell.materializer := rfl
@[simp] theorem registry_pay_materializer :
    registry.materializer .pay = Kernel.PayCell.materializer := rfl
@[simp] theorem registry_stream_materializer :
    registry.materializer .stream = StreamCell.materializer := rfl
@[simp] theorem registry_nock_program_materializer :
    registry.materializer .nockProgram = NockProgramCodec.materializer := rfl
@[simp] theorem registry_program_materializer :
    registry.materializer .declaredProgram = DeclaredEffectCell.materializer := rfl
@[simp] theorem registry_lifecycle_root :
    registry.rootBytes = ResourceBirthCodec.rootBytes := rfl

/-- Strict dependent decoding preserves the exact selected native codec/root.
It also rejects aliases accepted by older primitive prefix decoders. -/
def cellCodec : LawfulCodec (PackedCell registry) :=
  ResourceBirthCodec.strictCodec (PackedCell.codec registry)

@[simp] theorem cell_roundtrip (cell : PackedCell registry) :
    cellCodec.decode (cellCodec.encode cell) = some cell := cellCodec.decode_encode cell

theorem decoded_cell_canonical {bytes : List UInt8} {cell : PackedCell registry}
    (accepted : cellCodec.decode bytes = some cell) : PackedCell.bytes registry cell = bytes :=
  ResourceBirthCodec.strictCodec_canonical (PackedCell.codec registry) accepted

/-! ## Source-owned role and identity laws -/

/-- Pins belong to one deployment/authority domain. They do not impose one
Book across all nodes or domains. A request cannot choose a different Book or
authority cell merely because its payload has the right schema tag. -/
structure Deployment where
  domain : Digest
  factoryId : Nat
  resourceBookId : Nat
  authorityCellId : Nat
  deriving DecidableEq, Repr

def Deployment.Valid (deployment : Deployment) : Prop :=
  [deployment.factoryId, deployment.resourceBookId, deployment.authorityCellId].Nodup

instance deploymentValidDecidable (deployment : Deployment) : Decidable deployment.Valid := by
  unfold Deployment.Valid
  infer_instance

/-- Field constructors, not textual key names, determine role membership.
The account role's cell contains metadata only; it cannot encode money. -/
def KeyAllowed (kind : ResourceKind) (cellId : Nat) : StateKey → Prop
  | .objectField object _ =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId
  | .programCode program => kind = .program ∧ program.value = cellId
  | .accountBalance _ _ => False
  | .blinding => True

instance keyAllowedDecidable (kind : ResourceKind) (cellId : Nat) (key : StateKey) :
    Decidable (KeyAllowed kind cellId key) := by
  cases key <;> unfold KeyAllowed <;> infer_instance

theorem accountBalance_never_allowed (kind : ResourceKind) (cellId : Nat)
    (account : ResourceId .account) (asset : Digest) :
    ¬KeyAllowed kind cellId (.accountBalance account asset) := fun impossible => impossible

/-- The declared-cell law: every present field is a key this role allows at
this cell.  There is no capacity, no shard number and no in-cell domain tag:
the cell's domain is the directory that holds it. -/
def DeclaredCellLaw (kind : ResourceKind) (cellId : Nat) (store : Store effectLayout) : Prop :=
  ∀ address ∈ store.support, KeyAllowed kind cellId address.2

instance declaredCellLawDecidable (kind : ResourceKind) (cellId : Nat)
    (store : Store effectLayout) : Decidable (DeclaredCellLaw kind cellId store) := by
  unfold DeclaredCellLaw
  infer_instance

theorem DeclaredCellLaw.no_balance (kind : ResourceKind) (cellId : Nat)
    (store : Store effectLayout) (law : DeclaredCellLaw kind cellId store)
    (account : ResourceId .account) (asset : Digest) :
    store (StateKey.accountBalance account asset).address = none := by
  by_contra present
  exact law _ (DFinsupp.mem_support_toFun _ _ |>.mpr present)

def PresentLaw {α : Type} (law : α → Prop) : Option α → Prop
  | none => False
  | some value => law value

instance presentLawDecidable {α : Type} (law : α → Prop) [∀ value, Decidable (law value)]
    (value : Option α) : Decidable (PresentLaw law value) := by
  cases value <;> unfold PresentLaw <;> infer_instance

/-! ### Hyperdocument content: one document per cell -/

/-- The document a content record belongs to, where the record names one.
Element-owned fields and their conflicts are located through the element. -/
def recordDocument? : (space : Hyperdocument.Namespace) → Hyperdocument.Key space →
    Hyperdocument.Value space → Option DocumentId
  | .documents, document, _ => some document
  | .atoms, _, record => some record.document
  | .runs, _, record => some record.document
  | .elements, _, record => some record.document
  | .fields, key, _ =>
      match key.owner with
      | .document document => some document
      | .element _ => none
  | .conflicts, _, record =>
      match record.field.owner with
      | .document document => some document
      | .element _ => none
  | .links, _, record => some record.sourceDocument
  | .transclusions, _, record => some record.hostDocument
  | .marks, _, record => some record.document
  | .annotations, _, record => some record.document
  | .blinding, _, _ => none

/-- The document named by the record at `address`, if any. -/
def documentAt (store : Store Hyperdocument.layout)
    (address : Store.Address Hyperdocument.layout) : Option DocumentId :=
  (store address).bind (recordDocument? address.1 address.2)

/-- A content cell holds one document: every record that names a document
names the same one (the retired content page's `Entry.LocalTo`, over every
namespace). -/
def ContentLaw (store : Store Hyperdocument.layout) : Prop :=
  ∀ left ∈ store.support, ∀ right ∈ store.support,
    documentAt store left = none ∨ documentAt store right = none ∨
      documentAt store left = documentAt store right

instance contentLawDecidable (store : Store Hyperdocument.layout) :
    Decidable (ContentLaw store) := by
  unfold ContentLaw
  infer_instance

/-! ### Hyperdocument event history: this domain's well-formed, addressed events -/

local instance eventWellFormedDecidable (event : CausalVersionDag.EventPreimage) :
    Decidable event.WellFormed :=
  decidable_of_iff
    (event.parentFrontier.Pairwise (fun left right => left.value < right.value) ∧
      event.parentFrontier.Nodup)
    ⟨fun valid => ⟨valid.1, valid.2⟩,
      fun valid => ⟨valid.parentFrontierCanonical, valid.parentFrontierUnique⟩⟩

/-- One recorded event is valid in this deployment: it names this deployment's
history domain, its parent frontier is canonical, and its key is the derived
event address of its causal preimage. -/
def EventValid (deployment : Deployment) (key : VersionEventId) :
    Option VersionEventRecord → Prop
  | none => True
  | some record =>
      record.historyDomain = deployment.domain ∧ record.CausallyWellFormed ∧
        key.digest = HyperdocumentCell.eventScheme.address record.toCausalPreimage

instance eventValidDecidable (deployment : Deployment) (key : VersionEventId)
    (record : Option VersionEventRecord) : Decidable (EventValid deployment key record) := by
  cases record <;> unfold EventValid <;> infer_instance

/-- The event-log law: every recorded event is valid here, and all events are
of one document (the retired event page's scope). -/
def EventHistoryLaw (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout) : Prop :=
  (∀ address ∈ store.support, EventValid deployment address.2 (store address)) ∧
    ∀ left ∈ store.support, ∀ right ∈ store.support,
      (store left).map VersionEventRecord.document = (store right).map VersionEventRecord.document

instance eventHistoryLawDecidable (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout) :
    Decidable (EventHistoryLaw deployment store) := by
  unfold EventHistoryLaw
  infer_instance

/-- **The domain restoration (S3 decision 1).**  An event record naming any
other history domain cannot sit in this deployment's event log. -/
theorem foreign_domain_event_refused (deployment : Deployment)
    (store : Store Kernel.HyperdocumentEventLog.Sparse.layout)
    (address : Store.Address Kernel.HyperdocumentEventLog.Sparse.layout) (record : VersionEventRecord)
    (present : store address = some record) (foreign : record.historyDomain ≠ deployment.domain) :
    ¬ EventHistoryLaw deployment store := by
  intro law
  have valid := law.1 address (DFinsupp.mem_support_toFun _ _ |>.mpr (by rw [present]; intro same; cases same))
  rw [present] at valid
  exact foreign valid.1

/-- Satisfiable pole: the empty event log is lawful in every deployment. -/
theorem empty_event_history_lawful (deployment : Deployment) :
    EventHistoryLaw deployment 0 := by
  constructor <;> intro address member <;> simp at member

/-- Semantic identity of the source-owned loaded/final law. -/
def logicalLawVersion : List UInt8 :=
  "DREGG.REGISTRY.LOADED-AND-FINAL.STORE-CELLS/v7".toUTF8.toList

/-- Checked both on the loaded cell and on the ACTUAL final joint post, after
all effects have composed. Local candidate validity alone does not imply this. -/
def LogicalLaw (deployment : Deployment) (cellId : Nat) :
    (kind : Kind) → Store (layout kind) → Prop
  | .declaredObject, state => DeclaredCellLaw .object cellId state
  | .accountMetadata, state => DeclaredCellLaw .account cellId state
  | .declaredProgram, state => DeclaredCellLaw .program cellId state
  | .content, state => ContentLaw state
  | .eventHistory, state => EventHistoryLaw deployment state
  | .authority, _ => cellId = deployment.authorityCellId
  | .resourceBook, state => cellId = deployment.resourceBookId ∧
      (CanonicalResourcePageMaterializer.bookAt state).isSome = true ∧
      (CanonicalResourceKernel.logicalBook state).AccountSupported
  | .policySource, state => PresentLaw (PolicySourceCell.SourceValid deployment.domain cellId)
      (PolicySourceCell.recordAt state)
  | .pay, state => cellId = Kernel.PayCell.physicalId deployment.domain ∧ Kernel.PayCell.Law state
  | .stream, state => StreamCell.StreamLaw state
  | .nockProgram, state => PresentLaw (NockProgramCodec.CellValid deployment.domain cellId)
      (NockProgramCodec.programAt state)
  | .clock, state => cellId = Kernel.ClockCell.physicalId deployment.domain ∧
      Kernel.ClockCell.Law state

instance logicalLawDecidable (deployment : Deployment) (cellId : Nat)
    (kind : Kind) (state : Store (layout kind)) :
    Decidable (LogicalLaw deployment cellId kind state) := by
  cases kind <;> unfold LogicalLaw <;> infer_instance

def CellLaw (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Prop :=
  deployment.Valid ∧ LogicalLaw deployment cellId cell.kind cell.payload.logical

instance cellLawDecidable (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    Decidable (CellLaw deployment cellId cell) := by
  unfold CellLaw
  infer_instance

def cellCheck (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Bool :=
  decide (CellLaw deployment cellId cell)

@[simp] theorem cellCheck_iff (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    cellCheck deployment cellId cell = true ↔ CellLaw deployment cellId cell := by
  simp [cellCheck]

/-- The final-state admission uses the same fixed logical law as loaded-state
admission. A family must run this on the composed joint post, not cache a local
candidate's Boolean. The role is selected from the actual old packed cell. -/
def postStateCheck (deployment : Deployment) (cellId : Nat) (kind : Kind)
    (state : Store (layout kind)) : Bool :=
  decide (deployment.Valid ∧ LogicalLaw deployment cellId kind state)

@[simp] theorem postStateCheck_iff (deployment : Deployment) (cellId : Nat) (kind : Kind)
    (state : Store (layout kind)) :
    postStateCheck deployment cellId kind state = true ↔
      deployment.Valid ∧ LogicalLaw deployment cellId kind state := by
  simp [postStateCheck]

def FinalPostLaw (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Prop :=
  before.kind = after.kind ∧ CellLaw deployment cellId before ∧ CellLaw deployment cellId after ∧
    (before.kind = .policySource ∨ before.kind = .nockProgram →
      PackedCell.bytes registry before = PackedCell.bytes registry after)

instance finalPostLawDecidable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Decidable (FinalPostLaw deployment cellId before after) := by
  unfold FinalPostLaw
  infer_instance

/-- Neutral content genesis is an empty document cell, holding at most its
hiding key: the cell's identifier is the new document's identity.  Historical provenance, authority grants, Book
balances and policy sources are generated by their semantic controllers, never
injected as raw user initial payloads. -/
def UserShape : (kind : Kind) → Store (layout kind) → Prop
  | .declaredObject, _ | .accountMetadata, _ | .declaredProgram, _ => True
  -- Empty but for the owner-derived blinding (K-NARROW-HIDE).
  | .content, state => ∀ address ∈ state.support, address = ⟨.blinding, ()⟩
  | .stream, state => state.support = ∅
  | .nockProgram, state => PresentLaw NockProgramCodec.Admissible (NockProgramCodec.programAt state)
  | .eventHistory, _ | .authority, _ | .resourceBook, _ | .policySource, _ | .pay, _ | .clock, _ => False

instance userShapeDecidable (kind : Kind) (state : Store (layout kind)) :
    Decidable (UserShape kind state) := by
  cases kind <;> unfold UserShape <;> infer_instance

def UserInitial (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Prop :=
  CellLaw deployment cellId cell ∧ UserShape cell.kind cell.payload.logical

instance userInitialDecidable (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    Decidable (UserInitial deployment cellId cell) := by
  unfold UserInitial
  infer_instance

def userInitialCheck (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Bool :=
  decide (UserInitial deployment cellId cell)

@[simp] theorem userInitialCheck_iff (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) :
    userInitialCheck deployment cellId cell = true ↔ UserInitial deployment cellId cell := by
  simp [userInitialCheck]

def BirthsAdmissible (deployment : Deployment) (descriptor : ResourceBirth.Descriptor registry) : Prop :=
  ∀ item ∈ descriptor.births, UserInitial deployment item.create.cellId item.create.cell

instance birthsAdmissibleDecidable (deployment : Deployment) (descriptor : ResourceBirth.Descriptor registry) :
    Decidable (BirthsAdmissible deployment descriptor) := by unfold BirthsAdmissible; infer_instance

/-- The shared layout is not authority to select another role's family.
Object requests cannot select account metadata with the same id. -/
def selectDeclared (deployment : Deployment) (cellId : Nat) (requested : ResourceKind)
    (cell : PackedCell registry) : Option (Materialized DeclaredEffectCell.materializer) :=
  if CellLaw deployment cellId cell then
    match requested, cell with
    | .object, ⟨.declaredObject, payload⟩ => some payload
    | .account, ⟨.accountMetadata, payload⟩ => some payload
    | .program, ⟨.declaredProgram, payload⟩ => some payload
    | _, _ => none
  else none

theorem object_cannot_select_account (deployment : Deployment) (cellId : Nat)
    (payload : Materialized DeclaredEffectCell.materializer) :
    selectDeclared deployment cellId .object ⟨.accountMetadata, payload⟩ = none := by
  unfold selectDeclared
  split <;> rfl

theorem book_identity_is_pinned (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (valid : CellLaw deployment cellId ⟨.resourceBook, payload⟩) :
    cellId = deployment.resourceBookId := valid.2.1

/-- The one authority cell lives at the deployment's pinned identifier. -/
theorem authority_identity_is_pinned (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityCell.materializer)
    (valid : CellLaw deployment cellId ⟨.authority, payload⟩) :
    cellId = deployment.authorityCellId := valid.2

/-- Loaded and final canonical Books cannot carry balances for unregistered
accounts. The lossless wire codec deliberately imposes no such semantic law. -/
theorem book_accountSupported (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (valid : CellLaw deployment cellId ⟨.resourceBook, payload⟩) :
    (CanonicalResourceKernel.logicalBook payload.logical).AccountSupported := valid.2.2.2

theorem hidden_book_refused (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (account asset : Nat)
    (absent : account ∉ (CanonicalResourceKernel.logicalBook payload.logical).accounts)
    (hidden : (CanonicalResourceKernel.logicalBook payload.logical).balance account asset ≠ 0) :
    ¬ CellLaw deployment cellId ⟨.resourceBook, payload⟩ := by
  intro valid
  exact hidden ((book_accountSupported _ _ _ valid).balance_zero absent asset)

theorem no_user_book_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer) :
    ¬UserInitial deployment cellId ⟨.resourceBook, payload⟩ := fun admitted => admitted.2

theorem no_user_authority_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityCell.materializer) :
    ¬UserInitial deployment cellId ⟨.authority, payload⟩ := fun admitted => admitted.2

theorem no_user_event_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized HyperdocumentCell.eventMaterializer) :
    ¬UserInitial deployment cellId ⟨.eventHistory, payload⟩ := fun admitted => admitted.2

/-- The metadata identity is exactly the account registered by the existing
source-derived resource batch; it is not an independently funded Book. -/
theorem account_metadata_registered
    (descriptor : ResourceBirth.Descriptor registry) (item : ResourceBirth.BirthItem registry)
    (member : item ∈ descriptor.births)
    (actualKind : item.create.cell.kind = .accountMetadata)
    (kindBound : item.resourceKind = resourceKindOf item.create.cell.kind) :
    item.create.cellId ∈ descriptor.registeredAccounts := by
  have account : item.resourceKind = .account := by
    simpa [actualKind, resourceKindOf] using kindBound
  simp only [ResourceBirth.Descriptor.registeredAccounts, List.mem_filterMap]
  exact ⟨item, member, by simp [account]⟩

/-! ## Immutable policy source cells and same-directory source resolution -/

def policySourceCell (record : CanonicalPolicyAdmission.PolicyRecord) : PackedCell registry :=
  ⟨.policySource, materialize PolicySourceCell.materializer
    (PolicySourceCell.stateOfOption (some record))⟩

def policySourceCreate (domain : Digest) (record : CanonicalPolicyAdmission.PolicyRecord) :
    CreateRequest (CellId := Nat) registry where
  cellId := PolicySourceCell.physicalId domain (PolicyRecordCodec.digest record)
  expectedPreRoot := CellSlot.root registry .absent
  cell := policySourceCell record

theorem policySourceCreate_cell_law (deployment : Deployment)
    (record : CanonicalPolicyAdmission.PolicyRecord) (valid : deployment.Valid)
    (domainExact : record.domain = deployment.domain) :
    CellLaw deployment (policySourceCreate deployment.domain record).cellId
      (policySourceCreate deployment.domain record).cell := by
  change deployment.Valid ∧ PolicySourceCell.SourceValid deployment.domain
    (PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record)) record
  exact ⟨valid, domainExact, rfl⟩

/-- Only records returned by the fixed initial-policy checker are used by the
birth receiver. This helper derives bytes and identifiers; lifecycle admission
still checks actual absence, permanent freshness and duplicate identifiers. -/
def initialSourceCreates (domain : Digest) (records : List CanonicalPolicyAdmission.PolicyRecord) :
    List (CreateRequest (CellId := Nat) registry) := records.map (policySourceCreate domain)

theorem initialSourceCreates_ids {F : Type} [Field F] {domain : Digest}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {initials : List ResourceBirth.InitialPolicy}
    (checked : PolicySourceCell.CheckedInitials domain profile initials) :
    (initialSourceCreates domain checked.records).map CreateRequest.cellId =
      PolicySourceCell.initialIds domain initials := by
  simpa [initialSourceCreates, policySourceCreate, List.map_map] using checked.ids_exact

structure LoadedPolicySource (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) where
  payload : Materialized PolicySourceCell.materializer
  present : directory.slots (PolicySourceCell.physicalId domain address) =
    .present ⟨.policySource, payload⟩
  record : CanonicalPolicyAdmission.PolicyRecord
  recordExact : PolicySourceCell.recordAt payload.logical = some record
  domainExact : record.domain = domain
  addressExact : PolicyRecordCodec.digest record = address

def LoadedPolicySource.cell {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PackedCell registry := ⟨.policySource, loaded.payload⟩

def LoadedPolicySource.cellId {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (_loaded : LoadedPolicySource domain directory address) : Nat :=
  PolicySourceCell.physicalId domain address

def LoadedPolicySource.canonicalBytes {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) : List UInt8 :=
  PolicyRecordCodec.encode loaded.record

/-- The guard is over the actual outer physical cell, not the content digest
or the singleton payload's native materializer root. -/
def LoadedPolicySource.readGuard {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) : Nat × Digest :=
  (loaded.cellId, ResourceBirthCodec.physicalRoot (.live loaded.cell))

theorem LoadedPolicySource.lifecycle_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    ResourceBirthCodec.LifecycleImage.view registry directory loaded.cellId = .live loaded.cell :=
  (ResourceBirthCodec.LifecycleImage.view_live_iff registry directory loaded.cellId loaded.cell).mpr
    loaded.present

theorem LoadedPolicySource.readGuard_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    loaded.readGuard.2 = ResourceBirthCodec.rootBytes
      (ResourceBirthCodec.LifecycleImage.bytes registry
        (ResourceBirthCodec.LifecycleImage.view registry directory loaded.cellId)) := by
  rw [loaded.lifecycle_exact]
  rfl

theorem LoadedPolicySource.cell_exact {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    loaded.cell = policySourceCell loaded.record := by
  have stateExact := PolicySourceCell.state_ext loaded.payload.logical
  rw [loaded.recordExact] at stateExact
  exact congrArg (fun (payload : Materialized PolicySourceCell.materializer) =>
      (⟨.policySource, payload⟩ : PackedCell registry))
    (Materialized.ext stateExact)

theorem LoadedPolicySource.record_of_present {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address)
    (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots loaded.cellId = .present (policySourceCell record)) :
    loaded.record = record := by
  have sameCell : loaded.cell = policySourceCell record :=
    CellSlot.present.inj (loaded.present.symm.trans present)
  have sameRecord := congrArg (fun (cell : PackedCell registry) =>
    match cell with
    | ⟨.policySource, payload⟩ => PolicySourceCell.recordAt payload.logical
    | _ => none) sameCell
  change PolicySourceCell.recordAt loaded.payload.logical = some record at sameRecord
  rw [loaded.recordExact] at sameRecord
  exact Option.some.inj sameRecord

theorem LoadedPolicySource.bytes_decode {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PolicyRecordCodec.decode loaded.canonicalBytes = some loaded.record :=
  PolicyRecordCodec.decode_encode loaded.record

theorem LoadedPolicySource.bytes_digest {domain : Digest} {directory : Directory Nat registry}
    {address : Digest} (loaded : LoadedPolicySource domain directory address) :
    PolicyRecordCodec.hashBytes loaded.canonicalBytes = address := loaded.addressExact

def loadPolicySource (domain : Digest) (directory : Directory Nat registry) (address : Digest) :
    Option (LoadedPolicySource domain directory address) :=
  match present : directory.slots (PolicySourceCell.physicalId domain address) with
  | .present ⟨.policySource, payload⟩ =>
      match found : PolicySourceCell.recordAt payload.logical with
      | none => none
      | some record =>
          if valid : record.domain = domain ∧ PolicyRecordCodec.digest record = address then
            some ⟨payload, present, record, found, valid.1, valid.2⟩
          else none
  | _ => none

def fetchPolicySource (domain : Digest) (directory : Directory Nat registry) (address : Digest) :
    Option (List UInt8) :=
  (loadPolicySource domain directory address).map LoadedPolicySource.canonicalBytes

theorem fetchPolicySource_exact (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (domainExact : record.domain = domain)
    (addressExact : PolicyRecordCodec.digest record = address) :
    fetchPolicySource domain directory address = some (PolicyRecordCodec.encode record) := by
  unfold fetchPolicySource loadPolicySource
  split
  next payload found =>
    have actual := congrArg (fun (slot : CellSlot registry) =>
      match slot with
      | .present ⟨.policySource, payload⟩ => PolicySourceCell.recordAt payload.logical
      | _ => none) (found.symm.trans present)
    change PolicySourceCell.recordAt payload.logical = some record at actual
    split
    next absent => simp [actual] at absent
    next selected selectedAt =>
      have same : selected = record := Option.some.inj (selectedAt.symm.trans actual)
      subst selected
      simp [domainExact, addressExact, LoadedPolicySource.canonicalBytes]
  next => simp_all [policySourceCell]

theorem missing_policy_source_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest)
    (missing : directory.slots (PolicySourceCell.physicalId domain address) = .absent) :
    fetchPolicySource domain directory address = none := by
  simp [fetchPolicySource, loadPolicySource, missing]

theorem wrong_policy_source_kind_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (cell : PackedCell registry)
    (present : directory.slots (PolicySourceCell.physicalId domain address) = .present cell)
    (wrongKind : cell.kind ≠ .policySource) :
    fetchPolicySource domain directory address = none := by
  rcases cell with ⟨kind, payload⟩
  cases kind <;> simp_all [fetchPolicySource, loadPolicySource]

theorem wrong_policy_source_domain_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (wrongDomain : record.domain ≠ domain) :
    fetchPolicySource domain directory address = none := by
  cases result : loadPolicySource domain directory address with
  | none => simp [fetchPolicySource, result]
  | some loaded =>
      have same := loaded.record_of_present record present
      have domainExact := loaded.domainExact
      rw [same] at domainExact
      exact False.elim (wrongDomain domainExact)

theorem wrong_policy_source_digest_refused (domain : Digest) (directory : Directory Nat registry)
    (address : Digest) (record : CanonicalPolicyAdmission.PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain address) =
      .present (policySourceCell record))
    (wrongDigest : PolicyRecordCodec.digest record ≠ address) :
    fetchPolicySource domain directory address = none := by
  cases result : loadPolicySource domain directory address with
  | none => simp [fetchPolicySource, result]
  | some loaded =>
      have same := loaded.record_of_present record present
      have addressExact := loaded.addressExact
      rw [same] at addressExact
      exact False.elim (wrongDigest addressExact)

theorem policy_source_no_user_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized PolicySourceCell.materializer) :
    ¬UserInitial deployment cellId ⟨.policySource, payload⟩ := fun admitted => admitted.2

theorem policy_source_final_bytes_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (source : before.kind = .policySource)
    (valid : FinalPostLaw deployment cellId before after) :
    PackedCell.bytes registry before = PackedCell.bytes registry after := valid.2.2.2 (Or.inl source)

theorem policy_source_final_state_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (source : before.kind = .policySource)
    (valid : FinalPostLaw deployment cellId before after) : before = after := by
  have bytesExact : cellCodec.encode before = cellCodec.encode after :=
    policy_source_final_bytes_immutable deployment cellId before after source valid
  have same := congrArg cellCodec.decode bytesExact
  rw [cellCodec.decode_encode, cellCodec.decode_encode] at same
  exact Option.some.inj same

theorem policy_source_occupied_refused (domain : Digest) (directory : Directory Nat registry)
    (record : CanonicalPolicyAdmission.PolicyRecord) (occupant : PackedCell registry)
    (occupied : directory.slots (policySourceCreate domain record).cellId = .present occupant) :
    CellRegistry.create registry directory (policySourceCreate domain record) =
      .error .duplicateCreate := by
  simp [CellRegistry.create, occupied]

theorem policy_source_retired_refused (domain : Digest) (directory : Directory Nat registry)
    (record : CanonicalPolicyAdmission.PolicyRecord)
    (absent : directory.slots (policySourceCreate domain record).cellId = .absent)
    (used : (policySourceCreate domain record).cellId ∈ directory.used) :
    CellRegistry.create registry directory (policySourceCreate domain record) =
      .error .retiredIdentifier := by
  simp [CellRegistry.create, absent, used]

theorem policy_source_identifier_collision_refused (domain : Digest)
    (directory : Directory Nat registry) (left right : CanonicalPolicyAdmission.PolicyRecord)
    (collision : (policySourceCreate domain left).cellId =
      (policySourceCreate domain right).cellId) :
    CellRegistry.create registry
      (Directory.insert registry directory (policySourceCreate domain left).cellId
        (policySourceCell left))
      (policySourceCreate domain right) = .error .duplicateCreate := by
  apply policy_source_occupied_refused domain _ right (policySourceCell left)
  rw [collision]
  exact Directory.insert_slot registry directory _ _

/-! ## Nock program cells: content-addressed, immutable, born by friends

A program cell is born through the ordinary resource birth (its creator's law,
its creator's owner grant), never by a special capability. Its identifier is its
content address, so the same record born twice meets an occupied identifier
(`program_occupied_refused`); a different ABI over the same jam is a different
program at a different identifier. -/

def programCell (program : NockProgramCodec.Program) : PackedCell registry :=
  ⟨.nockProgram, materialize NockProgramCodec.materializer
    (NockProgramCodec.stateOfOption (some program))⟩

def programCellId (domain : Digest) (program : NockProgramCodec.Program) : Nat :=
  NockProgramCodec.physicalId domain (NockProgramCodec.programId program)

def programCreate (domain : Digest) (program : NockProgramCodec.Program) :
    CreateRequest (CellId := Nat) registry where
  cellId := programCellId domain program
  expectedPreRoot := CellSlot.root registry .absent
  cell := programCell program

/-- The program a packed cell holds, if it is a program cell. -/
def cellProgram : PackedCell registry → Option NockProgramCodec.Program
  | ⟨.nockProgram, payload⟩ => NockProgramCodec.programAt payload.logical
  | _ => none

@[simp] theorem cellProgram_programCell (program : NockProgramCodec.Program) :
    cellProgram (programCell program) = some program := by
  simp [cellProgram, programCell]

/-- The program at `id`'s address in this directory, checked against the address. -/
def loadProgram (domain : Digest) (directory : Directory Nat registry) (id : Digest) :
    Option NockProgramCodec.Program :=
  match directory.slots (NockProgramCodec.physicalId domain id) with
  | .present cell =>
      match cellProgram cell with
      | some program => if NockProgramCodec.programId program = id then some program else none
      | none => none
  | _ => none

theorem loadProgram_present (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program)
    (present : directory.slots (programCellId domain program) = .present (programCell program)) :
    loadProgram domain directory (NockProgramCodec.programId program) = some program := by
  unfold loadProgram
  rw [show NockProgramCodec.physicalId domain (NockProgramCodec.programId program) =
    programCellId domain program from rfl, present]
  simp

theorem loadProgram_programId {domain : Digest} {directory : Directory Nat registry}
    {id : Digest} {program : NockProgramCodec.Program}
    (loaded : loadProgram domain directory id = some program) :
    NockProgramCodec.programId program = id := by
  unfold loadProgram at loaded
  split at loaded
  · split at loaded
    · split at loaded
      · rename_i same
        cases loaded
        exact same
      · cases loaded
    · cases loaded
  · cases loaded

theorem missing_program_refused (domain : Digest) (directory : Directory Nat registry)
    (id : Digest) (missing : directory.slots (NockProgramCodec.physicalId domain id) = .absent) :
    loadProgram domain directory id = none := by
  simp [loadProgram, missing]

/-- Every library a program names is a program cell present here. -/
def librariesPresent (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) : Bool :=
  program.abi.libraries.all fun library => (loadProgram domain directory library).isSome

/-- Every program born by `descriptor` names only libraries already present. -/
def birthLibrariesPresent (domain : Digest) (directory : Directory Nat registry)
    (descriptor : ResourceBirth.Descriptor registry) : Bool :=
  descriptor.births.all fun item =>
    match cellProgram item.create.cell with
    | none => true
    | some program => librariesPresent domain directory program

theorem missing_library_refused (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) (library : Digest)
    (named : library ∈ program.abi.libraries)
    (missing : loadProgram domain directory library = none) :
    librariesPresent domain directory program = false := by
  unfold librariesPresent
  rw [List.all_eq_false]
  exact ⟨library, named, by simp [missing]⟩

theorem birth_missing_library_refused (domain : Digest) (directory : Directory Nat registry)
    (descriptor : ResourceBirth.Descriptor registry) (item : ResourceBirth.BirthItem registry)
    (member : item ∈ descriptor.births) (program : NockProgramCodec.Program)
    (holds : cellProgram item.create.cell = some program)
    (missing : librariesPresent domain directory program = false) :
    birthLibrariesPresent domain directory descriptor = false := by
  unfold birthLibrariesPresent
  rw [List.all_eq_false]
  exact ⟨item, member, by simp [holds, missing]⟩

/-- A friend may birth exactly an admissible program at its content address. -/
theorem program_user_initial_iff (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program) :
    UserInitial deployment cellId (programCell program) ↔
      deployment.Valid ∧ cellId = programCellId deployment.domain program ∧
        NockProgramCodec.Admissible program := by
  simp [UserInitial, CellLaw, LogicalLaw, UserShape, programCell, PresentLaw,
    NockProgramCodec.CellValid, programCellId, and_assoc]

theorem nonCanonical_birth_refused (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program)
    (bad : Noun.canonical program.jam = false) :
    ¬ UserInitial deployment cellId (programCell program) := by
  rw [program_user_initial_iff]
  rintro ⟨_, _, admitted, _⟩
  rw [bad] at admitted
  cases admitted

theorem wrong_address_birth_refused (deployment : Deployment) (cellId : Nat)
    (program : NockProgramCodec.Program)
    (elsewhere : cellId ≠ programCellId deployment.domain program) :
    ¬ UserInitial deployment cellId (programCell program) := by
  rw [program_user_initial_iff]
  rintro ⟨_, same, _⟩
  exact elsewhere same

theorem program_occupied_refused (domain : Digest) (directory : Directory Nat registry)
    (program : NockProgramCodec.Program) (occupant : PackedCell registry)
    (occupied : directory.slots (programCreate domain program).cellId = .present occupant) :
    CellRegistry.create registry directory (programCreate domain program) =
      .error .duplicateCreate := by
  simp [CellRegistry.create, occupied]

theorem nock_program_final_state_immutable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) (program : before.kind = .nockProgram)
    (valid : FinalPostLaw deployment cellId before after) : before = after := by
  have bytesExact : cellCodec.encode before = cellCodec.encode after :=
    valid.2.2.2 (Or.inr program)
  have same := congrArg cellCodec.decode bytesExact
  rw [cellCodec.decode_encode, cellCodec.decode_encode] at same
  exact Option.some.inj same

namespace Witness

def deployment : Deployment := ⟨⟨42⟩, 1, 2, 3⟩

/-- Account metadata with one field of its own identity. -/
def payload : Materialized DeclaredEffectCell.materializer :=
  materialize DeclaredEffectCell.materializer
    (StoreCodec.fromEntries [⟨(StateKey.objectField ⟨10⟩ ⟨1⟩).address, (17 : Int)⟩])

def account : PackedCell registry := ⟨.accountMetadata, payload⟩

theorem user_account_inhabited : UserInitial deployment 10 account := by decide

theorem account_dispatch_inhabited :
    (selectDeclared deployment 10 .account account).isSome = true := by decide

theorem object_dispatch_refused : selectDeclared deployment 10 .object account = none :=
  object_cannot_select_account deployment 10 payload

/-- Neutral content genesis: the empty document cell. -/
def emptyContent : PackedCell registry :=
  ⟨.content, materialize HyperdocumentCell.contentMaterializer 0⟩

theorem user_content_inhabited : UserInitial deployment 11 emptyContent := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · intro left member
    exact ((DFinsupp.mem_support_toFun _ _).mp member rfl).elim
  · intro address member
    exact ((DFinsupp.mem_support_toFun _ _).mp member rfl).elim

end Witness

end Minidregg.Compiler.CanonicalCellRegistry

/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.DeclaredCellLaw.no_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.DeclaredCellLaw.no_balance
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.foreign_domain_event_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.foreign_domain_event_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.empty_event_history_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.empty_event_history_lawful
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.authority_identity_is_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.authority_identity_is_pinned
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.user_content_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.user_content_inhabited
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.program_user_initial_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.program_user_initial_iff
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.nonCanonical_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.nonCanonical_birth_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.missing_library_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.missing_library_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.birth_missing_library_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.birth_missing_library_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.loadProgram_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.loadProgram_present
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.program_occupied_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.program_occupied_refused
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.nock_program_final_state_immutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.nock_program_final_state_immutable
