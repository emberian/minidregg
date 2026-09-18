/-
# Compiler.CanonicalCellRegistry — one executable receiving registry

This is the production union of the existing bounded content/event/authority
and declared-effect page materializers, with the canonical resource Book and
authority catalogue. The old partial registries remain scoped exhibits; new
birth, policy, authority-domain and native receivers select this registry.

Kinds are semantic roles, even when their physical page schema is shared.
Object/program/account-metadata roles have source-owned field laws and typed
dispatch. No such role may carry an `accountBalance` field: only the domain's
configured resource Book owns money. Account metadata uses the existing page
schema, not another ledger; its created identity is the same account registered
by `ResourceBirth.Descriptor.resourceBatch`.

`CellLaw` is an invariant for loaded and FINAL post cells, not only a birth
check. `UserInitial` further refuses internal authority, Book and event-history
payloads. Those cells are produced by their source-owned semantic lowerings.
The registry supplies no public raw-state installation endpoint.
-/
import Compiler.BoundedPageExtensionCatalog
import Compiler.DeclaredEffectPageMaterializer
import Compiler.CredentialAuthorityDomain
import Compiler.CanonicalResourcePageMaterializer
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.CanonicalCellRegistry

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration

set_option autoImplicit false

inductive Kind where
  | content
  | eventHistory
  | authorityShard
  | declaredObject
  | resourceBook
  | authorityCatalogue
  | accountMetadata
  | declaredProgram
  deriving DecidableEq, Repr

def Kind.all : List Kind :=
  [.content, .eventHistory, .authorityShard, .declaredObject,
    .resourceBook, .authorityCatalogue, .accountMetadata, .declaredProgram]

/-- Existing bounded-page tags 1/2/3 and effect-page tag 5 are retained.
Tag 4 remains unassigned. New tags and schema refs are deployment pins. -/
def Kind.tag : Kind → UInt8
  | .content => 1
  | .eventHistory => 2
  | .authorityShard => 3
  | .declaredObject => 5
  | .resourceBook => 6
  | .authorityCatalogue => 7
  | .accountMetadata => 8
  | .declaredProgram => 9

def kindAtTag : UInt8 → Option Kind
  | 1 => some .content
  | 2 => some .eventHistory
  | 3 => some .authorityShard
  | 5 => some .declaredObject
  | 6 => some .resourceBook
  | 7 => some .authorityCatalogue
  | 8 => some .accountMetadata
  | 9 => some .declaredProgram
  | _ => none

@[simp] theorem kindAtTag_tag (kind : Kind) : kindAtTag kind.tag = some kind := by
  cases kind <;> rfl

def schemaRef : Kind → SchemaRef
  | .content => ⟨⟨91001⟩, 1⟩
  | .eventHistory => ⟨⟨91002⟩, 1⟩
  | .authorityShard => ⟨⟨91003⟩, 2⟩
  | .declaredObject => ⟨⟨91004⟩, 1⟩
  | .resourceBook => ⟨⟨91005⟩, 2⟩
  | .authorityCatalogue => ⟨⟨91006⟩, 1⟩
  | .accountMetadata => ⟨⟨91007⟩, 1⟩
  | .declaredProgram => ⟨⟨91008⟩, 1⟩

theorem schemaRef_injective : Function.Injective schemaRef := by
  intro left right same
  cases left <;> cases right <;> simp [schemaRef] at same ⊢

def schema : Kind → CellState.Schema.{0, 0, 0, 0}
  | .content => HyperdocumentContentPageMaterializer.schema
  | .eventHistory => HyperdocumentEventPageMaterializer.schema
  | .authorityShard => CredentialAuthorityPageMaterializer.schema
  | .declaredObject => DeclaredEffectPageMaterializer.schema
  | .resourceBook => CanonicalResourceKernel.schema
  | .authorityCatalogue => CredentialAuthorityDomain.catalogueSchema
  | .accountMetadata => DeclaredEffectPageMaterializer.schema
  | .declaredProgram => DeclaredEffectPageMaterializer.schema

instance fieldDecidableEq : (kind : Kind) → DecidableEq (schema kind).Field
  | .content => inferInstanceAs (DecidableEq HyperdocumentContentPageMaterializer.schema.Field)
  | .eventHistory => inferInstanceAs (DecidableEq HyperdocumentEventPageMaterializer.schema.Field)
  | .authorityShard => inferInstanceAs (DecidableEq CredentialAuthorityPageMaterializer.schema.Field)
  | .declaredObject => inferInstanceAs (DecidableEq DeclaredEffectPageMaterializer.schema.Field)
  | .resourceBook => inferInstanceAs (DecidableEq CanonicalResourceKernel.Field)
  | .authorityCatalogue => inferInstanceAs (DecidableEq CredentialAuthorityDomain.catalogueSchema.Field)
  | .accountMetadata => inferInstanceAs (DecidableEq DeclaredEffectPageMaterializer.schema.Field)
  | .declaredProgram => inferInstanceAs (DecidableEq DeclaredEffectPageMaterializer.schema.Field)

instance resourceDecidableEq : (kind : Kind) → DecidableEq (schema kind).Resource
  | .content => inferInstanceAs (DecidableEq Empty)
  | .eventHistory => inferInstanceAs (DecidableEq Empty)
  | .authorityShard => inferInstanceAs (DecidableEq Empty)
  | .declaredObject => inferInstanceAs (DecidableEq Empty)
  | .resourceBook => inferInstanceAs (DecidableEq Empty)
  | .authorityCatalogue => inferInstanceAs (DecidableEq Empty)
  | .accountMetadata => inferInstanceAs (DecidableEq Empty)
  | .declaredProgram => inferInstanceAs (DecidableEq Empty)

def materializer : (kind : Kind) → Materializer (schema kind) Digest
  | .content => HyperdocumentContentPageMaterializer.materializer
  | .eventHistory => HyperdocumentEventPageMaterializer.materializer
  | .authorityShard => CredentialAuthorityPageMaterializer.materializer
  | .declaredObject => DeclaredEffectPageMaterializer.materializer
  | .resourceBook => CanonicalResourcePageMaterializer.materializer
  | .authorityCatalogue => CredentialAuthorityDomain.catalogueMaterializer
  | .accountMetadata => DeclaredEffectPageMaterializer.materializer
  | .declaredProgram => DeclaredEffectPageMaterializer.materializer

def registry : TypeRegistry Digest where
  Kind := Kind
  tag := Kind.tag
  kindAtTag := kindAtTag
  kindAtTag_tag := kindAtTag_tag
  schemaRef := schemaRef
  schemaRef_injective := schemaRef_injective
  schema := schema
  materializer := materializer
  rootBytes := ResourceBirthCodec.rootBytes

instance registryKindDecidableEq : DecidableEq registry.Kind :=
  inferInstanceAs (DecidableEq Kind)

instance registryFieldDecidableEq (kind : registry.Kind) :
    DecidableEq (registry.schema kind).Field := fieldDecidableEq kind

instance registryResourceDecidableEq (kind : registry.Kind) :
    DecidableEq (registry.schema kind).Resource := resourceDecidableEq kind

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
    registry.materializer .content = HyperdocumentContentPageMaterializer.materializer := rfl
@[simp] theorem registry_event_materializer :
    registry.materializer .eventHistory = HyperdocumentEventPageMaterializer.materializer := rfl
@[simp] theorem registry_authority_materializer :
    registry.materializer .authorityShard = CredentialAuthorityPageMaterializer.materializer := rfl
@[simp] theorem registry_catalogue_materializer :
    registry.materializer .authorityCatalogue = CredentialAuthorityDomain.catalogueMaterializer := rfl
@[simp] theorem registry_book_materializer :
    registry.materializer .resourceBook = CanonicalResourcePageMaterializer.materializer := rfl
@[simp] theorem registry_factory_materializer :
    registry.materializer factoryKind = DeclaredEffectPageMaterializer.materializer := rfl
@[simp] theorem registry_account_materializer :
    registry.materializer .accountMetadata = DeclaredEffectPageMaterializer.materializer := rfl
@[simp] theorem registry_program_materializer :
    registry.materializer .declaredProgram = DeclaredEffectPageMaterializer.materializer := rfl
@[simp] theorem registry_lifecycle_root :
    registry.rootBytes = ResourceBirthCodec.rootBytes := rfl

theorem retained_content_pin : schemaRef .content =
    ⟨BoundedPageExtensionCatalog.contentController.schemaId,
      BoundedPageExtensionCatalog.contentController.wireVersion⟩ := rfl
theorem retained_event_pin : schemaRef .eventHistory =
    ⟨BoundedPageExtensionCatalog.eventHistoryController.schemaId,
      BoundedPageExtensionCatalog.eventHistoryController.wireVersion⟩ := rfl
theorem retained_authority_pin : schemaRef .authorityShard =
    ⟨BoundedPageExtensionCatalog.authorityPolicyController.schemaId,
      BoundedPageExtensionCatalog.authorityPolicyController.wireVersion⟩ := rfl

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
catalogue merely because its payload has the right schema tag. -/
structure Deployment where
  domain : Digest
  factoryId : Nat
  resourceBookId : Nat
  authorityCatalogueId : Nat
  deriving DecidableEq, Repr

def Deployment.Valid (deployment : Deployment) : Prop :=
  [deployment.factoryId, deployment.resourceBookId, deployment.authorityCatalogueId].Nodup

instance deploymentValidDecidable (deployment : Deployment) : Decidable deployment.Valid := by
  unfold Deployment.Valid
  infer_instance

def Deployment.authorityAnchor (deployment : Deployment) : CredentialAuthorityDomain.Anchor :=
  ⟨deployment.domain, ⟨deployment.authorityCatalogueId⟩⟩

/-- Field constructors, not textual key names, determine role membership.
The account role's page contains metadata only; it cannot encode money. -/
def KeyAllowed (kind : ResourceKind) (cellId : Nat) : StateKey → Prop
  | .objectField object _ =>
      (kind = .object ∨ kind = .account) ∧ object.value = cellId
  | .programCode program => kind = .program ∧ program.value = cellId
  | .accountBalance _ _ => False

instance keyAllowedDecidable (kind : ResourceKind) (cellId : Nat) (key : StateKey) :
    Decidable (KeyAllowed kind cellId key) := by
  cases key <;> unfold KeyAllowed <;> infer_instance

theorem accountBalance_never_allowed (kind : ResourceKind) (cellId : Nat)
    (account : ResourceId .account) (asset : Digest) :
    ¬KeyAllowed kind cellId (.accountBalance account asset) := fun impossible => impossible

def DeclaredPageLaw (deployment : Deployment) (kind : ResourceKind)
    (cellId : Nat) (page : DeclaredEffectPageMaterializer.Page) : Prop :=
  page.effectDomain = deployment.domain ∧
    page.shardNumber = cellId % DeclaredEffectPageMaterializer.shardCount ∧
    page.Valid ∧ ∀ entry ∈ page.entries, KeyAllowed kind cellId entry.key

instance declaredPageLawDecidable (deployment : Deployment) (kind : ResourceKind)
    (cellId : Nat) (page : DeclaredEffectPageMaterializer.Page) :
    Decidable (DeclaredPageLaw deployment kind cellId page) := by
  unfold DeclaredPageLaw
  infer_instance

theorem DeclaredPageLaw.no_balance (deployment : Deployment) (kind : ResourceKind)
    (cellId : Nat) (page : DeclaredEffectPageMaterializer.Page)
    (law : DeclaredPageLaw deployment kind cellId page)
    (entry : DeclaredEffectPageMaterializer.Entry) (member : entry ∈ page.entries)
    (account : ResourceId .account) (asset : Digest) :
    entry.key ≠ .accountBalance account asset := by
  intro same
  have allowed := law.2.2.2 entry member
  rw [same] at allowed
  exact allowed

def PresentLaw {α : Type} (law : α → Prop) : Option α → Prop
  | none => False
  | some value => law value

instance presentLawDecidable {α : Type} (law : α → Prop) [∀ value, Decidable (law value)]
    (value : Option α) : Decidable (PresentLaw law value) := by
  cases value <;> unfold PresentLaw <;> infer_instance

local instance eventWellFormedDecidable (event : CausalVersionDag.EventPreimage) :
    Decidable event.WellFormed :=
  decidable_of_iff
    (event.parentFrontier.Pairwise (fun left right => left.value < right.value) ∧
      event.parentFrontier.Nodup)
    ⟨fun valid => ⟨valid.1, valid.2⟩,
      fun valid => ⟨valid.parentFrontierCanonical, valid.parentFrontierUnique⟩⟩

local instance eventEntryDecidable (page : HyperdocumentEventPageMaterializer.Page)
    (entry : HyperdocumentEventPageMaterializer.Entry) : Decidable (entry.ValidFor page) := by
  unfold HyperdocumentEventPageMaterializer.Entry.ValidFor Hyperdocument.VersionEventRecord.CausallyWellFormed
  infer_instance

local instance eventPageDecidable (page : HyperdocumentEventPageMaterializer.Page) :
    Decidable page.Valid :=
  decidable_of_iff
    ((∀ entry ∈ page.entries, entry.ValidFor page) ∧
      (page.entries.map HyperdocumentEventPageMaterializer.Entry.key).Nodup)
    ⟨fun valid => ⟨valid.1, valid.2⟩, fun valid => ⟨valid.entriesValid, valid.keysNodup⟩⟩

/-- Checked both on the loaded cell and on the ACTUAL final joint post, after
all effects have composed. Local candidate validity alone does not imply this. -/
def LogicalLaw (deployment : Deployment) (cellId : Nat) :
    (kind : Kind) → LogicalState (schema kind) → Prop
  | .declaredObject, state => PresentLaw (DeclaredPageLaw deployment .object cellId)
      (DeclaredEffectPageMaterializer.pageAt state)
  | .accountMetadata, state => PresentLaw (DeclaredPageLaw deployment .account cellId)
      (DeclaredEffectPageMaterializer.pageAt state)
  | .declaredProgram, state => PresentLaw (DeclaredPageLaw deployment .program cellId)
      (DeclaredEffectPageMaterializer.pageAt state)
  | .content, state => PresentLaw (fun page => page.contentDomain = deployment.domain ∧ page.Valid)
      (HyperdocumentContentPageMaterializer.pageAt state)
  | .eventHistory, state => PresentLaw (fun page => page.historyDomain = deployment.domain ∧ page.Valid)
      (HyperdocumentEventPageMaterializer.pageAt state)
  | .authorityShard, state => PresentLaw (fun page => page.authorityDomain = deployment.domain ∧
      page.Valid ∧ CredentialAuthorityDomain.Routed page)
      (CredentialAuthorityPageMaterializer.pageAt state)
  | .authorityCatalogue, state => cellId = deployment.authorityCatalogueId ∧
      PresentLaw (fun catalogue => catalogue.domain = deployment.domain ∧ catalogue.Valid)
        (CredentialAuthorityDomain.catalogueAt state)
  | .resourceBook, state => cellId = deployment.resourceBookId ∧
      (CanonicalResourcePageMaterializer.bookAt state).isSome = true

instance logicalLawDecidable (deployment : Deployment) (cellId : Nat)
    (kind : Kind) (state : LogicalState (schema kind)) :
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
    (state : LogicalState (schema kind)) : Bool :=
  decide (deployment.Valid ∧ LogicalLaw deployment cellId kind state)

@[simp] theorem postStateCheck_iff (deployment : Deployment) (cellId : Nat) (kind : Kind)
    (state : LogicalState (schema kind)) :
    postStateCheck deployment cellId kind state = true ↔
      deployment.Valid ∧ LogicalLaw deployment cellId kind state := by
  simp [postStateCheck]

def FinalPostLaw (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Prop :=
  before.kind = after.kind ∧ CellLaw deployment cellId before ∧ CellLaw deployment cellId after

instance finalPostLawDecidable (deployment : Deployment) (cellId : Nat)
    (before after : PackedCell registry) : Decidable (FinalPostLaw deployment cellId before after) := by
  unfold FinalPostLaw
  infer_instance

/-- Neutral content genesis names this new identity. Historical provenance,
authority grants, Book balances and catalogue references are generated by
their semantic controllers, never injected as raw user initial payloads. -/
def UserShape (cellId : Nat) : (kind : Kind) → LogicalState (schema kind) → Prop
  | .declaredObject, _ | .accountMetadata, _ | .declaredProgram, _ => True
  | .content, state => PresentLaw (fun page => page.document.digest = ⟨cellId⟩ ∧
      page.pageNumber = 0 ∧ page.entries = [])
      (HyperdocumentContentPageMaterializer.pageAt state)
  | .eventHistory, _ | .authorityShard, _ | .authorityCatalogue, _ | .resourceBook, _ => False

instance userShapeDecidable (cellId : Nat) (kind : Kind) (state : LogicalState (schema kind)) :
    Decidable (UserShape cellId kind state) := by
  cases kind <;> unfold UserShape <;> infer_instance

def UserInitial (deployment : Deployment) (cellId : Nat) (cell : PackedCell registry) : Prop :=
  CellLaw deployment cellId cell ∧ UserShape cellId cell.kind cell.payload.logical

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

/-- The shared physical page schema is not authority to select another role's
family. Object requests cannot select account metadata with the same id. -/
def selectDeclared (deployment : Deployment) (cellId : Nat) (requested : ResourceKind)
    (cell : PackedCell registry) : Option (Materialized DeclaredEffectPageMaterializer.materializer) :=
  if CellLaw deployment cellId cell then
    match requested, cell with
    | .object, ⟨.declaredObject, payload⟩ => some payload
    | .account, ⟨.accountMetadata, payload⟩ => some payload
    | .program, ⟨.declaredProgram, payload⟩ => some payload
    | _, _ => none
  else none

theorem object_cannot_select_account (deployment : Deployment) (cellId : Nat)
    (payload : Materialized DeclaredEffectPageMaterializer.materializer) :
    selectDeclared deployment cellId .object ⟨.accountMetadata, payload⟩ = none := by
  unfold selectDeclared
  split <;> rfl

theorem book_identity_is_pinned (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer)
    (valid : CellLaw deployment cellId ⟨.resourceBook, payload⟩) :
    cellId = deployment.resourceBookId := valid.2.1

theorem no_user_book_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CanonicalResourcePageMaterializer.materializer) :
    ¬UserInitial deployment cellId ⟨.resourceBook, payload⟩ := fun admitted => admitted.2

theorem no_user_authority_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityPageMaterializer.materializer) :
    ¬UserInitial deployment cellId ⟨.authorityShard, payload⟩ := fun admitted => admitted.2

theorem no_user_catalogue_birth (deployment : Deployment) (cellId : Nat)
    (payload : Materialized CredentialAuthorityDomain.catalogueMaterializer) :
    ¬UserInitial deployment cellId ⟨.authorityCatalogue, payload⟩ := fun admitted => admitted.2

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

namespace Witness

def deployment : Deployment := ⟨⟨42⟩, 1, 2, 3⟩

def page : DeclaredEffectPageMaterializer.Page :=
  ⟨deployment.domain, 10, some ⟨.objectField ⟨10⟩ ⟨1⟩, 17⟩, none, none, none⟩

def payload : Materialized DeclaredEffectPageMaterializer.materializer :=
  materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some page))

def account : PackedCell registry := ⟨.accountMetadata, payload⟩

theorem user_account_inhabited : UserInitial deployment 10 account := by decide

theorem account_dispatch_inhabited :
    (selectDeclared deployment 10 .account account).isSome = true := by decide

theorem object_dispatch_refused : selectDeclared deployment 10 .object account = none :=
  object_cannot_select_account deployment 10 payload

end Witness

end Minidregg.Compiler.CanonicalCellRegistry

/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.registry_lifecycle_root
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.decoded_cell_canonical
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.DeclaredPageLaw.no_balance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.DeclaredPageLaw.no_balance
/-- info: 'Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.CanonicalCellRegistry.Witness.user_account_inhabited
