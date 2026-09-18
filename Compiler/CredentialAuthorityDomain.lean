/-
# Compiler.CredentialAuthorityDomain -- complete routed authority shards

The catalogue enumerates every physical shard in one authority domain.
Shard placement is data in that committed catalogue; semantic coordinate
routing is fixed here. A policy's grant generation, source revision and revision-indexed address
are one entry group, never independently routed fields. Four entry groups occupy a shard.

The checked complete view folds the actual shard entries into the existing
`CredentialAuthorityState.schema`. Its genuine sparse materializer computes
the semantic authority root. Catalogue and shard physical roots stay separate;
the receiving module retains their exact same-snapshot read dependencies.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Compiler.CredentialAuthorityStateCodec
import Theory.PolicyInstall

namespace Minidregg.Compiler.CredentialAuthorityDomain

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- A receiving deployment fixes this anchor. It is not supplied in a request
or chosen by a request's purported policy or capability. -/
structure Anchor where
  domain : Digest
  catalogueCellId : Digest
  deriving DecidableEq, Repr

def fieldGroup : AuthorityField → Nat
  | .capability .object identifier => 9 * identifier.value
  | .capability .account identifier => 9 * identifier.value + 1
  | .capability .program identifier => 9 * identifier.value + 2
  | .issuerEpoch issuer => 9 * issuer.value + 3
  | .policyEpoch policy => 9 * policy.value + 4
  | .policyRevision policy => 9 * policy.value + 4
  | .policyAddress policy _ => 9 * policy.value + 4
  | .subjectKeyEpoch subject => 9 * subject.value + 5
  | .subjectKey subject _ => 9 * subject.value + 5
  | .revoked (.capability identifier) => 9 * identifier.value + 6
  | .revoked (.channel channel) => 9 * channel.value + 7
  | .nullifier identifier => 9 * identifier + 8

def entryGroup : Entry → Nat
  | .capability .object stored => 9 * stored.head.id.value
  | .capability .account stored => 9 * stored.head.id.value + 1
  | .capability .program stored => 9 * stored.head.id.value + 2
  | .issuerEpoch issuer _ => 9 * issuer.value + 3
  | .policy policy _ _ _ => 9 * policy.value + 4
  | .subjectKeyEpoch subject _ => 9 * subject.value + 5
  | .subjectKey key => 9 * key.subject + 5
  | .revocation (.capability identifier) _ => 9 * identifier.value + 6
  | .revocation (.channel channel) _ => 9 * channel.value + 7
  | .nullifier identifier _ => 9 * identifier + 8

theorem entry_fields_same_group (entry : Entry) (field : AuthorityField)
    (member : field ∈ entry.fields) : fieldGroup field = entryGroup entry := by
  cases entry with
  | policy policy generation revision address =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl
  | revocation key revoked =>
      simp only [Entry.fields, List.mem_singleton] at member
      subst field
      cases key <;> rfl
  | capability kind stored =>
      simp only [Entry.fields, List.mem_singleton] at member
      subst field
      cases kind <;> rfl
  | issuerEpoch issuer epoch =>
      simp only [Entry.fields, List.mem_singleton] at member
      subst field
      rfl
  | subjectKeyEpoch subject epoch =>
      simp only [Entry.fields, List.mem_singleton] at member
      subst field
      rfl
  | subjectKey key =>
      simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
  | nullifier identifier consumed =>
      simp only [Entry.fields, List.mem_singleton] at member
      subst field
      rfl

def pageNumber (entry : Entry) : Nat := entryGroup entry / 4
def slotNumber (entry : Entry) : Nat := entryGroup entry % 4

theorem slotNumber_lt_four (entry : Entry) : slotNumber entry < 4 :=
  Nat.mod_lt _ (by decide)

def slotRouted (number slot : Nat) : Option Entry → Prop
  | none => True
  | some entry => pageNumber entry = number ∧ slotNumber entry = slot

instance slotRoutedDecidable (number slot : Nat) (entry : Option Entry) :
    Decidable (slotRouted number slot entry) := by
  cases entry <;> unfold slotRouted <;> infer_instance

def Routed (page : Page) : Prop :=
  slotRouted page.pageNumber 0 page.slot0 ∧
  slotRouted page.pageNumber 1 page.slot1 ∧
  slotRouted page.pageNumber 2 page.slot2 ∧
  slotRouted page.pageNumber 3 page.slot3

instance routedDecidable (page : Page) : Decidable (Routed page) := by
  unfold Routed
  infer_instance

def emptyPage (domain : Digest) (number : Nat) : Page :=
  ⟨domain, number, none, none, none, none⟩

theorem emptyPage_valid (domain : Digest) (number : Nat) :
    (emptyPage domain number).Valid := by
  simp [Page.Valid, Page.fields, Page.entries, emptyPage]

theorem emptyPage_routed (domain : Digest) (number : Nat) :
    Routed (emptyPage domain number) := by simp [Routed, slotRouted, emptyPage]

structure Ref where
  number : Nat
  cellId : Digest
  physicalRoot : Digest
  deriving DecidableEq, Repr

structure Catalogue where
  domain : Digest
  revision : Nat
  pages : List Ref
  deriving DecidableEq, Repr

def Catalogue.Valid (catalogue : Catalogue) : Prop :=
  (catalogue.pages.map Ref.number).Pairwise (· < ·) ∧
    (catalogue.pages.map Ref.cellId).Nodup

instance catalogueValidDecidable (catalogue : Catalogue) : Decidable catalogue.Valid := by
  unfold Catalogue.Valid
  infer_instance

def refStream : StreamCodec Ref :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream digestStream))
    (fun reference => (reference.number, reference.cellId, reference.physicalRoot))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro reference; rfl)

def catalogueStream : StreamCodec Catalogue :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.list refStream)))
    (fun catalogue => (catalogue.domain, catalogue.revision, catalogue.pages))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro catalogue; rfl)

def catalogueSchema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => Catalogue
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq catalogueSchema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq catalogueSchema.Resource := fun resource => resource.elim

def catalogueState : Option Catalogue → LogicalState catalogueSchema
  | none => { fields := 0, resources := fun resource => nomatch resource }
  | some catalogue =>
      { fields := (0 : FieldStore catalogueSchema).write () catalogue
        resources := fun resource => nomatch resource }

def catalogueAt (state : LogicalState catalogueSchema) : Option Catalogue := state.fields ()

theorem catalogueState_at (state : LogicalState catalogueSchema) :
    catalogueState (catalogueAt state) = state := by
  cases state with
  | mk fields resources =>
      have resourcesExact : resources = fun resource => nomatch resource := by
        funext resource
        exact Empty.elim resource
      cases present : fields () with
      | none =>
          have fieldsExact : fields = (0 : FieldStore catalogueSchema) := by
            apply DFinsupp.ext
            intro field
            cases field
            simpa using present
          rw [fieldsExact, resourcesExact]
          rfl
      | some catalogue =>
          have fieldsExact : fields = (0 : FieldStore catalogueSchema).write () catalogue := by
            apply DFinsupp.ext
            intro field
            cases field
            simp [present]
          rw [fieldsExact, resourcesExact]
          rfl

def catalogueStateStream : StreamCodec (LogicalState catalogueSchema) :=
  StreamCodec.xmap (StreamCodec.option catalogueStream) catalogueAt catalogueState
    catalogueState_at

def catalogueFrame : List UInt8 := "LOOM/AUTH/DOMAIN".toUTF8.toList ++ [2]

def encodeCatalogueState (state : LogicalState catalogueSchema) : List UInt8 :=
  catalogueFrame ++ catalogueStateStream.encode state

def decodeCatalogueRaw (bytes : List UInt8) : Option (LogicalState catalogueSchema) :=
  if bytes.take catalogueFrame.length = catalogueFrame then
    catalogueStateStream.toLawful.decode (bytes.drop catalogueFrame.length)
  else none

@[simp] theorem decodeCatalogueRaw_encode (state : LogicalState catalogueSchema) :
    decodeCatalogueRaw (encodeCatalogueState state) = some state := by
  have payload := catalogueStateStream.toLawful.decode_encode state
  change catalogueStateStream.toLawful.decode (catalogueStateStream.encode state) =
    some state at payload
  simp [decodeCatalogueRaw, encodeCatalogueState, payload]

def decodeCatalogueState (bytes : List UInt8) : Option (LogicalState catalogueSchema) := do
  let state ← decodeCatalogueRaw bytes
  if encodeCatalogueState state = bytes then some state else none

theorem decodeCatalogueState_rejects_v1 (payload : List UInt8) :
    decodeCatalogueState ("LOOM/AUTH/DOMAIN".toUTF8.toList ++ 1 :: payload) = none := by
  let oldFrame : List UInt8 := "LOOM/AUTH/DOMAIN".toUTF8.toList ++ [1]
  have lengthExact : catalogueFrame.length = oldFrame.length := by simp [catalogueFrame, oldFrame]
  have frameDifferent : oldFrame ≠ catalogueFrame := by simp [catalogueFrame, oldFrame]
  have raw : decodeCatalogueRaw (oldFrame ++ payload) = none := by
    simp [decodeCatalogueRaw, lengthExact, frameDifferent]
  have rejected : decodeCatalogueState (oldFrame ++ payload) = none := by
    simp [decodeCatalogueState, raw]
  simpa only [oldFrame, List.append_assoc, List.singleton_append] using rejected

@[simp] theorem decodeCatalogueState_encode (state : LogicalState catalogueSchema) :
    decodeCatalogueState (encodeCatalogueState state) = some state := by
  simp [decodeCatalogueState]

theorem decodeCatalogueState_canonical {bytes : List UInt8}
    {state : LogicalState catalogueSchema}
    (accepted : decodeCatalogueState bytes = some state) :
    encodeCatalogueState state = bytes := by
  unfold decodeCatalogueState at accepted
  cases raw : decodeCatalogueRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical => cases Option.some.inj accepted; exact canonical
      next => contradiction

def catalogueCodec : LawfulCodec (LogicalState catalogueSchema) where
  encode := encodeCatalogueState
  decode := decodeCatalogueState
  decode_encode := decodeCatalogueState_encode

def catalogueRootCustomization : List UInt8 := "LOOM.AUTH.DOMAIN.ROOT/v2".toUTF8.toList

def catalogueRoot (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash catalogueRootCustomization bytes).digest

def catalogueMaterializer : CellState.Materializer catalogueSchema Digest where
  codec := catalogueCodec
  rootBytes := catalogueRoot

def allEntries (pages : List Page) : List Entry := pages.flatMap Page.entries

def Complete (catalogue : Catalogue) (pages : List Page) : Prop :=
  catalogue.Valid ∧
    pages.map Page.pageNumber = catalogue.pages.map Ref.number ∧
    (∀ page ∈ pages, page.authorityDomain = catalogue.domain ∧ page.Valid ∧ Routed page) ∧
    ((allEntries pages).flatMap Entry.fields).Nodup

instance completeDecidable (catalogue : Catalogue) (pages : List Page) :
    Decidable (Complete catalogue pages) := by
  unfold Complete
  infer_instance

/-- A complete logical view. Its receiving provenance lives in the indexed
`DomainReceiver.Loaded` value; the physical controller consumes that value,
never a requester-provided `Snapshot`. -/
structure Snapshot where
  private mk ::
  catalogue : Catalogue
  pages : List Page
  complete : Complete catalogue pages

def assemble (catalogue : Catalogue) (pages : List Page) : Option Snapshot :=
  if complete : Complete catalogue pages then some ⟨catalogue, pages, complete⟩ else none

def Snapshot.domain (snapshot : Snapshot) : Digest := snapshot.catalogue.domain
def Snapshot.entries (snapshot : Snapshot) : List Entry := allEntries snapshot.pages

def Snapshot.logical (snapshot : Snapshot) :
    LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := snapshot.entries.foldl Entry.install 0
  resources := fun resource => nomatch resource

def Snapshot.cell (snapshot : Snapshot) :
    Materialized CredentialAuthorityStateCodec.materializer :=
  materialize CredentialAuthorityStateCodec.materializer snapshot.logical

def entryRevocationKeys : Entry → Finset RevocationKey
  | .revocation key _ => {key}
  | .capability _ stored =>
      insert (.capability stored.head.id)
        ((stored.head.ancestors.image RevocationKey.capability) ∪
          (stored.head.channels.image RevocationKey.channel))
  | _ => ∅

def Snapshot.revocationUniverse (snapshot : Snapshot) : ProjectionUniverse :=
  ⟨snapshot.entries.foldr (fun entry keys => entryRevocationKeys entry ∪ keys) ∅⟩

def Snapshot.authState (snapshot : Snapshot) : AuthState :=
  CredentialAuthorityState.authState snapshot.revocationUniverse snapshot.cell

def headAt (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) (policy : PolicyId) :
    Option PolicyInstall.Head := do
  let _generation ← logical.fields (.policyEpoch policy)
  let revision ← logical.fields (.policyRevision policy)
  let address ← logical.fields (.policyAddress policy revision)
  some ⟨revision, address⟩

theorem headAt_missing_generation
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) (policy : PolicyId)
    (missing : logical.fields (.policyEpoch policy) = none) :
    headAt logical policy = none := by simp [headAt, missing]

theorem headAt_missing_revision
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) (policy : PolicyId)
    (missing : logical.fields (.policyRevision policy) = none) :
    headAt logical policy = none := by
  unfold headAt
  cases logical.fields (.policyEpoch policy) <;> simp [missing]

def Snapshot.currentHead (snapshot : Snapshot) (policy : PolicyId) :
    Option PolicyInstall.Head := headAt snapshot.logical policy

def Snapshot.currentSigningKey (snapshot : Snapshot) (subject : SubjectId) :
    Option CredentialSigningKey.KeyRecord :=
  CredentialAuthorityState.currentSigningKey snapshot.logical subject

def Snapshot.policyContains (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : Nat) (address : Digest) : Prop :=
  Entry.policy policy generation revision address ∈ snapshot.entries

instance snapshotPolicyContainsDecidable (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : Nat) (address : Digest) :
    Decidable (snapshot.policyContains policy generation revision address) := by
  unfold Snapshot.policyContains
  infer_instance

theorem Snapshot.entry_exact (snapshot : Snapshot) (entry : Entry)
    (member : entry ∈ snapshot.entries) (field : AuthorityField)
    (inside : field ∈ entry.fields) :
    snapshot.logical.fields field = Entry.install 0 entry field :=
  installEntries_exact snapshot.entries snapshot.complete.2.2.2 entry member field inside 0

theorem Snapshot.absent_exact (snapshot : Snapshot) (field : AuthorityField)
    (outside : field ∉ snapshot.entries.flatMap Entry.fields) :
    snapshot.logical.fields field = none :=
  installEntries_frame snapshot.entries 0 field outside

theorem Snapshot.cell_projection_exact (snapshot : Snapshot) :
    snapshot.cell.logical = snapshot.logical := rfl

theorem Snapshot.policy_exact (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : Nat) (address : Digest)
    (member : snapshot.policyContains policy generation revision address) :
    snapshot.currentHead policy = some ⟨revision, address⟩ := by
  have generationExact := snapshot.entry_exact (.policy policy generation revision address) member
    (.policyEpoch policy) (by simp [Entry.fields])
  have revisionExact := snapshot.entry_exact (.policy policy generation revision address) member
    (.policyRevision policy) (by simp [Entry.fields])
  have addressExact := snapshot.entry_exact (.policy policy generation revision address) member
    (.policyAddress policy revision) (by simp [Entry.fields])
  simp [Entry.install] at generationExact revisionExact addressExact
  simp [Snapshot.currentHead, headAt, generationExact, revisionExact, addressExact]

theorem Snapshot.signingKey_exact (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord)
    (member : Entry.subjectKey key ∈ snapshot.entries) :
    snapshot.currentSigningKey ⟨key.subject⟩ = some key := by
  apply CredentialAuthorityState.currentSigningKey_exact
  · have exactEpoch := snapshot.entry_exact (.subjectKey key) member
      (.subjectKeyEpoch ⟨key.subject⟩) (by simp [Entry.fields])
    simpa [Entry.install] using exactEpoch
  · have exactKey := snapshot.entry_exact (.subjectKey key) member
      (.subjectKey ⟨key.subject⟩ key.keyEpoch) (by simp [Entry.fields])
    simpa [Entry.install] using exactKey

/-! ## Source-derived routed updates and exact canonical patch refinement -/

def logicalOfPages (pages : List Page) :
    LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := (allEntries pages).foldl Entry.install 0
  resources := fun resource => nomatch resource

def PagesValid (domain : Digest) (pages : List Page) : Prop :=
  (pages.map Page.pageNumber).Pairwise (· < ·) ∧
    (∀ page ∈ pages, page.authorityDomain = domain ∧ page.Valid ∧ Routed page) ∧
    ((allEntries pages).flatMap Entry.fields).Nodup

instance pagesValidDecidable (domain : Digest) (pages : List Page) :
    Decidable (PagesValid domain pages) := by
  unfold PagesValid
  infer_instance

theorem Snapshot.pages_valid (snapshot : Snapshot) :
    PagesValid snapshot.domain snapshot.pages := by
  refine ⟨?_, snapshot.complete.2.2.1, snapshot.complete.2.2.2⟩
  rw [snapshot.complete.2.1]
  exact snapshot.complete.1.1

/-- An exact old entry is required for replacement. Absence is an insertion,
not permission to overwrite the selected slot. Only entries in the same
source-defined coordinate group can replace one another. -/
structure Edit where
  before : Option Entry
  after : Entry
  deriving DecidableEq, Repr

def slotAt (page : Page) : Nat → Option Entry
  | 0 => page.slot0
  | 1 => page.slot1
  | 2 => page.slot2
  | 3 => page.slot3
  | _ => none

def setSlot (page : Page) (slot : Nat) (entry : Option Entry) : Page :=
  match slot with
  | 0 => { page with slot0 := entry }
  | 1 => { page with slot1 := entry }
  | 2 => { page with slot2 := entry }
  | 3 => { page with slot3 := entry }
  | _ => page

def Edit.sameGroup (edit : Edit) : Prop :=
  ∀ old ∈ edit.before, entryGroup old = entryGroup edit.after

instance editSameGroupDecidable (edit : Edit) : Decidable edit.sameGroup := by
  unfold Edit.sameGroup
  infer_instance

def editPage (page : Page) (edit : Edit) : Option Page := do
  if page.pageNumber = pageNumber edit.after ∧ edit.sameGroup ∧
      slotAt page (slotNumber edit.after) = edit.before then
    let post := setSlot page (slotNumber edit.after) (some edit.after)
    if post.Valid ∧ Routed post then some post else none
  else none

/-- Sorted replacement/insertion has one result per page number. A batch of
edits on one shard therefore produces one physical post image. -/
def putPage (page : Page) : List Page → List Page
  | [] => [page]
  | head :: rest =>
      if page.pageNumber < head.pageNumber then page :: head :: rest
      else if page.pageNumber = head.pageNumber then page :: rest
      else head :: putPage page rest

def runEdits (domain : Digest) : List Page → List Edit → Option (List Page)
  | pages, [] => some pages
  | pages, edit :: rest => do
      let pre := (pages.find? fun page => page.pageNumber = pageNumber edit.after).getD
        (emptyPage domain (pageNumber edit.after))
      let post ← editPage pre edit
      runEdits domain (putPage post pages) rest

/-- Typed writes are derived from the entry's existing field vocabulary and
interpreter. This does not reimplement dependent authority values. -/
def entryWrites (entry : Entry) : List (FieldWrite CredentialAuthorityState.schema.{0, 0}) :=
  entry.fields.map fun field => ⟨field, Entry.install 0 entry field⟩

theorem entryWrites_policy (policy : PolicyId) (generation : Epoch)
    (revision : Nat) (address : Digest) :
    entryWrites (.policy policy generation revision address) =
      [⟨.policyEpoch policy, some generation⟩, ⟨.policyRevision policy, some revision⟩,
        ⟨.policyAddress policy revision, some address⟩] := by
  simp [entryWrites, Entry.fields, List.map, Entry.install]

theorem entryWrites_subjectKey (key : CredentialSigningKey.KeyRecord) :
    entryWrites (.subjectKey key) =
      [⟨.subjectKeyEpoch ⟨key.subject⟩, some key.keyEpoch⟩,
        ⟨.subjectKey ⟨key.subject⟩ key.keyEpoch, some key⟩] := by
  simp [entryWrites, Entry.fields, List.map, Entry.install]

theorem entryWrites_nullifier (nullifierId : Nat) (consumed : Bool) :
    entryWrites (.nullifier nullifierId consumed) =
      [⟨.nullifier nullifierId, some consumed⟩] := by
  simp [entryWrites, Entry.fields, List.map, Entry.install]

def Edit.writes (edit : Edit) : List (FieldWrite CredentialAuthorityState.schema.{0, 0}) :=
  (edit.before.toList.flatMap Entry.fields).map (fun field => ⟨field, none⟩) ++
    entryWrites edit.after

def editPatch (snapshot : Snapshot) (edits : List Edit) :
    Patch CredentialAuthorityState.schema.{0, 0} Digest where
  expectedPreRoot := snapshot.cell.root
  fieldFootprint := ((edits.flatMap Edit.writes).map FieldWrite.field).toFinset
  resourceFootprint := ∅
  fieldWrites := edits.flatMap Edit.writes
  resourceWrites := []

/-- A prepared update has no authorization. It contains the computed routed
post and the existing kernel validator token, joined by exact canonical-state
equality. The receiving adapter subsequently binds its physical writes and
complete pre-snapshot; a semantic family still supplies authorization. -/
structure Prepared (snapshot : Snapshot) (edits : List Edit) where
  private mk ::
  postPages : List Page
  computed : runEdits snapshot.domain snapshot.pages edits = some postPages
  valid : PagesValid snapshot.domain postPages
  validated : ValidatedPatch CredentialAuthorityStateCodec.materializer snapshot.cell
    (editPatch snapshot edits)
  projectionExact : logicalOfPages postPages = validated.apply.logical

def Prepared.postLogical {snapshot : Snapshot} {edits : List Edit}
    (prepared : Prepared snapshot edits) : LogicalState CredentialAuthorityState.schema.{0, 0} :=
  logicalOfPages prepared.postPages

def Prepared.postCell {snapshot : Snapshot} {edits : List Edit}
    (prepared : Prepared snapshot edits) : Materialized CredentialAuthorityStateCodec.materializer :=
  materialize CredentialAuthorityStateCodec.materializer prepared.postLogical

/-- The exact re-encoding check is a executable proof-producing refinement
check, not a root comparison. Neither the post pages nor the post logical
state is accepted from the caller. -/
def prepare (snapshot : Snapshot) (edits : List Edit) : Option (Prepared snapshot edits) :=
  match computed : runEdits snapshot.domain snapshot.pages edits with
  | none => none
  | some pages =>
      if valid : PagesValid snapshot.domain pages then
        match validate CredentialAuthorityStateCodec.materializer snapshot.cell
            (editPatch snapshot edits) with
        | .rejected _ => none
        | .accepted validated =>
            if exactBytes : CredentialAuthorityStateCodec.encode (logicalOfPages pages) =
                CredentialAuthorityStateCodec.encode validated.apply.logical then
              some ⟨pages, computed, valid, validated,
                CredentialAuthorityStateCodec.encode_injective exactBytes⟩
            else none
      else none

theorem Prepared.post_exact {snapshot : Snapshot} {edits : List Edit}
    (prepared : Prepared snapshot edits) : prepared.postCell = prepared.validated.apply := by
  apply Materialized.ext
  exact prepared.projectionExact

theorem Prepared.frame {snapshot : Snapshot} {edits : List Edit}
    (prepared : Prepared snapshot edits) (field : AuthorityField)
    (outside : field ∉ (editPatch snapshot edits).fieldFootprint) :
    prepared.postLogical.fields field = snapshot.logical.fields field := by
  rw [show prepared.postLogical = prepared.validated.apply.logical from prepared.projectionExact]
  exact prepared.validated.field_frame field outside

/-- Policy identity fixes the old entry; the request cannot choose which
version is replaced or request a partial page view. Succession and policy
authorization are checked by the existing policy family. -/
def policyEdit (snapshot : Snapshot) (policy : PolicyId) (epoch : Epoch)
    (address : Digest) : Edit where
  before := (snapshot.currentHead policy).map fun head =>
    .policy policy (snapshot.authState.policyEpoch policy) head.version head.address
  after := .policy policy (snapshot.authState.policyEpoch policy) epoch address

def preparePolicy (snapshot : Snapshot) (policy : PolicyId) (epoch : Epoch)
    (address : Digest) : Option (Prepared snapshot [policyEdit snapshot policy epoch address]) :=
  if (snapshot.currentHead policy).isSome then
    prepare snapshot [policyEdit snapshot policy epoch address]
  else none

theorem policyEdit_sameGroup (snapshot : Snapshot) (policy : PolicyId)
    (epoch : Epoch) (address : Digest) :
    (policyEdit snapshot policy epoch address).sameGroup := by
  unfold Edit.sameGroup policyEdit
  intro old member
  simp only [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨head, _, rfl⟩ := member
  rfl

theorem preparedPolicy_head {snapshot : Snapshot} {policy : PolicyId}
    {epoch : Epoch} {address : Digest}
    (prepared : Prepared snapshot [policyEdit snapshot policy epoch address]) :
    headAt prepared.postLogical policy = some ⟨epoch, address⟩ := by
  rw [show prepared.postLogical = prepared.validated.apply.logical from prepared.projectionExact]
  cases old : snapshot.currentHead policy <;>
    simp [headAt, ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
      policyEdit, old, Entry.fields, applyFieldWrites,
      FieldStore.assign, List.map_cons, List.map_nil, materialize]

theorem preparedPolicy_retired_address_absent {snapshot : Snapshot} {policy : PolicyId}
    {epoch : Epoch} {address : Digest}
    (prepared : Prepared snapshot [policyEdit snapshot policy epoch address])
    (old : PolicyInstall.Head) (current : snapshot.currentHead policy = some old)
    (different : old.version ≠ epoch) :
    prepared.postLogical.fields (.policyAddress policy old.version) = none := by
  rw [show prepared.postLogical = prepared.validated.apply.logical from prepared.projectionExact]
  simp [ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
    policyEdit, current, Entry.fields, applyFieldWrites,
    FieldStore.assign, List.map_cons, List.map_nil, materialize]
  have differentFields : AuthorityField.policyAddress policy old.version ≠
      AuthorityField.policyAddress policy epoch := by
    intro equal
    exact different (AuthorityField.policyAddress.inj equal).2
  simp_all [Function.update]
  intro equal
  exact (different (AuthorityField.policyAddress.inj equal).2).elim

/-- The old current key (or explicitly keyless epoch) comes from the complete
pre-state. The new record itself determines both coordinates. This prepares
a patch only; the surrounding authority family must authorize installation. -/
def signingKeyEdit (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord) : Edit where
  before := match snapshot.currentSigningKey ⟨key.subject⟩ with
    | some old => some (.subjectKey old)
    | none => (snapshot.logical.fields (.subjectKeyEpoch ⟨key.subject⟩)).map
        fun epoch => .subjectKeyEpoch ⟨key.subject⟩ epoch
  after := .subjectKey key

def prepareSigningKey (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord) :
    Option (Prepared snapshot [signingKeyEdit snapshot key]) :=
  prepare snapshot [signingKeyEdit snapshot key]

/-- Preserve the exact optional pre-state spelling while consuming the one
canonical operation marker. Admission separately requires it to be unused. -/
def nullifierEdit (snapshot : Snapshot) (nullifierId : Nat) : Edit where
  before := (snapshot.logical.fields (.nullifier nullifierId)).map
    (Entry.nullifier nullifierId)
  after := .nullifier nullifierId true

theorem preparedSigningKey_exact {snapshot : Snapshot} {key : CredentialSigningKey.KeyRecord}
    (prepared : Prepared snapshot [signingKeyEdit snapshot key]) :
    CredentialAuthorityState.currentSigningKey prepared.postLogical ⟨key.subject⟩ = some key := by
  rw [show prepared.postLogical = prepared.validated.apply.logical from prepared.projectionExact]
  cases selected : snapshot.currentSigningKey ⟨key.subject⟩ with
  | some old =>
      simp [CredentialAuthorityState.currentSigningKey, ValidatedPatch.apply,
        editPatch, Edit.writes, signingKeyEdit, selected, Entry.fields,
        entryWrites_subjectKey, applyFieldWrites, FieldStore.assign, materialize,
        bind, Option.bind]
  | none =>
      cases epoch : snapshot.logical.fields (.subjectKeyEpoch ⟨key.subject⟩) <;>
        simp [CredentialAuthorityState.currentSigningKey, ValidatedPatch.apply,
          editPatch, Edit.writes, signingKeyEdit, selected, epoch, Entry.fields,
          entryWrites_subjectKey, applyFieldWrites, FieldStore.assign, materialize,
          Option.map, List.map_cons, List.map_nil, bind, Option.bind]

def policyAndNullifierEdits (snapshot : Snapshot) (policy : PolicyId)
    (epoch : Epoch) (address : Digest) (nullifierId : Nat) : List Edit :=
  [policyEdit snapshot policy epoch address, nullifierEdit snapshot nullifierId]

/-- One grouped authority update retains the exact unused-marker evidence.
Authorization and final joint-post checks remain with the existing family. -/
structure PreparedPolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (epoch : Epoch) (address : Digest) (nullifierId : Nat) where
  prepared : Prepared snapshot (policyAndNullifierEdits snapshot policy epoch address nullifierId)
  nullifierFresh : isNullified snapshot.cell nullifierId = false
  generationPresent : snapshot.logical.fields (.policyEpoch policy) =
    some (snapshot.authState.policyEpoch policy)

def preparePolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (epoch : Epoch) (address : Digest) (nullifierId : Nat) :
    Option (PreparedPolicyAndNullifier snapshot policy epoch address nullifierId) := do
  if fresh : isNullified snapshot.cell nullifierId = false then
    if present : (show Option Epoch from snapshot.logical.fields (.policyEpoch policy)) =
        some (snapshot.authState.policyEpoch policy) then
      let _old ← snapshot.currentHead policy
      let prepared ← prepare snapshot (policyAndNullifierEdits snapshot policy epoch address nullifierId)
      some ⟨prepared, fresh, present⟩
    else none
  else none

theorem PreparedPolicyAndNullifier.head_exact
    {snapshot : Snapshot} {policy : PolicyId} {epoch : Epoch} {address : Digest} {nullifierId : Nat}
    (update : PreparedPolicyAndNullifier snapshot policy epoch address nullifierId) :
    headAt update.prepared.postLogical policy = some ⟨epoch, address⟩ := by
  rw [show update.prepared.postLogical = update.prepared.validated.apply.logical from
    update.prepared.projectionExact]
  cases old : snapshot.currentHead policy <;>
    cases marker : snapshot.logical.fields (.nullifier nullifierId) <;>
    simp [headAt, ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
      entryWrites_nullifier, policyAndNullifierEdits, policyEdit, nullifierEdit, old, marker,
      Entry.fields, applyFieldWrites, FieldStore.assign, List.map_cons, List.map_nil,
      Option.map, materialize] <;> rfl

theorem PreparedPolicyAndNullifier.generation_exact
    {snapshot : Snapshot} {policy : PolicyId} {epoch : Epoch} {address : Digest} {nullifierId : Nat}
    (update : PreparedPolicyAndNullifier snapshot policy epoch address nullifierId) :
    update.prepared.postLogical.fields (.policyEpoch policy) =
      some (snapshot.authState.policyEpoch policy) := by
  rw [show update.prepared.postLogical = update.prepared.validated.apply.logical from
    update.prepared.projectionExact]
  cases old : snapshot.currentHead policy <;>
    cases marker : snapshot.logical.fields (.nullifier nullifierId) <;>
    simp [ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
      entryWrites_nullifier, policyAndNullifierEdits, policyEdit, nullifierEdit, old, marker,
      Entry.fields, applyFieldWrites, FieldStore.assign, List.map_cons, List.map_nil,
      Option.map, materialize] <;> rfl

theorem PreparedPolicyAndNullifier.generation_preserved
    {snapshot : Snapshot} {policy : PolicyId} {epoch : Epoch} {address : Digest} {nullifierId : Nat}
    (update : PreparedPolicyAndNullifier snapshot policy epoch address nullifierId) :
    update.prepared.postLogical.fields (.policyEpoch policy) =
      snapshot.logical.fields (.policyEpoch policy) :=
  update.generation_exact.trans update.generationPresent.symm

theorem PreparedPolicyAndNullifier.nullifier_consumed
    {snapshot : Snapshot} {policy : PolicyId} {epoch : Epoch} {address : Digest} {nullifierId : Nat}
    (update : PreparedPolicyAndNullifier snapshot policy epoch address nullifierId) :
    update.prepared.postLogical.fields (.nullifier nullifierId) = some true := by
  rw [show update.prepared.postLogical = update.prepared.validated.apply.logical from
    update.prepared.projectionExact]
  cases old : snapshot.currentHead policy <;>
    cases marker : snapshot.logical.fields (.nullifier nullifierId) <;>
    simp [ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
      entryWrites_nullifier, policyAndNullifierEdits, policyEdit, nullifierEdit, old, marker,
      Entry.fields, applyFieldWrites, FieldStore.assign, List.map_cons, List.map_nil,
      Option.map, materialize] <;> rfl

theorem PreparedPolicyAndNullifier.retired_address_absent
    {snapshot : Snapshot} {policy : PolicyId} {epoch : Epoch} {address : Digest} {nullifierId : Nat}
    (update : PreparedPolicyAndNullifier snapshot policy epoch address nullifierId)
    (old : PolicyInstall.Head) (current : snapshot.currentHead policy = some old)
    (different : old.version ≠ epoch) :
    update.prepared.postLogical.fields (.policyAddress policy old.version) = none := by
  rw [show update.prepared.postLogical = update.prepared.validated.apply.logical from
    update.prepared.projectionExact]
  cases marker : snapshot.logical.fields (.nullifier nullifierId) <;>
    simp [ValidatedPatch.apply, editPatch, Edit.writes, entryWrites_policy,
      entryWrites_nullifier, policyAndNullifierEdits, policyEdit, nullifierEdit, current, marker,
      Entry.fields, applyFieldWrites, FieldStore.assign, List.map_cons, List.map_nil,
      Option.map, materialize] <;>
    simp_all [Function.update] <;>
    intro equal <;> exact (different (AuthorityField.policyAddress.inj equal).2).elim

theorem preparePolicyAndNullifier_used_refused (snapshot : Snapshot) (policy : PolicyId)
    (epoch : Epoch) (address : Digest) (nullifierId : Nat)
    (used : isNullified snapshot.cell nullifierId = true) :
    preparePolicyAndNullifier snapshot policy epoch address nullifierId = none := by
  simp [preparePolicyAndNullifier, used]

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.entry_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.entry_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Prepared.post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Prepared.post_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.preparedPolicy_retired_address_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedPolicy_retired_address_absent

/-! ## Complete revocations and source-derived issuance registration -/

theorem revoked_field_has_key (entry : Entry) (key : RevocationKey)
    (present : AuthorityField.revoked key ∈ entry.fields) :
    key ∈ entryRevocationKeys entry := by
  cases entry with
  | policy policy generation revision address => simp [Entry.fields] at present
  | revocation other revoked =>
      simp only [Entry.fields, List.mem_singleton, AuthorityField.revoked.injEq] at present
      subst other
      simp [entryRevocationKeys]
  | capability kind stored => simp [Entry.fields] at present
  | issuerEpoch issuer epoch => simp [Entry.fields] at present
  | subjectKeyEpoch subject epoch => simp [Entry.fields] at present
  | subjectKey key => simp [Entry.fields] at present
  | nullifier identifier consumed => simp [Entry.fields] at present

theorem mem_fold_revocationKeys (entries : List Entry) (entry : Entry)
    (present : entry ∈ entries) (key : RevocationKey)
    (registered : key ∈ entryRevocationKeys entry) :
    key ∈ entries.foldr (fun item keys => entryRevocationKeys item ∪ keys) ∅ := by
  induction entries with
  | nil => simp at present
  | cons head rest induction =>
      rcases List.mem_cons.mp present with rfl | inRest
      · exact Finset.mem_union_left _ registered
      · exact Finset.mem_union_right _ (induction inRest)

/-- Every omitted key is actually absent in the complete canonical field
support. A finite revocation projection cannot silently forget a true flag. -/
theorem Snapshot.revocation_absent_of_outside (snapshot : Snapshot) (key : RevocationKey)
    (outside : key ∉ snapshot.revocationUniverse.revocationKeys) :
    snapshot.logical.fields (.revoked key) = none := by
  apply snapshot.absent_exact
  intro present
  obtain ⟨entry, entryPresent, fieldPresent⟩ := List.mem_flatMap.mp present
  apply outside
  exact mem_fold_revocationKeys snapshot.entries entry entryPresent key
    (revoked_field_has_key entry key fieldPresent)

theorem Snapshot.revocation_false_of_outside (snapshot : Snapshot) (key : RevocationKey)
    (outside : key ∉ snapshot.revocationUniverse.revocationKeys) :
    isRevoked snapshot.cell key = false := by
  change (snapshot.logical.fields (.revoked key)).getD false = false
  rw [snapshot.revocation_absent_of_outside key outside]
  rfl

def Snapshot.extendedUniverse (snapshot : Snapshot) (additional : Finset RevocationKey) :
    ProjectionUniverse :=
  ⟨snapshot.revocationUniverse.revocationKeys ∪ additional⟩

/-- Registration can grow without changing ANY old authorization field or
root because the complete old projection already includes every true flag.
The receiving preparation supplies only the proposed grants' own self keys;
channel registration is still checked against the original universe. -/
theorem Snapshot.authState_extension_exact (snapshot : Snapshot)
    (additional : Finset RevocationKey) :
    CredentialAuthorityState.authState (snapshot.extendedUniverse additional) snapshot.cell =
      snapshot.authState := by
  have revokedExact :
      (snapshot.revocationUniverse.revocationKeys ∪ additional).filter
          (fun key => isRevoked snapshot.cell key) =
        snapshot.revocationUniverse.revocationKeys.filter
          (fun key => isRevoked snapshot.cell key) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨registered | added, live⟩
      · exact ⟨registered, live⟩
      · by_cases registered : key ∈ snapshot.revocationUniverse.revocationKeys
        · exact ⟨registered, live⟩
        · rw [snapshot.revocation_false_of_outside key registered] at live
          contradiction
    · rintro ⟨registered, live⟩
      exact ⟨Or.inl registered, live⟩
  unfold CredentialAuthorityState.authState Snapshot.authState Snapshot.extendedUniverse
  dsimp only
  rw [revokedExact]
  rfl

end Minidregg.Compiler.CredentialAuthorityDomain
