/-
# Compiler.CredentialAuthorityDomainReceiver -- the anchored physical join

The fixed production registry decodes one catalogue at a deployment-owned
anchor and EVERY shard named by that catalogue from one durable snapshot.
No request supplies a page subset, authority projection, decoder or root
function. Complete read dependencies accompany the derived semantic cell.

Routed semantic preparation lives in CredentialAuthorityDomain. This module
owns only its exact physical representation and deterministic allocation of
new internal authority shards; native authority roots and lifecycle CAS roots
remain distinct.
-/
import Compiler.CanonicalCellRegistry
import Compiler.DurableReceiverIO
import Theory.ResourceBirthAuthority

namespace Minidregg.Compiler.CredentialAuthorityDomainReceiver

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev PhysicalSnapshot := DataSnapshot ResourceBirthCodec.rootBytes

def shardCell (page : Page) : PackedCell registry :=
  ⟨.authorityShard,
    materialize CredentialAuthorityPageMaterializer.materializer (stateOfOption (some page))⟩

def catalogueCell (catalogue : Catalogue) : PackedCell registry :=
  ⟨.authorityCatalogue, materialize catalogueMaterializer (catalogueState (some catalogue))⟩

def shardBytes (page : Page) : List UInt8 :=
  LifecycleImage.bytes registry (.live (shardCell page))

def catalogueBytes (catalogue : Catalogue) : List UInt8 :=
  LifecycleImage.bytes registry (.live (catalogueCell catalogue))

def decodeCatalogue (bytes : List UInt8) : Option Catalogue := do
  let image ← (LifecycleImage.codec registry).decode bytes
  match image with
  | .live ⟨.authorityCatalogue, payload⟩ => catalogueAt payload.logical
  | _ => none

def decodeShard (bytes : List UInt8) : Option Page := do
  let image ← (LifecycleImage.codec registry).decode bytes
  match image with
  | .live ⟨.authorityShard, payload⟩ => pageAt payload.logical
  | _ => none

def decodePages (physical : PhysicalSnapshot) : List Ref → Option (List Page)
  | [] => some []
  | reference :: rest => do
      let page ← decodeShard (physical.canonicalBytes reference.cellId)
      let pages ← decodePages physical rest
      some (page :: pages)

def PageObserved (physical : PhysicalSnapshot) (reference : Ref) (page : Page) : Prop :=
  physical.canonicalBytes reference.cellId = shardBytes page ∧
    reference.physicalRoot = ResourceBirthCodec.rootBytes (shardBytes page)

instance pageObservedDecidable (physical : PhysicalSnapshot) (reference : Ref) (page : Page) :
    Decidable (PageObserved physical reference page) := by
  unfold PageObserved
  infer_instance

def Observed (anchor : Anchor) (physical : PhysicalSnapshot)
    (snapshot : CredentialAuthorityDomain.Snapshot) : Prop :=
  snapshot.domain = anchor.domain ∧
    anchor.catalogueCellId ∉ snapshot.catalogue.pages.map Ref.cellId ∧
    physical.canonicalBytes anchor.catalogueCellId = catalogueBytes snapshot.catalogue ∧
    List.Forall₂ (PageObserved physical) snapshot.catalogue.pages snapshot.pages

instance observedDecidable (anchor : Anchor) (physical : PhysicalSnapshot)
    (snapshot : CredentialAuthorityDomain.Snapshot) : Decidable (Observed anchor physical snapshot) := by
  unfold Observed
  infer_instance

/-- The constructor is private: callers load all anchored dependencies from
one existing physical snapshot. Pure logical `Domain.assemble` does not mint
this receiving provenance. -/
structure Loaded (anchor : Anchor) (physical : PhysicalSnapshot) where
  private mk ::
  snapshot : CredentialAuthorityDomain.Snapshot
  observed : Observed anchor physical snapshot

def load (anchor : Anchor) (physical : PhysicalSnapshot) : Option (Loaded anchor physical) := do
  let catalogue ← decodeCatalogue (physical.canonicalBytes anchor.catalogueCellId)
  let pages ← decodePages physical catalogue.pages
  let snapshot ← assemble catalogue pages
  if observed : Observed anchor physical snapshot then some ⟨snapshot, observed⟩ else none

theorem observed_roots (physical : PhysicalSnapshot) {references : List Ref} {pages : List Page}
    (observed : List.Forall₂ (PageObserved physical) references pages) :
    ∀ reference ∈ references,
      reference.physicalRoot = physical.model.roots reference.cellId := by
  induction observed with
  | nil => simp
  | @cons reference page references pages here tail induction =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact here.2.trans ((congrArg ResourceBirthCodec.rootBytes here.1.symm).trans
          (physical.coherent _))
      · exact induction selected inTail

def Loaded.readGuards {anchor : Anchor} {physical : PhysicalSnapshot}
    (loaded : Loaded anchor physical) : List ReadGuard :=
  { cellId := anchor.catalogueCellId,
    expectedRoot := physical.model.roots anchor.catalogueCellId } ::
  loaded.snapshot.catalogue.pages.map fun reference =>
    { cellId := reference.cellId, expectedRoot := reference.physicalRoot }

theorem Loaded.readGuards_exact {anchor : Anchor} {physical : PhysicalSnapshot}
    (loaded : Loaded anchor physical) (guard : ReadGuard) (member : guard ∈ loaded.readGuards) :
    guard.expectedRoot = physical.model.roots guard.cellId := by
  rcases List.mem_cons.mp member with rfl | shard
  · rfl
  · obtain ⟨reference, referenceMember, rfl⟩ := List.mem_map.mp shard
    exact observed_roots physical loaded.observed.2.2.2 reference referenceMember

theorem Loaded.guards_catalogue {anchor : Anchor} {physical : PhysicalSnapshot}
    (loaded : Loaded anchor physical) :
    anchor.catalogueCellId ∈ loaded.readGuards.map ReadGuard.cellId := by
  simp [Loaded.readGuards]

theorem Loaded.guards_every_shard {anchor : Anchor} {physical : PhysicalSnapshot}
    (loaded : Loaded anchor physical) (reference : Ref)
    (member : reference ∈ loaded.snapshot.catalogue.pages) :
    reference.cellId ∈ loaded.readGuards.map ReadGuard.cellId := by
  simp only [Loaded.readGuards, List.map_cons, List.mem_cons, List.map_map]
  exact Or.inr (List.mem_map.mpr ⟨reference, member, rfl⟩)

theorem Loaded.no_anchor_alias {anchor : Anchor} {physical : PhysicalSnapshot}
    (loaded : Loaded anchor physical) :
    anchor.catalogueCellId ∉ loaded.snapshot.catalogue.pages.map Ref.cellId :=
  loaded.observed.2.1

/-! ## One complete physical directory, including retired identities -/

def directoryRows (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    List (Nat × List UInt8) :=
  durable.cells.map fun row => (row.1.value, row.2)

/-- The finite support comes from the complete replayed durable image. A
request cannot supply a reduced directory or discard tombstones to influence
fresh allocation. The only absent lifecycle representation is `[]`. -/
structure LoadedDirectory (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) where
  private mk ::
  directory : Directory Nat registry
  decoded : DirectoryImage.decode registry (directoryRows durable) = some directory
  absentDefault : durable.image.seed.absentBytes = []

def loadDirectory (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    Option (LoadedDirectory durable) :=
  if absentDefault : durable.image.seed.absentBytes = [] then
    match decoded : DirectoryImage.decode registry (directoryRows durable) with
    | none => none
    | some directory => some ⟨directory, decoded, absentDefault⟩
  else none

private theorem lookup_enumeration (identifiers : List Digest)
    (bytes : Digest → List UInt8) (identifier : Nat) :
    ((identifiers.map fun selected => (selected.value, bytes selected)).lookup identifier).getD [] =
      if (⟨identifier⟩ : Digest) ∈ identifiers then bytes ⟨identifier⟩ else [] := by
  induction identifiers with
  | nil => simp
  | cons head rest induction =>
      cases head with
      | mk value =>
          by_cases equal : identifier = value
          · subst value
            simp
          · have differentBool : (identifier == value) = false := by simp [equal]
            simpa [List.lookup_cons, differentBool, equal, Ne.symm equal] using induction

/-- Global exactness, including identities outside the finite support. This
is stronger than checking only the cells selected by the incoming request. -/
theorem LoadedDirectory.bytes_exact
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (identifier : Nat) :
    LifecycleImage.bytes registry (LifecycleImage.view registry loaded.directory identifier) =
      durable.snapshot.canonicalBytes ⟨identifier⟩ := by
  rw [DirectoryImage.decode_exact registry loaded.decoded identifier]
  simp only [directoryRows, DurableReceiverIO.Loaded.cells, List.map_map, Function.comp_def]
  rw [lookup_enumeration]
  split
  next => rfl
  next outside =>
    exact (durable.image.outside_support ResourceBirthCodec.rootBytes durable.snapshot
      durable.represented ⟨identifier⟩ outside).trans loaded.absentDefault |>.symm

def LoadedDirectory.freshCursor
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (requestedUserIds : List Nat) : Nat :=
  (loaded.directory.used ∪ requestedUserIds.toFinset).sup (fun value => value) + 1

theorem LoadedDirectory.cursor_above_used
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (requestedUserIds : List Nat)
    (identifier : Nat) (used : identifier ∈ loaded.directory.used) :
    identifier < loaded.freshCursor requestedUserIds := by
  apply Nat.lt_succ_of_le
  exact Finset.le_sup (f := fun value : Nat => value) (Finset.mem_union_left _ used)

theorem LoadedDirectory.cursor_above_user
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (requestedUserIds : List Nat)
    (identifier : Nat) (requested : identifier ∈ requestedUserIds) :
    identifier < loaded.freshCursor requestedUserIds := by
  apply Nat.lt_succ_of_le
  exact Finset.le_sup (f := fun value : Nat => value)
    (Finset.mem_union_right _ (List.mem_toFinset.mpr requested))

/-! ## Deterministic physical placement and grouped writes -/

structure Placement where
  references : List Ref
  auxiliaryCreates : List (CreateRequest (CellId := Nat) registry)

/-- Existing shard identities are retained. New identities increase from a
cursor derived from the complete used set and requested user births, never
from the final descriptor hash (which includes these creates). -/
def placePages (old : Catalogue) : List Page → Nat → Placement
  | [], _ => ⟨[], []⟩
  | page :: rest, cursor =>
      match old.pages.find? (fun reference => reference.number = page.pageNumber) with
      | some reference =>
          let tail := placePages old rest cursor
          ⟨{ reference with physicalRoot := ResourceBirthCodec.rootBytes (shardBytes page) } ::
              tail.references, tail.auxiliaryCreates⟩
      | none =>
          let tail := placePages old rest (cursor + 1)
          ⟨⟨page.pageNumber, ⟨cursor⟩, ResourceBirthCodec.rootBytes (shardBytes page)⟩ ::
              tail.references,
            { cellId := cursor, expectedPreRoot := CellSlot.root registry .absent,
              cell := shardCell page } :: tail.auxiliaryCreates⟩

def placedCatalogue (old : Catalogue) (placement : Placement) : Catalogue :=
  ⟨old.domain, old.revision + 1, placement.references⟩

def shardWrite (reference : Ref) (page : Page) : DataWrite where
  cellId := reference.cellId
  expectedPre := reference.physicalRoot
  exactPost := ResourceBirthCodec.rootBytes (shardBytes page)
  canonicalPostBytes := shardBytes page

def existingWrites (physical : PhysicalSnapshot) (old : Catalogue) (posts : List Page) :
    List DataWrite :=
  posts.filterMap fun page => do
    let reference ← old.pages.find? (fun reference => reference.number = page.pageNumber)
    if shardBytes page = physical.canonicalBytes reference.cellId then none
    else some (shardWrite reference page)

def catalogueWrite (anchor : Anchor) (physical : PhysicalSnapshot) (post : Catalogue) :
    DataWrite where
  cellId := anchor.catalogueCellId
  expectedPre := physical.model.roots anchor.catalogueCellId
  exactPost := ResourceBirthCodec.rootBytes (catalogueBytes post)
  canonicalPostBytes := catalogueBytes post

def planWrites (anchor : Anchor) (physical : PhysicalSnapshot) (old : Catalogue)
    (posts : List Page) (placement : Placement) : List DataWrite :=
  existingWrites physical old posts ++ [catalogueWrite anchor physical (placedCatalogue old placement)]

theorem planWrites_roots_bound (anchor : Anchor) (physical : PhysicalSnapshot)
    (old : Catalogue) (posts : List Page) (placement : Placement)
    (write : DataWrite) (member : write ∈ planWrites anchor physical old posts placement) :
    ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with shard | catalogue
  · obtain ⟨page, _, selected⟩ := List.mem_filterMap.mp shard
    unfold existingWrites at shard
    cases found : old.pages.find? (fun reference => reference.number = page.pageNumber) with
    | none => simp [found] at selected
    | some reference =>
        simp only [found, bind, Option.bind] at selected
        split at selected
        next => contradiction
        next => cases Option.some.inj selected; rfl
  · have same : write = catalogueWrite anchor physical (placedCatalogue old placement) := by
      simpa using catalogue
    subst write
    rfl

def Placement.Fresh {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (directory : LoadedDirectory durable) (requestedUserIds : List Nat)
    (placement : Placement) : Prop :=
  (placement.auxiliaryCreates.map (fun request => request.cellId)).Nodup ∧
    (∀ request ∈ placement.auxiliaryCreates,
      request.cellId ∉ directory.directory.used ∧ request.cellId ∉ requestedUserIds)

instance placementFreshDecidable {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (directory : LoadedDirectory durable) (requestedUserIds : List Nat) (placement : Placement) :
    Decidable (placement.Fresh directory requestedUserIds) := by
  unfold Placement.Fresh
  infer_instance

def readonlyGuards (guards : List ReadGuard) (writes : List DataWrite) : List ReadGuard :=
  guards.filter fun guard => guard.cellId ∉ writes.map DataWrite.cellId

/-- Every post shard is represented by an exact old-cell write, an exact
derived internal create, or unchanged bytes with a retained read guard.
Root equality alone is deliberately insufficient at this refinement seam. -/
def PostPageRepresented (physical : PhysicalSnapshot) (writes : List DataWrite)
    (guards : List ReadGuard) (creates : List (CreateRequest (CellId := Nat) registry))
    (reference : Ref) (page : Page) : Prop :=
  reference.physicalRoot = ResourceBirthCodec.rootBytes (shardBytes page) ∧
    ((∃ write ∈ writes, write.cellId = reference.cellId ∧
        write.canonicalPostBytes = shardBytes page) ∨
      (∃ request ∈ creates, (⟨request.cellId⟩ : Digest) = reference.cellId ∧
        LifecycleImage.bytes registry (.live request.cell) = shardBytes page) ∨
      (physical.canonicalBytes reference.cellId = shardBytes page ∧
        ∃ guard ∈ guards, guard.cellId = reference.cellId))

instance postPageRepresentedDecidable (physical : PhysicalSnapshot) (writes : List DataWrite)
    (guards : List ReadGuard) (creates : List (CreateRequest (CellId := Nat) registry))
    (reference : Ref) (page : Page) :
    Decidable (PostPageRepresented physical writes guards creates reference page) := by
  unfold PostPageRepresented
  infer_instance

/-- All data are source-computed. The final shape check also ensures there
is exactly one physical write per cell and no internal create aliases the
fixed catalogue anchor. The birth controller must compare its descriptor's
auxiliary creates byte-for-byte with `placement.auxiliaryCreates`. -/
structure Lowered {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} (directory : LoadedDirectory durable)
    (loaded : Loaded anchor durable.snapshot) (edits : List Edit)
    (prepared : Prepared loaded.snapshot edits) (requestedUserIds : List Nat) where
  private mk ::
  placement : Placement
  placementExact : placement = placePages loaded.snapshot.catalogue prepared.postPages
    (directory.freshCursor requestedUserIds)
  fresh : placement.Fresh directory requestedUserIds
  post : CredentialAuthorityDomain.Snapshot
  postCatalogue : post.catalogue = placedCatalogue loaded.snapshot.catalogue placement
  postPages : post.pages = prepared.postPages
  writesUnique : ((planWrites anchor durable.snapshot loaded.snapshot.catalogue
    prepared.postPages placement).map DataWrite.cellId).Nodup
  createsAvoidAnchor : ∀ request ∈ placement.auxiliaryCreates,
    (⟨request.cellId⟩ : Digest) ≠ anchor.catalogueCellId
  createsDisjointWrites : ∀ request ∈ placement.auxiliaryCreates,
    (⟨request.cellId⟩ : Digest) ∉
      (planWrites anchor durable.snapshot loaded.snapshot.catalogue
        prepared.postPages placement).map DataWrite.cellId
  writePreExact : ∀ write ∈ planWrites anchor durable.snapshot loaded.snapshot.catalogue
      prepared.postPages placement,
    write.expectedPre = durable.snapshot.model.roots write.cellId
  represented : List.Forall₂
    (PostPageRepresented durable.snapshot
      (planWrites anchor durable.snapshot loaded.snapshot.catalogue prepared.postPages placement)
      (readonlyGuards loaded.readGuards
        (planWrites anchor durable.snapshot loaded.snapshot.catalogue prepared.postPages placement))
      placement.auxiliaryCreates) post.catalogue.pages post.pages

def Lowered.writes {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds) : List DataWrite :=
  planWrites anchor durable.snapshot loaded.snapshot.catalogue prepared.postPages lowered.placement

def Lowered.readGuards {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds) : List ReadGuard :=
  readonlyGuards loaded.readGuards lowered.writes

private theorem assemble_parts {catalogue : Catalogue} {pages : List Page}
    {snapshot : CredentialAuthorityDomain.Snapshot}
    (assembled : assemble catalogue pages = some snapshot) :
    snapshot.catalogue = catalogue ∧ snapshot.pages = pages := by
  unfold assemble at assembled
  split at assembled
  next => cases Option.some.inj assembled; exact ⟨rfl, rfl⟩
  next => contradiction

def lower {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} (directory : LoadedDirectory durable)
    (loaded : Loaded anchor durable.snapshot) {edits : List Edit}
    (prepared : Prepared loaded.snapshot edits) (requestedUserIds : List Nat) :
    Option (Lowered directory loaded edits prepared requestedUserIds) := do
  let placement := placePages loaded.snapshot.catalogue prepared.postPages
    (directory.freshCursor requestedUserIds)
  if fresh : placement.Fresh directory requestedUserIds then
    match assembled : assemble (placedCatalogue loaded.snapshot.catalogue placement)
        prepared.postPages with
    | none => none
    | some post =>
        let writes := planWrites anchor durable.snapshot loaded.snapshot.catalogue
          prepared.postPages placement
        if shape : (writes.map DataWrite.cellId).Nodup ∧
            (∀ request ∈ placement.auxiliaryCreates,
              (⟨request.cellId⟩ : Digest) ≠ anchor.catalogueCellId) ∧
            (∀ request ∈ placement.auxiliaryCreates,
              (⟨request.cellId⟩ : Digest) ∉ writes.map DataWrite.cellId) ∧
            (∀ write ∈ writes,
              write.expectedPre = durable.snapshot.model.roots write.cellId) then
          if represented : List.Forall₂
              (PostPageRepresented durable.snapshot writes
                (readonlyGuards loaded.readGuards writes) placement.auxiliaryCreates)
              post.catalogue.pages post.pages then
            some ⟨placement, rfl, fresh, post, (assemble_parts assembled).1,
              (assemble_parts assembled).2, shape.1, shape.2.1, shape.2.2.1,
              shape.2.2.2, represented⟩
          else none
        else none
  else none

theorem Lowered.projection_exact
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds) :
    lowered.post.logical = prepared.validated.apply.logical := by
  change logicalOfPages lowered.post.pages = _
  rw [lowered.postPages]
  exact prepared.projectionExact

theorem Lowered.readGuards_readonly
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds)
    (guard : ReadGuard) (member : guard ∈ lowered.readGuards) :
    guard.cellId ∉ lowered.writes.map DataWrite.cellId := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem Lowered.every_read_covered
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds)
    (guard : ReadGuard) (member : guard ∈ loaded.readGuards) :
    guard.cellId ∈ lowered.writes.map DataWrite.cellId ∨ guard ∈ lowered.readGuards := by
  by_cases written : guard.cellId ∈ lowered.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_filter.mpr ⟨member, by simpa using written⟩)

theorem Lowered.readGuards_exact
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {anchor : Anchor} {directory : LoadedDirectory durable}
    {loaded : Loaded anchor durable.snapshot} {edits : List Edit}
    {prepared : Prepared loaded.snapshot edits} {requestedUserIds : List Nat}
    (lowered : Lowered directory loaded edits prepared requestedUserIds)
    (guard : ReadGuard) (member : guard ∈ lowered.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId :=
  loaded.readGuards_exact guard (List.mem_filter.mp member).1

/-! ## Concrete preparation of the existing root-issuance batch -/

def issuanceKeys (grants : List AuthorityGrant) : Finset RevocationKey :=
  (grants.map fun grant => RevocationKey.capability grant.capability.head.id).toFinset

def issueUniverse (snapshot : CredentialAuthorityDomain.Snapshot) (grants : List AuthorityGrant) :
    ProjectionUniverse := snapshot.extendedUniverse (issuanceKeys grants)

theorem issueUniverse_authState_exact (snapshot : CredentialAuthorityDomain.Snapshot)
    (grants : List AuthorityGrant) :
    CredentialAuthorityState.authState (issueUniverse snapshot grants) snapshot.cell =
      snapshot.authState := snapshot.authState_extension_exact (issuanceKeys grants)

def GrantReady (snapshot : CredentialAuthorityDomain.Snapshot) (grant : AuthorityGrant) : Prop :=
  grant.capability.ancestry = [] ∧
    CredentialAuthorityState.readCapability snapshot.cell grant.kind grant.capability.head.id = none ∧
    grant.capability.head.parent = none ∧
    grant.capability.head.root = grant.capability.head.id ∧
    grant.capability.head.ancestors = ∅ ∧
    grant.capability.head.issuerEpoch = issuerEpochAt snapshot.cell grant.capability.head.issuer ∧
    grant.capability.head.policyEpoch = policyEpochAt snapshot.cell grant.capability.head.policyId ∧
    isRevoked snapshot.cell (.capability grant.capability.head.id) = false ∧
    (∀ channel ∈ grant.capability.head.channels,
      RevocationKey.channel channel ∈ snapshot.revocationUniverse.revocationKeys ∧
      isRevoked snapshot.cell (.channel channel) = false)

instance grantReadyDecidable (snapshot : CredentialAuthorityDomain.Snapshot) (grant : AuthorityGrant) :
    Decidable (GrantReady snapshot grant) := by
  unfold GrantReady
  infer_instance

def BatchReady (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) : Prop :=
  ((ResourceBirthAuthority.fieldWrites descriptor).map FieldWrite.field).Nodup ∧
    descriptor.GrantIdsDistinct ∧
    (∀ policy ∈ descriptor.initialPolicies,
      snapshot.logical.fields (.policyEpoch policy.policyId) = none ∧
        snapshot.logical.fields (.policyAddress policy.policyId 0) = none) ∧
    isNullified snapshot.cell descriptor.authorityNullifier = false ∧
    (∀ grant ∈ descriptor.grants, GrantReady snapshot grant)

instance batchReadyDecidable (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) : Decidable (BatchReady snapshot descriptor) := by
  unfold BatchReady Descriptor.GrantIdsDistinct
  infer_instance

def batchEvidence (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) (ready : BatchReady snapshot descriptor) :
    ResourceBirthAuthority.BatchEvidence (issueUniverse snapshot descriptor.grants)
      snapshot.cell descriptor where
  slotsDistinct := ready.1
  policiesFresh := ready.2.2.1
  nullifierFresh := ready.2.2.2.1
  ancestryEmpty := fun grant member => (ready.2.2.2.2 grant member).1
  issue := fun grant member => by
    obtain ⟨_, slot, parent, root, ancestors, issuer, policy, self, channels⟩ :=
      ready.2.2.2.2 grant member
    exact
      { preRootExact := rfl
        slotFresh := slot
        nullifierFresh := ready.2.2.2.1
        rootParent := parent
        rootSelf := root
        rootAncestors := ancestors
        issuerCurrent := issuer
        policyCurrent := policy
        selfRegistered := Finset.mem_union_right _
          (List.mem_toFinset.mpr (List.mem_map.mpr ⟨grant, member, rfl⟩))
        channelsRegistered := fun channel channelMember =>
          Finset.mem_union_left _ (channels channel channelMember).1
        selfLive := self
        channelsLive := fun channel channelMember => (channels channel channelMember).2 }

def grantEdits (snapshot : CredentialAuthorityDomain.Snapshot) (descriptor : Descriptor registry) :
    List Edit :=
  descriptor.initialPolicies.map (fun policy => ⟨none, .policy policy.policyId 0 policy.address⟩) ++
  descriptor.grants.map (fun grant => ⟨none, .capability grant.kind grant.capability⟩) ++
    [nullifierEdit snapshot descriptor.authorityNullifier]

def requestedUserIds (descriptor : Descriptor registry) : List Nat :=
  descriptor.births.map fun item => item.create.cellId

/-- Source-cell identities are known from canonical initial-policy addresses
before the final descriptor commitment. Authority allocation must skip them. -/
def allocationReservedIds (deployment : CanonicalCellRegistry.Deployment)
    (descriptor : Descriptor registry) : List Nat :=
  requestedUserIds descriptor ++
    PolicySourceCell.initialIds deployment.domain descriptor.initialPolicies

/-- The deployment fixes the anchor. This constructor prepares effects before
factory/policy authorization. New grants are never used to authorize their
own birth, and the full semantic family has its own old-domain-root request.
The enclosing controller must enforce exact auxiliary-create equality before
authorizing the final complete descriptor. -/
structure PreparedGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (directory : LoadedDirectory durable)
    (loaded : Loaded deployment.authorityAnchor durable.snapshot)
    (descriptor : Descriptor registry) where
  private mk ::
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile descriptor.initialPolicies
  mode : ResourceBirthAuthority.BatchEvidence (issueUniverse loaded.snapshot descriptor.grants)
    loaded.snapshot.cell descriptor
  prepared : Prepared loaded.snapshot (grantEdits loaded.snapshot descriptor)
  physical : Lowered directory loaded (grantEdits loaded.snapshot descriptor) prepared
    (allocationReservedIds deployment descriptor)
  semanticExact : physical.post.logical =
    (ResourceBirthAuthority.post loaded.snapshot.cell descriptor).logical

def prepareGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (directory : LoadedDirectory durable)
    (loaded : Loaded deployment.authorityAnchor durable.snapshot)
    (descriptor : Descriptor registry) :
    Option (PreparedGrantBatch profile deployment directory loaded descriptor) := do
  let initialSources ← PolicySourceCell.checkInitials deployment.domain profile descriptor.initialPolicies
  if ready : BatchReady loaded.snapshot descriptor then
    let prepared ← prepare loaded.snapshot (grantEdits loaded.snapshot descriptor)
    let physical ← lower directory loaded prepared (allocationReservedIds deployment descriptor)
    if same : CredentialAuthorityStateCodec.encode physical.post.logical =
        CredentialAuthorityStateCodec.encode
          (ResourceBirthAuthority.post loaded.snapshot.cell descriptor).logical then
      some ⟨initialSources, batchEvidence loaded.snapshot descriptor ready, prepared, physical,
        CredentialAuthorityStateCodec.encode_injective same⟩
    else none
  else none

def PreparedGrantBatch.auxiliaryCreates {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {directory : LoadedDirectory durable}
    {loaded : Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor registry}
    (prepared : PreparedGrantBatch profile deployment directory loaded descriptor) :
    List (CreateRequest (CellId := Nat) registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records ++
    prepared.physical.placement.auxiliaryCreates

theorem PreparedGrantBatch.post_exact {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {directory : LoadedDirectory durable}
    {loaded : Loaded deployment.authorityAnchor durable.snapshot}
    {descriptor : Descriptor registry}
    (prepared : PreparedGrantBatch profile deployment directory loaded descriptor) :
    prepared.physical.post.cell = ResourceBirthAuthority.post loaded.snapshot.cell descriptor :=
  Materialized.ext prepared.semanticExact

def loadDeployment (deployment : CanonicalCellRegistry.Deployment)
    (physical : PhysicalSnapshot) : Option (Loaded deployment.authorityAnchor physical) :=
  if deployment.Valid then load deployment.authorityAnchor physical else none

end Minidregg.Compiler.CredentialAuthorityDomainReceiver
