/-
# Compiler.CredentialAuthorityDomainReceiver -- the one authority cell, loaded and written

The receiving deployment pins one authority cell (`authorityCellId`).  `load`
decodes exactly that cell from one durable snapshot as the registry's
`.authority` role and pairs it with the deployment's domain.  No request
supplies a cell, a page subset, a decoder or a root function.

An authority update is one validated patch of that cell.  Its physical
representation is one `DataWrite`: the post cell's canonical bytes, guarded at
the snapshot's root of the same cell.  There is no catalogue to rewrite, no
shard to place and no auxiliary create; the write is a function of the post
cell's logical content alone (`write_of_planes`).
-/
import Compiler.CanonicalCellRegistry
import Compiler.CredentialAuthorityDomain
import Compiler.DurableReceiverIO
import Theory.ResourceBirthAuthority

namespace Minidregg.Compiler.CredentialAuthorityDomainReceiver

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev PhysicalSnapshot := DataSnapshot ResourceBirthCodec.rootBytes
abbrev Deployment := CanonicalCellRegistry.Deployment

/-- The durable identifier of the deployment's one authority cell. -/
def cellIdOf (deployment : Deployment) : CellId := ⟨deployment.authorityCellId⟩

def packedCell (cell : CredentialAuthorityDomain.Cell) : PackedCell registry := ⟨.authority, cell⟩

/-- The lifecycle bytes of a live authority cell. -/
def cellBytes (cell : CredentialAuthorityDomain.Cell) : List UInt8 :=
  LifecycleImage.bytes registry (.live (packedCell cell))

def cellRoot (cell : CredentialAuthorityDomain.Cell) : Digest :=
  ResourceBirthCodec.rootBytes (cellBytes cell)

/-- Decode a live cell of the authority role; any other role, a retired or a
fresh image, and non-canonical bytes are refused. -/
def decodeCell (bytes : List UInt8) : Option CredentialAuthorityDomain.Cell :=
  match (LifecycleImage.codec registry).decode bytes with
  | some (.live ⟨.authority, payload⟩) => some payload
  | _ => none

theorem decodeCell_bytes (cell : CredentialAuthorityDomain.Cell) :
    decodeCell (cellBytes cell) = some cell := by
  unfold decodeCell cellBytes
  rw [show LifecycleImage.bytes registry (.live (packedCell cell)) =
      (LifecycleImage.codec registry).encode (.live (packedCell cell)) from rfl,
    LifecycleImage.decode_encode]
  rfl

theorem decodeCell_canonical {bytes : List UInt8} {cell : CredentialAuthorityDomain.Cell}
    (decoded : decodeCell bytes = some cell) : cellBytes cell = bytes := by
  unfold decodeCell at decoded
  split at decoded
  · rename_i payload image
    cases Option.some.inj decoded
    exact LifecycleImage.decode_canonical registry image
  · cases decoded

/-- The loaded authority domain.  The constructor is private: `load` is the
only route, so the snapshot is exactly the cell at the pinned identifier of one
physical snapshot, read in the deployment's domain. -/
structure Loaded (deployment : Deployment) (physical : PhysicalSnapshot) where
  private mk ::
  snapshot : CredentialAuthorityDomain.Snapshot
  valid : deployment.Valid
  domainExact : snapshot.domain = deployment.domain
  observed : physical.canonicalBytes (cellIdOf deployment) = cellBytes snapshot.cell

def loadDeployment (deployment : Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  if valid : deployment.Valid then
    match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell =>
        some ⟨⟨deployment.domain, cell⟩, valid, rfl, (decodeCell_canonical decoded).symm⟩
  else none

/-- Refuting pole: a pinned identifier that does not hold a live authority cell
(a retired image, a fresh slot, another role, or a retired catalogue frame)
loads nothing. -/
theorem loadDeployment_refuses (deployment : Deployment) (physical : PhysicalSnapshot)
    (undecodable : decodeCell (physical.canonicalBytes (cellIdOf deployment)) = none) :
    loadDeployment deployment physical = none := by
  unfold loadDeployment
  split
  · split
    · rfl
    · rename_i cell decoded
      rw [undecodable] at decoded
      cases decoded
  · rfl

/-- Satisfiable pole: the cell the physical snapshot holds is loaded exactly. -/
theorem loadDeployment_exact (deployment : Deployment) (physical : PhysicalSnapshot)
    (valid : deployment.Valid) (cell : CredentialAuthorityDomain.Cell)
    (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell) :
    ∃ loaded, loadDeployment deployment physical = some loaded ∧ loaded.snapshot.cell = cell := by
  unfold loadDeployment
  rw [dif_pos valid]
  split
  · rename_i decoded
    rw [holds, decodeCell_bytes] at decoded
    cases decoded
  · rename_i found decoded
    rw [holds, decodeCell_bytes] at decoded
    exact ⟨_, rfl, (Option.some.inj decoded).symm⟩

theorem Loaded.root_exact {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) :
    cellRoot loaded.snapshot.cell = physical.model.roots (cellIdOf deployment) := by
  unfold cellRoot
  rw [← loaded.observed]
  exact physical.coherent _

/-- The loaded cell satisfies the registry's own law for the authority role. -/
theorem Loaded.cellLaw {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) :
    CanonicalCellRegistry.CellLaw deployment deployment.authorityCellId
      (packedCell loaded.snapshot.cell) :=
  ⟨loaded.valid, rfl⟩

/-- The one read dependency of the authority domain. -/
def Loaded.readGuard {deployment : Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) : ReadGuard :=
  { cellId := cellIdOf deployment, expectedRoot := physical.model.roots (cellIdOf deployment) }

def Loaded.readGuards {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) : List ReadGuard := [loaded.readGuard]

theorem Loaded.readGuards_exact {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (guard : ReadGuard) (member : guard ∈ loaded.readGuards) :
    guard.expectedRoot = physical.model.roots guard.cellId := by
  simp only [Loaded.readGuards, List.mem_singleton] at member
  subst guard
  rfl

/-! ## The one physical write of an authority update -/

/-- The post cell, written at the pinned identifier and guarded at the loaded
root of that same cell. -/
def Loaded.write {deployment : Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) : DataWrite where
  cellId := cellIdOf deployment
  expectedPre := physical.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

def Loaded.writes {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) : List DataWrite :=
  [loaded.write post]

theorem Loaded.write_root_bound {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    ResourceBirthCodec.rootBytes (loaded.write post).canonicalPostBytes = (loaded.write post).exactPost :=
  rfl

theorem Loaded.write_pre_exact {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.write post).expectedPre = physical.model.roots (loaded.write post).cellId :=
  rfl

/-- The write's guard is the loaded cell's own root: an authority write
cannot be applied over any other authority state. -/
theorem Loaded.write_pre_is_loaded_root {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.write post).expectedPre = cellRoot loaded.snapshot.cell :=
  loaded.root_exact.symm

/-- The write reads back as exactly the post cell. -/
theorem Loaded.write_decodes {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    decodeCell (loaded.write post).canonicalPostBytes = some post :=
  decodeCell_bytes post

/-- **The authority root is a function of the planes' logical content.**  Two
post cells that agree at every authority address produce the same physical
write: the same bytes, the same root, at the same identifier, under the same
guard.  No catalogue revision, placement cursor or shard numbering enters it,
so an update rewrites exactly one cell and nothing else. -/
theorem write_of_planes {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (left right : CredentialAuthorityDomain.Cell)
    (planes : ∀ address, left.logical address = right.logical address) :
    loaded.write left = loaded.write right := by
  have same : left = right := Materialized.ext (DFinsupp.ext planes)
  rw [same]

theorem cellRoot_of_planes (left right : CredentialAuthorityDomain.Cell)
    (planes : ∀ address, left.logical address = right.logical address) :
    cellRoot left = cellRoot right := by
  rw [Materialized.ext (DFinsupp.ext planes)]

theorem Loaded.writes_single {deployment : Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.writes post).map DataWrite.cellId = [cellIdOf deployment] := rfl

/-! ## One complete physical directory, including retired identities -/

def directoryRows (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    List (Nat × List UInt8) :=
  durable.cells.map fun row => (row.1.value, row.2)

/-- The finite support comes from the complete replayed durable image. A
request cannot supply a reduced directory or discard tombstones. The only
absent lifecycle representation is `[]`. -/
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

/-- Global exactness, including identities outside the finite support. -/
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

/-! ## Concrete preparation of the root-issuance batch -/

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
    CapabilityIdFresh snapshot.cell grant.capability.head.id ∧
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

def policyFresh (snapshot : CredentialAuthorityDomain.Snapshot) (policy : InitialPolicy) : Prop :=
  generationAt? snapshot.logical policy.policyId = none ∧
    revisionAt? snapshot.logical policy.policyId = none ∧
    addressAt? snapshot.logical policy.policyId 0 = none

instance policyFreshDecidable (snapshot : CredentialAuthorityDomain.Snapshot) (policy : InitialPolicy) :
    Decidable (policyFresh snapshot policy) := by
  unfold policyFresh
  infer_instance

def BatchReady (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) : Prop :=
  ((ResourceBirthAuthority.entries descriptor).map Sigma.fst).Nodup ∧
    descriptor.GrantIdsDistinct ∧
    (∀ policy ∈ descriptor.initialPolicies, policyFresh snapshot policy) ∧
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
  grantIdsDistinct := ready.2.1
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

/-- The deployment fixes the authority cell. This prepares the batch before
factory/policy authorization. New grants are never used to authorize their own
birth. The post is the batch patch applied to the loaded cell; its one write
replaces that cell. -/
structure PreparedGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : Deployment) (loaded : Loaded deployment durable.snapshot)
    (descriptor : Descriptor registry) where
  private mk ::
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile descriptor.initialPolicies
  mode : ResourceBirthAuthority.BatchEvidence (issueUniverse loaded.snapshot descriptor.grants)
    loaded.snapshot.cell descriptor

def prepareGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : Deployment) (loaded : Loaded deployment durable.snapshot)
    (descriptor : Descriptor registry) :
    Option (PreparedGrantBatch profile deployment loaded descriptor) := do
  let initialSources ← PolicySourceCell.checkInitials deployment.domain profile descriptor.initialPolicies
  if ready : BatchReady loaded.snapshot descriptor then
    some ⟨initialSources, batchEvidence loaded.snapshot descriptor ready⟩
  else none

section GrantBatch

variable {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : Deployment} {loaded : Loaded deployment durable.snapshot}
    {descriptor : Descriptor registry}

def PreparedGrantBatch.post (prepared : PreparedGrantBatch profile deployment loaded descriptor) :
    CredentialAuthorityDomain.Cell :=
  ResourceBirthAuthority.post loaded.snapshot.cell descriptor prepared.mode.nullifierFresh

def PreparedGrantBatch.writes (prepared : PreparedGrantBatch profile deployment loaded descriptor) :
    List DataWrite :=
  loaded.writes prepared.post

def PreparedGrantBatch.auxiliaryCreates
    (prepared : PreparedGrantBatch profile deployment loaded descriptor) :
    List (CreateRequest (CellId := Nat) registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records

theorem PreparedGrantBatch.post_logical
    (prepared : PreparedGrantBatch profile deployment loaded descriptor) :
    prepared.post.logical = setAll loaded.snapshot.logical (ResourceBirthAuthority.entries descriptor) :=
  ResourceBirthAuthority.post_logical _ _ _

end GrantBatch

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.write_of_planes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_of_planes
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.loadDeployment_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadDeployment_refuses
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.loadDeployment_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadDeployment_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded.write_pre_is_loaded_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.write_pre_is_loaded_root

end Minidregg.Compiler.CredentialAuthorityDomainReceiver
