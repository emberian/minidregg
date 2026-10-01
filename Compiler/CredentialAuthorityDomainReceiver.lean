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
import Compiler.CredentialAuthorityReplay
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

/-- The durable identifier of the deployment's one authority cell. -/
def cellIdOf (deployment : CanonicalCellRegistry.Deployment) : CellId := ⟨deployment.authorityCellId⟩

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

/-! ## The authority clock and the spent markers are durable system state

Operation nullifiers are not authority-cell state.  Every authority receiver
puts its operation marker into its intent's `nullifiers` as
`CredentialAuthorityReplay.nullifier domain marker`, and the durable protocol
installs it into its append-only consumed set and refuses a second use
(`DataIntent.consumed_nullifier_refused`).  The authority clock is the durable
height: every installation appends exactly one history event
(`clockOf_install`). -/

/-- The authority clock of a physical snapshot: its accepted-record count. -/
def clockOf (physical : PhysicalSnapshot) : Nat := physical.model.history.length

/-- Whether an authority operation marker is consumed in the durable set. -/
def spentOf (domain : Digest) (physical : PhysicalSnapshot) (marker : Nat) : Bool :=
  physical.model.consumed (CredentialAuthorityReplay.nullifier domain marker)

/-- Every accepted record advances the clock by exactly one. -/
theorem clockOf_install (physical : PhysicalSnapshot)
    (intent : DataIntent ResourceBirthCodec.rootBytes) :
    clockOf (DataSnapshot.install physical intent) = clockOf physical + 1 := by
  simp [clockOf, DataSnapshot.install_model, Minidregg.Kernel.DurableCommitProtocol.Snapshot.install_history]

/-- Satisfiable pole: installing an intent that carries a marker's replay key
marks it spent. -/
theorem spentOf_install (domain : Digest) (physical : PhysicalSnapshot)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (marker : Nat)
    (carries : CredentialAuthorityReplay.nullifier domain marker ∈ intent.nullifiers) :
    spentOf domain (DataSnapshot.install physical intent) marker = true := by
  unfold spentOf
  rw [DataSnapshot.install_model]
  exact Minidregg.Kernel.DurableCommitProtocol.Snapshot.install_consumes _ _ _ (by simpa using carries)

/-- Refuting pole: an intent carrying a spent marker's replay key never passes
preflight, whatever else it carries. -/
theorem spent_marker_refused (domain : Digest) (physical : PhysicalSnapshot)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (marker : Nat)
    (carries : CredentialAuthorityReplay.nullifier domain marker ∈ intent.nullifiers)
    (spent : spentOf domain physical marker = true) :
    intent.preflight physical ≠ .ok () :=
  DataIntent.consumed_nullifier_refused physical intent _ carries spent

/-- The loaded authority domain.  The constructor is private: `load` is the
only route, so the snapshot is exactly the cell at the pinned identifier of one
physical snapshot, read in the deployment's domain, with the clock and spent
markers of that same physical snapshot. -/
structure Loaded (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) where
  private mk ::
  snapshot : CredentialAuthorityDomain.Snapshot
  valid : deployment.Valid
  domainExact : snapshot.domain = deployment.domain
  revisionExact : snapshot.revision = clockOf physical
  spentExact : snapshot.spent = spentOf deployment.domain physical
  observed : physical.canonicalBytes (cellIdOf deployment) = cellBytes snapshot.cell

def loadDeployment (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  if valid : deployment.Valid then
    match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell =>
        some ⟨Snapshot.ofCell deployment.domain (clockOf physical)
            (spentOf deployment.domain physical) cell, valid, rfl, rfl, rfl,
          (decodeCell_canonical decoded).symm⟩
  else none

/-- Refuting pole: a pinned identifier that does not hold a live authority cell
(a retired image, a fresh slot, another role, or a retired catalogue frame)
loads nothing. -/
theorem loadDeployment_refuses (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
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
theorem loadDeployment_exact (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
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

/-- Two loads of the same deployment from the same physical snapshot are the
same authority snapshot: the pinned cell's bytes determine it. -/
theorem Loaded.snapshot_unique {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (left right : Loaded deployment physical) :
    left.snapshot = right.snapshot := by
  have cells : left.snapshot.cell = right.snapshot.cell := by
    have decoded := decodeCell_bytes left.snapshot.cell
    rw [← left.observed, right.observed, decodeCell_bytes] at decoded
    exact (Option.some.inj decoded).symm
  exact CredentialAuthorityDomain.Snapshot.ext_cell
    (left.domainExact.trans right.domainExact.symm)
    (left.revisionExact.trans right.revisionExact.symm)
    (left.spentExact.trans right.spentExact.symm) cells

theorem Loaded.root_exact {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) :
    cellRoot loaded.snapshot.cell = physical.model.roots (cellIdOf deployment) := by
  unfold cellRoot
  rw [← loaded.observed]
  exact physical.coherent _

/-- The loaded cell satisfies the registry's own law for the authority role. -/
theorem Loaded.cellLaw {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) :
    CanonicalCellRegistry.CellLaw deployment deployment.authorityCellId
      (packedCell loaded.snapshot.cell) :=
  ⟨loaded.valid, rfl⟩

/-- The one read dependency of the authority domain. -/
def Loaded.readGuard {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) : ReadGuard :=
  { cellId := cellIdOf deployment, expectedRoot := physical.model.roots (cellIdOf deployment) }

def Loaded.readGuards {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) : List ReadGuard := [loaded.readGuard]

theorem Loaded.readGuards_exact {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (guard : ReadGuard) (member : guard ∈ loaded.readGuards) :
    guard.expectedRoot = physical.model.roots guard.cellId := by
  simp only [Loaded.readGuards, List.mem_singleton] at member
  subst guard
  rfl

/-! ## The one physical write of an authority update -/

/-- The post cell, written at the pinned identifier and guarded at the loaded
root of that same cell. -/
def Loaded.write {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) : DataWrite where
  cellId := cellIdOf deployment
  expectedPre := physical.model.roots (cellIdOf deployment)
  exactPost := cellRoot post
  canonicalPostBytes := cellBytes post

def Loaded.writes {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) : List DataWrite :=
  [loaded.write post]

theorem Loaded.write_root_bound {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    ResourceBirthCodec.rootBytes (loaded.write post).canonicalPostBytes = (loaded.write post).exactPost :=
  rfl

theorem Loaded.write_pre_exact {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.write post).expectedPre = physical.model.roots (loaded.write post).cellId :=
  rfl

/-- The write's guard is the loaded cell's own root: an authority write
cannot be applied over any other authority state. -/
theorem Loaded.write_pre_is_loaded_root {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.write post).expectedPre = cellRoot loaded.snapshot.cell :=
  loaded.root_exact.symm

/-- The write reads back as exactly the post cell. -/
theorem Loaded.write_decodes {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    decodeCell (loaded.write post).canonicalPostBytes = some post :=
  decodeCell_bytes post

/-- **The authority root is a function of the planes' logical content.**  Two
post cells that agree at every authority address produce the same physical
write: the same bytes, the same root, at the same identifier, under the same
guard.  No catalogue revision, placement cursor or shard numbering enters it,
so an update rewrites exactly one cell and nothing else. -/
theorem write_of_planes {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (left right : CredentialAuthorityDomain.Cell)
    (planes : ∀ address, left.logical address = right.logical address) :
    loaded.write left = loaded.write right := by
  have same : left = right := Materialized.ext (DFinsupp.ext planes)
  rw [same]

theorem cellRoot_of_planes (left right : CredentialAuthorityDomain.Cell)
    (planes : ∀ address, left.logical address = right.logical address) :
    cellRoot left = cellRoot right := by
  rw [Materialized.ext (DFinsupp.ext planes)]

theorem Loaded.writes_single {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
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
    exact (Kernel.DurableCheckpoint.resume_outside_support ResourceBirthCodec.rootBytes
      durable.image durable.baseHeight durable.base durable.snapshot durable.resumed
      ⟨identifier⟩ outside).trans loaded.absentDefault |>.symm

/-! ## A held directory is the recomputation; an unchanged row is not decoded again

The Host holds one `LoadedDirectory` per served image (`NativeHost.Opened`).
These facts let every request read it instead of decoding every stored cell
again, and let a session advanced by new records decode only the rows whose
bytes moved. -/

/-- Two loaded directories of one image are equal: `decoded` fixes the
directory, so the one computed at open or at commit is the one any
recomputation returns. -/
theorem LoadedDirectory.unique {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (left right : LoadedDirectory durable) : left = right := by
  have same : left.directory = right.directory :=
    Option.some.inj (left.decoded.symm.trans right.decoded)
  cases left
  cases right
  simp only at same
  subst same
  rfl

/-- **A held directory is what `loadDirectory` would recompute** on the same image. -/
theorem LoadedDirectory.load_eq {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) : loadDirectory durable = some loaded := by
  cases computed : loadDirectory durable with
  | some other => exact congrArg some (LoadedDirectory.unique other loaded)
  | none =>
      exfalso
      unfold loadDirectory at computed
      rw [dif_pos loaded.absentDefault] at computed
      split at computed
      · rename_i missing
        rw [loaded.decoded] at missing
        cases missing
      · cases computed

/-- Two images whose canonical bytes agree at an identifier load the same slot there. -/
theorem LoadedDirectory.slots_eq_of_bytes
    {first second : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (left : LoadedDirectory first) (right : LoadedDirectory second) (identifier : Nat)
    (same : first.snapshot.canonicalBytes ⟨identifier⟩ =
      second.snapshot.canonicalBytes ⟨identifier⟩) :
    left.directory.slots identifier = right.directory.slots identifier := by
  have views : LifecycleImage.view registry left.directory identifier =
      LifecycleImage.view registry right.directory identifier := by
    have bytes := (left.bytes_exact identifier).trans
      (same.trans (right.bytes_exact identifier).symm)
    have decoded := congrArg (LifecycleImage.rawDecode registry) bytes
    rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at decoded
    exact Option.some.inj decoded
  rw [← LifecycleImage.view_slot registry left.directory identifier, views,
    LifecycleImage.view_slot]

/-- One directory row of a later image. When the identifier's canonical bytes
equal the held image's, the held directory's view of it is reused; otherwise the
bytes are decoded. `decodeRowFrom_eq`: both are what decoding the bytes returns. -/
def decodeRowFrom {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (identifier : Nat) (bytes : List UInt8) :
    Option (LifecycleImage registry) :=
  if prior.snapshot.canonicalBytes ⟨identifier⟩ == bytes then
    some (LifecycleImage.view registry held.directory identifier)
  else (LifecycleImage.codec registry).decode bytes

theorem decodeRowFrom_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (identifier : Nat) (bytes : List UInt8) :
    decodeRowFrom held identifier bytes = (LifecycleImage.codec registry).decode bytes := by
  unfold decodeRowFrom
  split
  next same =>
    have exact : LifecycleImage.bytes registry
        (LifecycleImage.view registry held.directory identifier) = bytes :=
      (held.bytes_exact identifier).trans (beq_iff_eq.mp same)
    rw [← exact]
    exact (LifecycleImage.decode_encode registry _).symm
  next => rfl

def decodeRowsFrom {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) :
    List (Nat × List UInt8) → Option (DirectoryImage.Rows registry)
  | [] => some []
  | (identifier, bytes) :: rest => do
      let image ← decodeRowFrom held identifier bytes
      let tail ← decodeRowsFrom held rest
      some ((identifier, image) :: tail)

theorem decodeRowsFrom_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) :
    ∀ input : List (Nat × List UInt8),
      decodeRowsFrom held input = DirectoryImage.decodeRows registry input
  | [] => rfl
  | (identifier, bytes) :: rest => by
      simp only [decodeRowsFrom, DirectoryImage.decodeRows, decodeRowFrom_eq,
        decodeRowsFrom_eq held rest]

def decodeFrom {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (input : List (Nat × List UInt8)) :
    Option (Directory Nat registry) := do
  let rows ← decodeRowsFrom held input
  if (rows.map Prod.fst).Nodup then some (DirectoryImage.ofRows registry rows) else none

theorem decodeFrom_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (input : List (Nat × List UInt8)) :
    decodeFrom held input = DirectoryImage.decode registry input := by
  simp only [decodeFrom, DirectoryImage.decode, decodeRowsFrom_eq]

/-- `loadDirectory` of a later image, decoding only the rows whose bytes differ
from `held`'s image (`loadDirectoryFrom_eq`). -/
def loadDirectoryFrom {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    Option (LoadedDirectory durable) :=
  if absentDefault : durable.image.seed.absentBytes = [] then
    match decoded : decodeFrom held (directoryRows durable) with
    | none => none
    | some directory =>
        some ⟨directory, (decodeFrom_eq held (directoryRows durable)).symm.trans decoded,
          absentDefault⟩
  else none

/-- **The incremental load is the full load**: same refusal, same directory. -/
theorem loadDirectoryFrom_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    loadDirectoryFrom held durable = loadDirectory durable := by
  cases computed : loadDirectory durable with
  | some loaded =>
      cases incremental : loadDirectoryFrom held durable with
      | some other => exact congrArg some (LoadedDirectory.unique other loaded)
      | none =>
          exfalso
          unfold loadDirectoryFrom at incremental
          rw [dif_pos loaded.absentDefault] at incremental
          split at incremental
          · rename_i missing
            rw [decodeFrom_eq, loaded.decoded] at missing
            cases missing
          · cases incremental
  | none =>
      cases incremental : loadDirectoryFrom held durable with
      | none => rfl
      | some other =>
          exfalso
          rw [LoadedDirectory.load_eq other] at computed
          cases computed

/-! ## Concrete preparation of the root-issuance batch -/

/-- A grant is ready at the loaded cell when it is a fresh root whose own key
is not yet registered (the birth registers it) and not revoked, and every
channel it names is already registered and live; each read is a presence-plane
read of the one cell. -/
def GrantReady (snapshot : CredentialAuthorityDomain.Snapshot) (grant : AuthorityGrant) : Prop :=
  grant.capability.ancestry = [] ∧
    CapabilityIdFresh snapshot.cell grant.capability.head.id ∧
    grant.capability.head.parent = none ∧
    grant.capability.head.root = grant.capability.head.id ∧
    grant.capability.head.ancestors = ∅ ∧
    grant.capability.head.issuerEpoch = issuerEpochAt snapshot.cell grant.capability.head.issuer ∧
    grant.capability.head.policyEpoch = policyEpochAt snapshot.cell grant.capability.head.policyId ∧
    isRegistered snapshot.cell (.capability grant.capability.head.id) = false ∧
    isRevoked snapshot.cell (.capability grant.capability.head.id) = false ∧
    (∀ channel ∈ grant.capability.head.channels,
      isRegistered snapshot.cell (.channel channel) = true ∧
      isRevoked snapshot.cell (.channel channel) = false)

instance grantReadyDecidable (snapshot : CredentialAuthorityDomain.Snapshot) (grant : AuthorityGrant) :
    Decidable (GrantReady snapshot grant) := by
  unfold GrantReady
  infer_instance

def policyFresh (snapshot : CredentialAuthorityDomain.Snapshot) (policy : InitialPolicy) : Prop :=
  (show Option Epoch from snapshot.logical ⟨.policyEpoch, policy.policyId⟩) = none ∧
    (show Option PolicyRevision from snapshot.logical ⟨.policyRevision, policy.policyId⟩) = none ∧
    (show Option Digest from snapshot.logical ⟨.policyAddress, (policy.policyId, 0)⟩) = none

instance policyFreshDecidable (snapshot : CredentialAuthorityDomain.Snapshot) (policy : InitialPolicy) :
    Decidable (policyFresh snapshot policy) := by
  unfold policyFresh
  infer_instance

def BatchReady (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) : Prop :=
  ((ResourceBirthAuthority.entries descriptor).map Sigma.fst).Nodup ∧
    descriptor.GrantIdsDistinct ∧
    (∀ policy ∈ descriptor.initialPolicies, policyFresh snapshot policy) ∧
    snapshot.spent descriptor.authorityNullifier = false ∧
    (∀ grant ∈ descriptor.grants, GrantReady snapshot grant) ∧
    (∀ row ∈ descriptor.parentRows, snapshot.cell.logical ⟨.parent, row.1⟩ = none)

instance batchReadyDecidable (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) : Decidable (BatchReady snapshot descriptor) := by
  unfold BatchReady Descriptor.GrantIdsDistinct
  infer_instance

def batchEvidence (snapshot : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) (ready : BatchReady snapshot descriptor) :
    ResourceBirthAuthority.BatchEvidence
      snapshot.cell descriptor where
  slotsDistinct := ready.1
  grantIdsDistinct := ready.2.1
  policiesFresh := ready.2.2.1
  ancestryEmpty := fun grant member => (ready.2.2.2.2.1 grant member).1
  parentsFresh := ready.2.2.2.2.2
  issue := fun grant member => by
    obtain ⟨_, slot, parent, root, ancestors, issuer, policy, unregistered, self, channels⟩ :=
      ready.2.2.2.2.1 grant member
    exact
      { preRootExact := rfl
        slotFresh := slot
        rootParent := parent
        rootSelf := root
        rootAncestors := ancestors
        issuerCurrent := issuer
        policyCurrent := policy
        selfUnregistered := unregistered
        channelsRegistered := fun channel channelMember => (channels channel channelMember).1
        selfLive := self
        channelsLive := fun channel channelMember => (channels channel channelMember).2 }

/-- The deployment fixes the authority cell. This prepares the batch before
factory/policy authorization. New grants are never used to authorize their own
birth. The post is the batch patch applied to the loaded cell; its one write
replaces that cell. -/
structure PreparedGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (loaded : Loaded deployment durable.snapshot)
    (descriptor : Descriptor registry) where
  private mk ::
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile descriptor.initialPolicies
  mode : ResourceBirthAuthority.BatchEvidence
    loaded.snapshot.cell descriptor

def prepareGrantBatch {F : Type} [Field F]
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (loaded : Loaded deployment durable.snapshot)
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
    {deployment : CanonicalCellRegistry.Deployment} {loaded : Loaded deployment durable.snapshot}
    {descriptor : Descriptor registry}

def PreparedGrantBatch.post (prepared : PreparedGrantBatch profile deployment loaded descriptor) :
    CredentialAuthorityDomain.Cell :=
  ResourceBirthAuthority.post loaded.snapshot.cell descriptor prepared.mode

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

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded.snapshot_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.snapshot_unique
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.clockOf_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clockOf_install
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.spentOf_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spentOf_install
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.spent_marker_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spent_marker_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.write_of_planes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_of_planes
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.loadDeployment_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadDeployment_refuses
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.loadDeployment_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadDeployment_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded.write_pre_is_loaded_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.write_pre_is_loaded_root

end Minidregg.Compiler.CredentialAuthorityDomainReceiver
