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
module

public import Compiler.CanonicalCellRegistry
public import Compiler.CredentialAuthorityDomain
public import Compiler.CredentialAuthorityReplay
public import Compiler.DurableReceiverCore
public import Theory.ResourceBirthAuthority

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.Util

@[expose] public section

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

/-- `decodeCell` on any bytes that decode to this live cell. Proved at a variable `bytes`:
unfolding `decodeCell` at the concrete `cellBytes cell` has the kernel run the decoder on
those bytes, which evaluates the Store layout digest (a closed cSHAKE256, Keccak round by
round), more than two minutes. -/
theorem decodeCell_of_decode {bytes : List UInt8} {cell : CredentialAuthorityDomain.Cell}
    (decoded : (LifecycleImage.codec registry).decode bytes = some (.live (packedCell cell))) :
    decodeCell bytes = some cell := by
  unfold decodeCell; rw [decoded]; rfl

theorem decodeCell_bytes (cell : CredentialAuthorityDomain.Cell) : decodeCell (cellBytes cell) = some cell :=
  decodeCell_of_decode (show (LifecycleImage.codec registry).decode
    ((LifecycleImage.codec registry).encode (.live (packedCell cell))) = _ from
      LifecycleImage.decode_encode _ _)

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

/-- Load at an already established clock. The exactness argument makes the
supplied height the snapshot's history length; a loaded durable image supplies
it in O(1). -/
def loadDeploymentAt (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (height : Nat) (heightExact : height = clockOf physical) :
    Option (Loaded deployment physical) :=
  if valid : deployment.Valid then
    match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell =>
        some ⟨Snapshot.ofCell deployment.domain height
            (spentOf deployment.domain physical) cell, valid, rfl, heightExact, rfl,
          (decodeCell_canonical decoded).symm⟩
  else none

def loadDeployment (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot) :
    Option (Loaded deployment physical) :=
  loadDeploymentAt deployment physical (clockOf physical) rfl

theorem loadDeploymentAt_eq (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (height : Nat) (heightExact : height = clockOf physical) :
    loadDeploymentAt deployment physical height heightExact = loadDeployment deployment physical := by
  cases heightExact
  rfl

/-- Refuting pole: a pinned identifier that does not hold a live authority cell
(a retired image, a fresh slot, another role, or a retired catalogue frame)
loads nothing. -/
theorem loadDeployment_refuses (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (undecodable : decodeCell (physical.canonicalBytes (cellIdOf deployment)) = none) :
    loadDeployment deployment physical = none := by
  unfold loadDeployment loadDeploymentAt
  split
  · split
    · rfl
    · rename_i cell decoded
      rw [undecodable] at decoded
      cases decoded
  · rfl

/-- Satisfiable pole at a supplied clock: the cell the physical snapshot holds
is loaded exactly. -/
theorem loadDeploymentAt_exact (deployment : CanonicalCellRegistry.Deployment)
    (physical : PhysicalSnapshot) (height : Nat) (heightExact : height = clockOf physical)
    (valid : deployment.Valid) (cell : CredentialAuthorityDomain.Cell)
    (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell) :
    ∃ loaded, loadDeploymentAt deployment physical height heightExact = some loaded ∧
      loaded.snapshot.cell = cell := by
  unfold loadDeploymentAt
  rw [dif_pos valid]
  split
  · rename_i decoded
    rw [holds, decodeCell_bytes] at decoded
    cases decoded
  · rename_i found decoded
    rw [holds, decodeCell_bytes] at decoded
    exact ⟨_, rfl, (Option.some.inj decoded).symm⟩

/-- Satisfiable pole: the cell the physical snapshot holds is loaded exactly. -/
theorem loadDeployment_exact (deployment : CanonicalCellRegistry.Deployment) (physical : PhysicalSnapshot)
    (valid : deployment.Valid) (cell : CredentialAuthorityDomain.Cell)
    (holds : physical.canonicalBytes (cellIdOf deployment) = cellBytes cell) :
    ∃ loaded, loadDeployment deployment physical = some loaded ∧ loaded.snapshot.cell = cell :=
  loadDeploymentAt_exact deployment physical (clockOf physical) rfl valid cell holds

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

/-- The complete held authority is fixed by its deployment and snapshot. -/
theorem Loaded.unique {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (left right : Loaded deployment physical) : left = right := by
  have same := Loaded.snapshot_unique left right
  cases left
  cases right
  simp only at same
  subst same
  rfl

#assert_axioms Loaded.unique

/-- **A held authority is what `loadDeployment` would recompute** on the same snapshot. -/
theorem Loaded.load_eq {deployment : CanonicalCellRegistry.Deployment}
    {physical : PhysicalSnapshot} (loaded : Loaded deployment physical) :
    loadDeployment deployment physical = some loaded := by
  obtain ⟨other, found, _⟩ :=
    loadDeployment_exact deployment physical loaded.valid loaded.snapshot.cell loaded.observed
  rw [found, Loaded.unique other loaded]

/-- `==` on byte lists, object identity first. `==` on `List UInt8` is `List.beq`
(`List.instBEq`), which `CompiledListOps.listDecEq`'s swap never reaches; the
comparisons of whole cell images on every session advance (`loadDeploymentFromAt`,
`decodeRowFrom`, the served twins, `cellsLawfulFrom`) call this, and an unchanged
cell's bytes in the next image are the very object of the prior image's. It is
`left == right` (`withPtrEq a b k h = k ()`, `bytesBEq_eq`). -/
@[inline] def bytesBEq (left right : List UInt8) : Bool :=
  withPtrEq left right (fun _ => left == right) (fun same => by subst same; exact beq_self_eq_true left)

@[simp] theorem bytesBEq_eq (left right : List UInt8) : bytesBEq left right = (left == right) := by
  simp only [bytesBEq, withPtrEq]

theorem bytesBEq_iff {left right : List UInt8} : bytesBEq left right = true ↔ left = right := by
  rw [bytesBEq_eq, beq_iff_eq]

/-- `loadDeployment` of a later physical snapshot: when the authority cell's
bytes equal `held`'s snapshot's, the held cell and its projection are reused
under this snapshot's clock and spent markers; otherwise the bytes are decoded and the
held cell's carried structure is moved to the decoded cell by their difference
(`Materialized.relativeTo`), so its root is not built over every entry.
`loadDeploymentFrom_eq`: it is `loadDeployment`. -/
def loadDeploymentFromAt {deployment : CanonicalCellRegistry.Deployment} {before : PhysicalSnapshot}
    (held : Loaded deployment before) (physical : PhysicalSnapshot)
    (height : Nat) (heightExact : height = clockOf physical) : Option (Loaded deployment physical) :=
  if same : bytesBEq (physical.canonicalBytes (cellIdOf deployment))
      (before.canonicalBytes (cellIdOf deployment)) then
    some ⟨⟨deployment.domain, height, spentOf deployment.domain physical, held.snapshot.cell,
        held.snapshot.authState, held.snapshot.authStateExact, held.snapshot.issued,
        held.domainExact ▸ held.snapshot.issuedExact⟩, held.valid, rfl, heightExact, rfl,
      (bytesBEq_iff.mp same).trans held.observed⟩
  else
    match decoded : decodeCell (physical.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell =>
        some ⟨Snapshot.ofCell deployment.domain height (spentOf deployment.domain physical)
            (held.snapshot.cell.relativeTo cell), held.valid, rfl, heightExact, rfl,
          by rw [Materialized.relativeTo_eq]; exact (decodeCell_canonical decoded).symm⟩

def loadDeploymentFrom {deployment : CanonicalCellRegistry.Deployment} {before : PhysicalSnapshot}
    (held : Loaded deployment before) (physical : PhysicalSnapshot) : Option (Loaded deployment physical) :=
  loadDeploymentFromAt held physical (clockOf physical) rfl

theorem loadDeploymentFromAt_eq {deployment : CanonicalCellRegistry.Deployment} {before : PhysicalSnapshot}
    (held : Loaded deployment before) (physical : PhysicalSnapshot)
    (height : Nat) (heightExact : height = clockOf physical) :
    loadDeploymentFromAt held physical height heightExact =
      loadDeploymentAt deployment physical height heightExact := by
  unfold loadDeploymentFromAt
  split
  · rename_i same
    obtain ⟨loaded, found, _⟩ := loadDeploymentAt_exact deployment physical height heightExact
      held.valid held.snapshot.cell ((bytesBEq_iff.mp same).trans held.observed)
    rw [found]
    exact congrArg some (Loaded.unique _ loaded)
  · unfold loadDeploymentAt
    rw [dif_pos held.valid]
    split <;> first
      | rfl
      | exact congrArg some (Loaded.unique _ _)

theorem loadDeploymentFrom_eq {deployment : CanonicalCellRegistry.Deployment} {before : PhysicalSnapshot}
    (held : Loaded deployment before) (physical : PhysicalSnapshot) :
    loadDeploymentFrom held physical = loadDeployment deployment physical :=
  loadDeploymentFromAt_eq held physical (clockOf physical) rfl

#assert_axioms loadDeploymentFrom_eq

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
root of that same cell. The post is encoded once: its root is the root of
those same bytes (`cellRoot` unfolds to exactly that). -/
def Loaded.write {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (_loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) : DataWrite :=
  let bytes := cellBytes post
  { cellId := cellIdOf deployment
    expectedPre := physical.model.roots (cellIdOf deployment)
    exactPost := ResourceBirthCodec.rootBytes bytes
    canonicalPostBytes := bytes }

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
  have same : left = right := Materialized.ext (Minidregg.Theory.SparseMap.ext planes)
  rw [same]

theorem cellRoot_of_planes (left right : CredentialAuthorityDomain.Cell)
    (planes : ∀ address, left.logical address = right.logical address) :
    cellRoot left = cellRoot right := by
  rw [Materialized.ext (Minidregg.Theory.SparseMap.ext planes)]

theorem Loaded.writes_single {deployment : CanonicalCellRegistry.Deployment} {physical : PhysicalSnapshot}
    (loaded : Loaded deployment physical) (post : CredentialAuthorityDomain.Cell) :
    (loaded.writes post).map DataWrite.cellId = [cellIdOf deployment] := rfl

/-! ## One complete physical directory, including retired identities -/

def directoryRows (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    List (Nat × List UInt8) :=
  durable.cells.map fun row => (row.1.value, row.2)

/-! ## The directory held as data

A served state's directory is held as one lifecycle image per identifier (a persistent map, no
entry for a fresh image) and the used set beside it, which is exactly the identifiers whose
image was ever used. A step writes the images of the cells it wrote (`HeldImages.write`): one
map update per written cell, and the used set moves by a cons at an identifier's first use. -/

/-- The stored form of an image: a fresh image is no entry, so the map is determined by its images. -/
def storedImage : LifecycleImage registry → Option (LifecycleImage registry)
  | .fresh => none
  | image => some image

theorem storedImage_getD (image : LifecycleImage registry) : (storedImage image).getD .fresh = image := by
  cases image <;> rfl

theorem storedImage_ne_fresh (image : LifecycleImage registry) : storedImage image ≠ some .fresh := by
  cases image <;> simp [storedImage]

/-- Lifecycle images by identifier with the used set: `used` is exactly the identifiers whose
image was ever used, so a first use is a cons, decided by the image, never by a scan of the set. -/
structure HeldImages where
  images : SparseMap Nat (fun _ => LifecycleImage registry)
  used : Finset Nat
  noFresh : ∀ identifier, images.get? identifier ≠ some .fresh
  usedExact : ∀ identifier,
    identifier ∈ used ↔ LifecycleImage.everUsed registry ((images.get? identifier).getD .fresh) = true

namespace HeldImages

/-- The image at an identifier; fresh where none is held. -/
@[inline] def image (held : HeldImages) (identifier : Nat) : LifecycleImage registry :=
  (held.images.get? identifier).getD .fresh

theorem images_eq (held : HeldImages) (identifier : Nat) :
    held.images.get? identifier = storedImage (held.image identifier) := by
  unfold image
  have noFresh := held.noFresh identifier
  cases found : held.images.get? identifier with
  | none => rfl
  | some image =>
      rw [found] at noFresh
      cases image with
      | fresh => exact absurd rfl noFresh
      | retired => rfl
      | live cell => rfl

theorem mem_used (held : HeldImages) (identifier : Nat) :
    identifier ∈ held.used ↔ LifecycleImage.everUsed registry (held.image identifier) = true :=
  held.usedExact identifier

/-- Held images are equal when their images are. -/
theorem ext {left right : HeldImages} (same : ∀ identifier, left.image identifier = right.image identifier) :
    left = right := by
  have images : left.images = right.images := SparseMap.ext fun identifier => by
    show left.images.get? identifier = right.images.get? identifier
    rw [left.images_eq, right.images_eq, same]
  have used : left.used = right.used := Finset.ext fun identifier => by
    rw [left.mem_used, right.mem_used, same]
  cases left
  cases right
  simp only at images used
  subst images
  subst used
  rfl

def empty : HeldImages where
  images := SparseMap.empty
  used := ∅
  noFresh := by simp
  usedExact := by simp [LifecycleImage.everUsed]

theorem image_empty (identifier : Nat) : empty.image identifier = .fresh := by
  simp [image, empty]

/-- Write one identifier's image. The used set conses the identifier at its first use and drops
it only when a used image is overwritten by a fresh one. -/
def set (held : HeldImages) (identifier : Nat) (next : LifecycleImage registry) : HeldImages where
  images := held.images.set identifier (storedImage next)
  used :=
    if LifecycleImage.everUsed registry next then
      if was : LifecycleImage.everUsed registry (held.image identifier) = true then held.used
      else Finset.cons identifier held.used fun member => was ((held.mem_used identifier).mp member)
    else if LifecycleImage.everUsed registry (held.image identifier) then held.used.erase identifier
    else held.used
  noFresh := by
    intro other
    by_cases same : other = identifier
    · subst same
      rw [SparseMap.set_eq]
      exact storedImage_ne_fresh next
    · rw [SparseMap.set_ne _ _ _ _ same]
      exact held.noFresh other
  usedExact := by
    intro other
    by_cases same : other = identifier
    · subst same
      rw [SparseMap.set_eq, storedImage_getD]
      have was := held.mem_used other
      by_cases nextUsed : LifecycleImage.everUsed registry next = true
      · rw [if_pos nextUsed]
        split
        · rename_i old
          exact ⟨fun _ => nextUsed, fun _ => was.mpr old⟩
        · simp [nextUsed]
      · rw [if_neg nextUsed]
        split
        · simp [nextUsed]
        · rename_i old
          exact ⟨fun member => absurd (was.mp member) old, fun used => absurd used nextUsed⟩
    · rw [SparseMap.set_ne _ _ _ _ same]
      have was := held.usedExact other
      split
      · split
        · exact was
        · simp [same, was]
      · split
        · simp [same, was]
        · exact was

theorem image_set (held : HeldImages) (identifier : Nat) (next : LifecycleImage registry) (other : Nat) :
    (held.set identifier next).image other = if other = identifier then next else held.image other := by
  by_cases same : other = identifier
  · subst same
    rw [if_pos rfl]
    show ((held.images.set other (storedImage next)).get? other).getD .fresh = next
    rw [SparseMap.set_eq, storedImage_getD]
  · rw [if_neg same]
    show ((held.images.set identifier (storedImage next)).get? other).getD .fresh = held.image other
    rw [SparseMap.set_ne _ _ _ _ same]
    rfl

/-- Decode and write the image of each listed identifier from `bytesAt`; `none` when one does
not decode. -/
def write (bytesAt : Nat → List UInt8) : HeldImages → List Nat → Option HeldImages
  | held, [] => some held
  | held, identifier :: rest =>
      match (LifecycleImage.codec registry).decode (bytesAt identifier) with
      | none => none
      | some next => write bytesAt (held.set identifier next) rest

theorem write_some {bytesAt : Nat → List UInt8} :
    ∀ {held after : HeldImages} {identifiers : List Nat}, write bytesAt held identifiers = some after →
      ∀ other, LifecycleImage.bytes registry (after.image other) =
        if other ∈ identifiers then bytesAt other else LifecycleImage.bytes registry (held.image other)
  | held, after, [], written, other => by
      simp only [write, Option.some.injEq] at written
      subst written
      simp
  | held, after, identifier :: rest, written, other => by
      simp only [write] at written
      split at written
      · cases written
      · rename_i next decoded
        rw [write_some written other, image_set]
        by_cases inRest : other ∈ rest
        · simp [inRest]
        · by_cases same : other = identifier
          · subst same
            simp [inRest, LifecycleImage.decode_canonical registry decoded]
          · simp [inRest, same]

theorem write_none {bytesAt : Nat → List UInt8} :
    ∀ {held : HeldImages} {identifiers : List Nat}, write bytesAt held identifiers = none →
      ∃ identifier ∈ identifiers, (LifecycleImage.codec registry).decode (bytesAt identifier) = none
  | held, [], written => by simp [write] at written
  | held, identifier :: rest, written => by
      simp only [write] at written
      split at written
      · rename_i decoded
        exact ⟨identifier, List.mem_cons_self, decoded⟩
      · obtain ⟨other, member, decoded⟩ := write_none written
        exact ⟨other, List.mem_cons_of_mem _ member, decoded⟩

/-- The directory the held images are: a slot from each image, the held used set. -/
def directory (held : HeldImages) : Directory Nat registry where
  slots identifier := LifecycleImage.slot registry (held.image identifier)
  used := held.used
  present_used := by
    intro identifier cell present
    apply (held.mem_used identifier).mpr
    cases image : held.image identifier <;>
      simp_all [LifecycleImage.slot, LifecycleImage.everUsed]

theorem view_directory (held : HeldImages) (identifier : Nat) :
    LifecycleImage.view registry held.directory identifier = held.image identifier := by
  have used := held.mem_used identifier
  unfold LifecycleImage.view
  simp only [directory]
  cases image : held.image identifier <;>
    simp_all [LifecycleImage.slot, LifecycleImage.everUsed]

end HeldImages

/-- Two directories with the same view at every identifier are equal. -/
theorem directory_eq_of_view {left right : Directory Nat registry}
    (same : ∀ identifier, LifecycleImage.view registry left identifier =
      LifecycleImage.view registry right identifier) : left = right := by
  have slots : left.slots = right.slots := funext fun identifier => by
    rw [← LifecycleImage.view_slot registry left identifier, same, LifecycleImage.view_slot]
  have used : left.used = right.used := Finset.ext fun identifier => by
    rw [← LifecycleImage.view_used registry left identifier, same, LifecycleImage.view_used]
  cases left
  cases right
  simp only at slots used
  subst slots
  subst used
  rfl

/-- The finite support comes from the complete replayed durable image. A
request cannot supply a reduced directory or discard tombstones. The only
absent lifecycle representation is `[]`. The directory is held as data
(`HeldImages`): every identifier's image encodes to the image's canonical bytes there, so a later
image is loaded by writing only the cells whose bytes moved (`loadDirectoryStep`,
`loadDirectoryFrom`). -/
structure LoadedDirectory (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) where
  private mk ::
  held : HeldImages
  exact : ∀ identifier, LifecycleImage.bytes registry (held.image identifier) =
    durable.snapshot.canonicalBytes ⟨identifier⟩
  absentDefault : durable.image.seed.absentBytes = []

/-- The held directory. -/
@[inline] def LoadedDirectory.directory {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) : Directory Nat registry :=
  loaded.held.directory

/-- The directory of `durable` from images that agree with it outside `identifiers`: decode and
write those (`HeldImages.write`). `none` exactly when one of them does not decode. -/
def loadDirectoryWriting (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (absentDefault : durable.image.seed.absentBytes = []) (base : HeldImages) (identifiers : List Nat)
    (agrees : ∀ identifier, identifier ∉ identifiers →
      LifecycleImage.bytes registry (base.image identifier) = durable.snapshot.canonicalBytes ⟨identifier⟩) :
    Option (LoadedDirectory durable) :=
  match written : HeldImages.write (fun identifier => durable.snapshot.canonicalBytes ⟨identifier⟩) base
      identifiers with
  | none => none
  | some held => some ⟨held, fun identifier => by
      rw [HeldImages.write_some written identifier]
      split
      · rfl
      · rename_i outside
        exact agrees identifier outside, absentDefault⟩

theorem loadDirectoryWriting_none {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {absentDefault : durable.image.seed.absentBytes = []} {base : HeldImages} {identifiers : List Nat}
    {agrees : ∀ identifier, identifier ∉ identifiers →
      LifecycleImage.bytes registry (base.image identifier) = durable.snapshot.canonicalBytes ⟨identifier⟩}
    (refused : loadDirectoryWriting durable absentDefault base identifiers agrees = none) :
    ∃ identifier ∈ identifiers,
      (LifecycleImage.codec registry).decode (durable.snapshot.canonicalBytes ⟨identifier⟩) = none := by
  unfold loadDirectoryWriting at refused
  split at refused
  · rename_i missing
    exact HeldImages.write_none missing
  · cases refused

/-- Every enumerable cell decoded once into the held images (an open). Outside the enumeration
the bytes are the absent default `[]`, which is the fresh image's. -/
def loadDirectory (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    Option (LoadedDirectory durable) :=
  if absentDefault : durable.image.seed.absentBytes = [] then
    loadDirectoryWriting durable absentDefault HeldImages.empty (durable.cellIds.map (·.value))
      fun identifier outside => by
        rw [HeldImages.image_empty]
        have notMember : (⟨identifier⟩ : Digest) ∉ durable.image.cellIds := fun member =>
          outside (List.mem_map.mpr ⟨_, (DurableReceiverIO.Loaded.cellIds_eq durable).symm ▸ member, rfl⟩)
        exact ((Kernel.DurableCheckpoint.resume_outside_support ResourceBirthCodec.rootBytes
          durable.image durable.baseHeight durable.base durable.snapshot durable.resumed
          ⟨identifier⟩ notMember).trans absentDefault).symm
  else none

/-- Global exactness, including identities outside the finite support. -/
theorem LoadedDirectory.bytes_exact
    {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (identifier : Nat) :
    LifecycleImage.bytes registry (LifecycleImage.view registry loaded.directory identifier) =
      durable.snapshot.canonicalBytes ⟨identifier⟩ := by
  rw [LoadedDirectory.directory, HeldImages.view_directory]
  exact loaded.exact identifier

/-- An image with a directory decodes at every identifier. -/
theorem LoadedDirectory.decodes {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) (identifier : Nat) :
    (LifecycleImage.codec registry).decode (durable.snapshot.canonicalBytes ⟨identifier⟩) =
      some (loaded.held.image identifier) := by
  rw [← loaded.exact identifier]
  exact LifecycleImage.decode_encode registry _

/-! ## A held directory is the recomputation; an unchanged row is not decoded again

The Host holds one `LoadedDirectory` per served image (`NativeHost.Opened`).
These facts let every request read it instead of decoding every stored cell
again, and let a session advanced by new records decode only the cells whose
bytes moved. -/

/-- Two loaded directories of one image are equal: the bytes fix every image. -/
theorem LoadedDirectory.unique {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (left right : LoadedDirectory durable) : left = right := by
  have same : left.held = right.held := HeldImages.ext fun identifier => by
    have bytes := (left.exact identifier).trans (right.exact identifier).symm
    have decoded := congrArg (LifecycleImage.rawDecode registry) bytes
    rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at decoded
    exact Option.some.inj decoded
  cases left
  cases right
  simp only at same
  subst same
  rfl

/-- **A held directory is what `loadDirectory` would recompute** on the same image. -/
theorem LoadedDirectory.load_eq {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : LoadedDirectory durable) : loadDirectory durable = some loaded := by
  unfold loadDirectory
  rw [dif_pos loaded.absentDefault]
  cases computed : loadDirectoryWriting durable loaded.absentDefault HeldImages.empty
      (durable.cellIds.map (·.value)) _ with
  | some other => exact congrArg some (LoadedDirectory.unique other loaded)
  | none =>
      exfalso
      obtain ⟨identifier, _, decoded⟩ := loadDirectoryWriting_none computed
      rw [loaded.decodes identifier] at decoded
      cases decoded

/-- Any load that yields a directory whenever every listed cell decodes, and refuses only when a
cell of `durable` does not decode, is `loadDirectory`. -/
theorem loadDirectory_of_refusal {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (other : Option (LoadedDirectory durable))
    (refusal : other = none → (durable.image.seed.absentBytes = [] →
      ∃ identifier, (LifecycleImage.codec registry).decode (durable.snapshot.canonicalBytes ⟨identifier⟩) = none)) :
    other = loadDirectory durable := by
  cases other with
  | some loaded => exact (LoadedDirectory.load_eq loaded).symm
  | none =>
      cases computed : loadDirectory durable with
      | none => rfl
      | some loaded =>
          exfalso
          obtain ⟨identifier, decoded⟩ := refusal rfl loaded.absentDefault
          rw [loaded.decodes identifier] at decoded
          cases decoded

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

private theorem decodeRows_isSome : ∀ (rows : List (Nat × List UInt8)),
    (∀ row ∈ rows, ((LifecycleImage.codec registry).decode row.2).isSome) →
      (DirectoryImage.decodeRows registry rows).isSome
  | [], _ => rfl
  | (identifier, bytes) :: rest, decodes => by
      have head := decodes (identifier, bytes) (by simp)
      have tail := decodeRows_isSome rest fun row member => decodes row (by simp [member])
      obtain ⟨image, imageDecoded⟩ := Option.isSome_iff_exists.mp head
      obtain ⟨images, imagesDecoded⟩ := Option.isSome_iff_exists.mp tail
      simp [DirectoryImage.decodeRows, imageDecoded, imagesDecoded]

/-- **The held directory is the full decode** of every enumerable row (`DirectoryImage.decode`,
the directory's specification): the same directory, and the same refusal. -/
theorem loadDirectory_directory (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (absentDefault : durable.image.seed.absentBytes = []) :
    (loadDirectory durable).map (·.directory) = DirectoryImage.decode registry (directoryRows durable) := by
  have rowsAt : ∀ identifier, ((directoryRows durable).lookup identifier).getD [] =
      durable.snapshot.canonicalBytes ⟨identifier⟩ := by
    intro identifier
    simp only [directoryRows, DurableReceiverIO.Loaded.cells, List.map_map, Function.comp_def]
    rw [lookup_enumeration]
    split
    · rfl
    · rename_i outside
      exact ((Kernel.DurableCheckpoint.resume_outside_support ResourceBirthCodec.rootBytes
        durable.image durable.baseHeight durable.base durable.snapshot durable.resumed
        ⟨identifier⟩ outside).trans absentDefault).symm
  cases decoded : DirectoryImage.decode registry (directoryRows durable) with
  | some directory =>
      cases computed : loadDirectory durable with
      | some loaded =>
          simp only [Option.map_some, Option.some.injEq]
          apply directory_eq_of_view
          intro identifier
          have bytes := (loaded.bytes_exact identifier).trans ((rowsAt identifier).symm.trans
            (DirectoryImage.decode_exact registry decoded identifier).symm)
          have same := congrArg (LifecycleImage.rawDecode registry) bytes
          rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at same
          exact Option.some.inj same
      | none =>
          exfalso
          unfold loadDirectory at computed
          rw [dif_pos absentDefault] at computed
          obtain ⟨identifier, _, refused⟩ := loadDirectoryWriting_none computed
          rw [← rowsAt identifier, ← DirectoryImage.decode_exact registry decoded identifier] at refused
          have roundTrip := LifecycleImage.decode_encode registry
            (LifecycleImage.view registry directory identifier)
          change (LifecycleImage.codec registry).decode (LifecycleImage.bytes registry _) = _ at roundTrip
          rw [roundTrip] at refused
          cases refused
  | none =>
      cases computed : loadDirectory durable with
      | none => rfl
      | some loaded =>
          exfalso
          have rowsDecode := decodeRows_isSome (directoryRows durable) fun row member => by
            simp only [directoryRows, DurableReceiverIO.Loaded.cells, List.map_map, List.mem_map,
              Function.comp_def] at member
            obtain ⟨cellId, _, same⟩ := member
            subst same
            rw [loaded.decodes cellId.value]
            rfl
          obtain ⟨rows, rowsDecoded⟩ := Option.isSome_iff_exists.mp rowsDecode
          have keys := DirectoryImage.decodeRows_keys registry rowsDecoded
          have unique : (rows.map Prod.fst).Nodup := by
            rw [keys]
            simp only [directoryRows, DurableReceiverIO.Loaded.cells, List.map_map, Function.comp_def]
            exact (Kernel.DurableCheckpoint.nodup_eraseDups _).map fun left right same => by
              cases left
              cases right
              simp only at same
              rw [same]
          simp [DirectoryImage.decode, rowsDecoded, unique] at decoded

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

/-- The identifiers whose canonical bytes differ between two images (over both enumerations). -/
def changedCells (prior durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) : List Nat :=
  ((durable.cellIds ++ prior.cellIds).filter fun cellId =>
    !bytesBEq (prior.snapshot.canonicalBytes cellId) (durable.snapshot.canonicalBytes cellId)).map (·.value)

/-- `loadDirectory` of a later image, decoding only the cells whose bytes differ from `held`'s
image (`loadDirectoryFrom_eq`). It still compares every cell; a step that knows the cells it
wrote uses `loadDirectoryStep`. -/
def loadDirectoryFrom {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    Option (LoadedDirectory durable) :=
  if absentDefault : durable.image.seed.absentBytes = [] then
    loadDirectoryWriting durable absentDefault held.held (changedCells prior durable)
      fun identifier unchanged => by
        rw [held.exact identifier]
        by_cases same : bytesBEq (prior.snapshot.canonicalBytes ⟨identifier⟩)
            (durable.snapshot.canonicalBytes ⟨identifier⟩) = true
        · exact bytesBEq_iff.mp same
        · by_cases listed : (⟨identifier⟩ : Digest) ∈ durable.cellIds ++ prior.cellIds
          · have changed : identifier ∈ changedCells prior durable :=
              List.mem_map.mpr ⟨(⟨identifier⟩ : Digest), List.mem_filter.mpr ⟨listed, by simpa using same⟩, rfl⟩
            exact absurd changed unchanged
          · have outside := fun (image : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
                (member : (⟨identifier⟩ : Digest) ∉ image.image.cellIds) =>
              Kernel.DurableCheckpoint.resume_outside_support ResourceBirthCodec.rootBytes
                image.image image.baseHeight image.base image.snapshot image.resumed ⟨identifier⟩ member
            rw [List.mem_append, not_or, DurableReceiverIO.Loaded.cellIds_eq,
              DurableReceiverIO.Loaded.cellIds_eq] at listed
            rw [outside prior listed.2, outside durable listed.1, absentDefault, held.absentDefault]
  else none

/-- **The incremental load is the full load**: same refusal, same directory. -/
theorem loadDirectoryFrom_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) :
    loadDirectoryFrom held durable = loadDirectory durable := by
  apply loadDirectory_of_refusal
  intro refused absentDefault
  unfold loadDirectoryFrom at refused
  rw [dif_pos absentDefault] at refused
  obtain ⟨identifier, _, decoded⟩ := loadDirectoryWriting_none refused
  exact ⟨identifier, decoded⟩

/-- `loadDirectory` of an image one step after a held one, decoding only the cells the step wrote
(`moved`: every other cell kept its bytes, so its held image stands). -/
def loadDirectoryStep {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (written : List CellId)
    (moved : ∀ cellId, cellId ∉ written → durable.snapshot.canonicalBytes cellId = prior.snapshot.canonicalBytes cellId) :
    Option (LoadedDirectory durable) :=
  if absentDefault : durable.image.seed.absentBytes = [] then
    loadDirectoryWriting durable absentDefault held.held (written.map (·.value))
      fun identifier unwritten => by
        rw [held.exact identifier, moved ⟨identifier⟩ fun member =>
          unwritten (List.mem_map.mpr ⟨_, member, rfl⟩)]
  else none

/-- **The step load is the full load**: same refusal, same directory. -/
theorem loadDirectoryStep_eq {prior : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (held : LoadedDirectory prior) (durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (written : List CellId)
    (moved : ∀ cellId, cellId ∉ written → durable.snapshot.canonicalBytes cellId = prior.snapshot.canonicalBytes cellId) :
    loadDirectoryStep held durable written moved = loadDirectory durable := by
  apply loadDirectory_of_refusal
  intro refused absentDefault
  unfold loadDirectoryStep at refused
  rw [dif_pos absentDefault] at refused
  obtain ⟨identifier, _, decoded⟩ := loadDirectoryWriting_none refused
  exact ⟨identifier, decoded⟩

/-! ## Concrete preparation of the root-issuance batch -/

/-- A grant is ready at the loaded cell when it is a fresh root whose own key
is not yet registered (the birth registers it) and not revoked, and every
ancestor (a room birth: the creator's room-grant lineage) and channel it names
is already registered and live; each read is a presence-plane read of the one
cell. -/
def GrantReady (snapshot : CredentialAuthorityDomain.Snapshot) (grant : AuthorityGrant) : Prop :=
  grant.capability.ancestry = [] ∧
    CapabilityIdFresh snapshot.cell grant.capability.head.id ∧
    grant.capability.head.parent = none ∧
    grant.capability.head.root = grant.capability.head.id ∧
    (∀ ancestor ∈ grant.capability.head.ancestors,
      isRegistered snapshot.cell (.capability ancestor) = true ∧
      isRevoked snapshot.cell (.capability ancestor) = false) ∧
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
        ancestorsRegistered := fun ancestor member => (ancestors ancestor member).1
        issuerCurrent := issuer
        policyCurrent := policy
        selfUnregistered := unregistered
        channelsRegistered := fun channel channelMember => (channels channel channelMember).1
        selfLive := self
        channelsLive := fun channel channelMember => (channels channel channelMember).2
        ancestorsLive := fun ancestor member => (ancestors ancestor member).2 }

/-- The deployment fixes the authority cell. This prepares the batch before
factory/policy authorization. New grants are never used to authorize their own
birth. The post is the batch patch applied to the loaded cell; its one write
replaces that cell. -/
structure PreparedGrantBatch {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (authority : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) where
  private mk ::
  initialSources : PolicySourceCell.CheckedInitials deployment.domain profile descriptor.initialPolicies
  mode : ResourceBirthAuthority.BatchEvidence
    authority.cell descriptor
  /-- The post cell, built once: every reader of `post` (each planned write, the candidate
  check, the session's held cell) shares this one `Materialized`, so its bytes are encoded
  once per birth (`post_eq_postCached`). -/
  postCell : CredentialAuthorityDomain.Cell
  postExact : postCell = ResourceBirthAuthority.post authority.cell descriptor mode
/-- The prepared batch is fresh at the loaded authority cell. -/
theorem PreparedGrantBatch.batchFresh {F : Type} [Field F]
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {authority : CredentialAuthorityDomain.Snapshot}
    {descriptor : Descriptor registry}
    (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    ((ResourceBirthAuthority.entries descriptor).map Sigma.fst).Nodup ∧
      descriptor.GrantIdsDistinct ∧
      (∀ row ∈ descriptor.parentRows, authority.cell.logical ⟨.parent, row.1⟩ = none) :=
  ⟨prepared.mode.slotsDistinct, prepared.mode.grantIdsDistinct, prepared.mode.parentsFresh⟩

/-- **What a prepared grant batch guarantees about its indices**: the batch's slots and grant ids
are distinct, every parent row is absent in the `authority` cell, and every initial policy of
`descriptor` decodes to a record satisfying `InitialFacts` for `deployment`'s domain and `profile`
(the profile has a descriptor, the record names this domain and the profile's semantics, is version 0
with no predecessor, and its predicate is one the profile's compiler supports). -/
theorem PreparedGrantBatch.sound {F : Type} [Field F]
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {authority : CredentialAuthorityDomain.Snapshot}
    {descriptor : Descriptor registry}
    (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    ((ResourceBirthAuthority.entries descriptor).map Sigma.fst).Nodup ∧
      descriptor.GrantIdsDistinct ∧
      (∀ row ∈ descriptor.parentRows, authority.cell.logical ⟨.parent, row.1⟩ = none) ∧
      ∀ initial ∈ descriptor.initialPolicies, ∃ record,
        PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
          PolicySourceCell.InitialFacts deployment.domain profile initial record :=
  ⟨prepared.mode.slotsDistinct, prepared.mode.grantIdsDistinct, prepared.mode.parentsFresh,
    fun initial member => by
      obtain ⟨record, _, decoded, facts⟩ := prepared.initialSources.record_of_member initial member
      exact ⟨record, decoded, facts⟩⟩

def prepareGrantBatch {F : Type} [Field F]
    (profile : CanonicalPolicyAdmission.PolicyCompilerProfile F)
    (deployment : CanonicalCellRegistry.Deployment) (authority : CredentialAuthorityDomain.Snapshot)
    (descriptor : Descriptor registry) :
    Option (PreparedGrantBatch profile deployment authority descriptor) := do
  let initialSources ← PolicySourceCell.checkInitials deployment.domain profile descriptor.initialPolicies
  if ready : BatchReady authority descriptor then
    let mode := batchEvidence authority descriptor ready
    some ⟨initialSources, mode, ResourceBirthAuthority.post authority.cell descriptor mode, rfl⟩
  else none

section GrantBatch

variable {F : Type} [Field F]
    {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {authority : CredentialAuthorityDomain.Snapshot}
    {descriptor : Descriptor registry}

def PreparedGrantBatch.post (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    CredentialAuthorityDomain.Cell :=
  ResourceBirthAuthority.post authority.cell descriptor prepared.mode

/-- The post cell the preparation built (`postExact`). -/
def PreparedGrantBatch.postCached (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    CredentialAuthorityDomain.Cell :=
  prepared.postCell

/-- Compiled code reads the prepared post cell instead of re-applying the batch patch, so its
cached bytes and root are shared by every reader. -/
@[csimp] theorem PreparedGrantBatch.post_eq_postCached :
    @PreparedGrantBatch.post = @PreparedGrantBatch.postCached := by
  funext F _ profile deployment authority descriptor prepared
  exact prepared.postExact.symm

def PreparedGrantBatch.auxiliaryCreates
    (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    List (CreateRequest (CellId := Nat) registry) :=
  CanonicalCellRegistry.initialSourceCreates deployment.domain prepared.initialSources.records

theorem PreparedGrantBatch.post_logical
    (prepared : PreparedGrantBatch profile deployment authority descriptor) :
    prepared.post.logical = setAll authority.logical (ResourceBirthAuthority.entries descriptor) :=
  ResourceBirthAuthority.post_logical _ _ _

end GrantBatch

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded.snapshot_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.snapshot_unique
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomainReceiver.clockOf_install' depends on axioms: [propext, Quot.sound] -/
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
