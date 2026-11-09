/-
# Compiler.CredentialAuthorityServed — the directory and the authority cell of a served state

KN2 stage 2b-1. The light counterparts of `CredentialAuthorityDomainReceiver`'s
`LoadedDirectory` and `Loaded` (the authority domain), over a `Served` state
instead of the full verified materialization:

* `ServedDirectory served`: the complete physical directory of the served
  state (every enumerable cell, tombstones included), held as lifecycle images by
  identifier (`HeldImages`) and moved by a step at the cells it wrote
  (`loadServedDirectoryStep`); `bytes_exact` holds at every identifier, inside or
  outside the enumeration.
* `ServedAuthority deployment served`: the deployment's authority cell decoded
  from the served bytes. It carries NO spent function: the authority clock is
  the served height (`snapshotOn`'s revision) and a spent marker is read only
  through a `VerifiedFootprint` that declares its nullifier (`snapshotOn`).

`loadServedDirectory_ofLoaded` / `loadServedAuthority_ofLoaded`: on the full
shape's state the light loads decode exactly what the full loads decode.
-/
module

public import Compiler.CredentialAuthorityDomainReceiver
public import Compiler.DurableServed

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

@[expose] public section

namespace Minidregg.Compiler.CredentialAuthorityServed

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.DurableServed (Served)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (VerifiedFootprint)
open Minidregg.Kernel.DurableDataIntent (CellId)
open Minidregg.Kernel.DurableView (Keys)

set_option autoImplicit false

abbrev State (store : StoreIdentity) := Served ResourceBirthCodec.rootBytes store

def servedRows {store : StoreIdentity} (served : State store) : List (Nat × List UInt8) :=
  served.cells.map fun row => (row.1.value, row.2)

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

/-- The complete physical directory of a served state, held as images by identifier
(`HeldImages`): every identifier's image encodes to the served bytes there. -/
structure ServedDirectory {store : StoreIdentity} (served : State store) where
  private mk ::
  held : HeldImages
  exact : ∀ identifier, LifecycleImage.bytes registry (held.image identifier) = served.canonicalBytes ⟨identifier⟩
  absentDefault : served.absentBytes = []

/-- The held directory. -/
@[inline] def ServedDirectory.directory {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) : Directory Nat registry :=
  loaded.held.directory

/-- Every enumerable cell decoded once into the held images (the store open). -/
def loadServedDirectory {store : StoreIdentity} (served : State store) : Option (ServedDirectory served) :=
  if absentDefault : served.absentBytes = [] then
    match written : HeldImages.write (fun identifier => served.canonicalBytes ⟨identifier⟩) HeldImages.empty
        (served.cellIds.map (·.value)) with
    | none => none
    | some held => some ⟨held, fun identifier => by
        rw [HeldImages.write_some written identifier, HeldImages.image_empty]
        split
        · rfl
        · rename_i outside
          have notMember : (⟨identifier⟩ : CellId) ∉ served.cellIds := fun member =>
            outside (List.mem_map.mpr ⟨_, member, rfl⟩)
          exact ((served.canonicalBytes_outside ⟨identifier⟩ notMember).trans absentDefault).symm,
        absentDefault⟩
  else none

/-- Global exactness, including identities outside the finite support. -/
theorem ServedDirectory.bytes_exact {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) (identifier : Nat) :
    LifecycleImage.bytes registry (LifecycleImage.view registry loaded.directory identifier) =
      served.canonicalBytes ⟨identifier⟩ := by
  rw [ServedDirectory.directory, HeldImages.view_directory]
  exact loaded.exact identifier

/-- Two directories of one served state are equal. -/
theorem ServedDirectory.unique {store : StoreIdentity} {served : State store}
    (left right : ServedDirectory served) : left = right := by
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

/-- A served state with a directory decodes at every identifier. -/
theorem ServedDirectory.decodes {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) (identifier : Nat) :
    (LifecycleImage.codec registry).decode (served.canonicalBytes ⟨identifier⟩) =
      some (loaded.held.image identifier) := by
  rw [← loaded.exact identifier]
  exact LifecycleImage.decode_encode registry _

/-- Loading a state that has a directory yields that directory. -/
theorem ServedDirectory.load_eq {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) : loadServedDirectory served = some loaded := by
  unfold loadServedDirectory
  rw [dif_pos loaded.absentDefault]
  split
  · rename_i missing
    obtain ⟨identifier, _, decoded⟩ := HeldImages.write_none missing
    rw [loaded.decodes identifier] at decoded
    cases decoded
  · exact congrArg some (ServedDirectory.unique _ loaded)

/-- Two served states whose bytes agree at an identifier load the same slot there. -/
theorem ServedDirectory.slots_eq_of_bytes {store : StoreIdentity} {first second : State store}
    (left : ServedDirectory first) (right : ServedDirectory second) (identifier : Nat)
    (same : first.canonicalBytes ⟨identifier⟩ = second.canonicalBytes ⟨identifier⟩) :
    left.directory.slots identifier = right.directory.slots identifier := by
  have views : LifecycleImage.view registry left.directory identifier =
      LifecycleImage.view registry right.directory identifier := by
    have bytes := (left.bytes_exact identifier).trans (same.trans (right.bytes_exact identifier).symm)
    have decoded := congrArg (LifecycleImage.rawDecode registry) bytes
    rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at decoded
    exact Option.some.inj decoded
  rw [← LifecycleImage.view_slot registry left.directory identifier, views, LifecycleImage.view_slot]

/-- **The light directory of the full shape's state is the full directory**:
the same rows, so the same decode and the same refusal. -/
theorem servedRows_ofLoaded {store : StoreIdentity} (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (sameStart : store.logStart = loaded.logStart) :
    servedRows (Served.ofLoaded loaded sameStart) = directoryRows loaded := by
  simp only [servedRows, directoryRows, Served.cells, Served.ofLoaded_canonicalBytes,
    DurableReceiverIO.Loaded.cells_eq_cellsCached, DurableReceiverIO.Loaded.cellsCached, List.map_map,
    Function.comp_def]
  rfl

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

/-- A served state with a directory decodes as the full shape decodes its rows. -/
private theorem decode_servedRows_isSome {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) :
    (DirectoryImage.decode registry (servedRows served)).isSome := by
  have rowsDecode := decodeRows_isSome (servedRows served) fun row member => by
    simp only [servedRows, Served.cells, List.map_map, List.mem_map, Function.comp_def] at member
    obtain ⟨cellId, _, same⟩ := member
    subst same
    rw [loaded.decodes cellId.value]
    rfl
  obtain ⟨rows, decoded⟩ := Option.isSome_iff_exists.mp rowsDecode
  have keys := DirectoryImage.decodeRows_keys registry decoded
  have unique : (rows.map Prod.fst).Nodup := by
    rw [keys]
    simp only [servedRows, Served.cells, List.map_map, Function.comp_def]
    exact served.cellIds_nodup.map fun left right same => by
      cases left
      cases right
      simp only at same
      rw [same]
  simp [DirectoryImage.decode, decoded, unique]

theorem loadServedDirectory_ofLoaded {store : StoreIdentity}
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (loadServedDirectory (Served.ofLoaded loaded sameStart)).map (·.directory) =
      (loadDirectory loaded).map (·.directory) := by
  have absent : (Served.ofLoaded loaded sameStart).absentBytes = loaded.image.seed.absentBytes := rfl
  cases full : loadDirectory loaded with
  | some fullLoaded =>
      cases light : loadServedDirectory (Served.ofLoaded loaded sameStart) with
      | none =>
          exfalso
          unfold loadServedDirectory at light
          rw [dif_pos (absent.trans fullLoaded.absentDefault)] at light
          split at light
          · rename_i missing
            obtain ⟨identifier, _, decoded⟩ := HeldImages.write_none missing
            rw [Served.ofLoaded_canonicalBytes, ← fullLoaded.bytes_exact identifier] at decoded
            have roundTrip := LifecycleImage.decode_encode registry
              (LifecycleImage.view registry fullLoaded.directory identifier)
            change (LifecycleImage.codec registry).decode (LifecycleImage.bytes registry _) = _ at roundTrip
            rw [roundTrip] at decoded
            cases decoded
          · cases light
      | some lightLoaded =>
          simp only [Option.map_some]
          congr 1
          apply directory_eq_of_view
          intro identifier
          have bytes := (lightLoaded.bytes_exact identifier).trans
            ((congrFun (Served.ofLoaded_canonicalBytes loaded sameStart) ⟨identifier⟩).trans
              (fullLoaded.bytes_exact identifier).symm)
          have decoded := congrArg (LifecycleImage.rawDecode registry) bytes
          rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at decoded
          exact Option.some.inj decoded
  | none =>
      cases light : loadServedDirectory (Served.ofLoaded loaded sameStart) with
      | none => rfl
      | some lightLoaded =>
          exfalso
          unfold loadDirectory at full
          rw [dif_pos (absent.symm.trans lightLoaded.absentDefault)] at full
          have decodes := decode_servedRows_isSome lightLoaded
          rw [servedRows_ofLoaded loaded sameStart] at decodes
          split at full
          · rename_i missing
            rw [missing] at decodes
            cases decodes
          · cases full

/-- The deployment's authority cell, decoded from the served bytes. No spent
function and no clock are carried: `snapshotOn` takes the clock from the
served height and the spent markers from a verified footprint. -/
structure ServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) where
  private mk ::
  cell : CredentialAuthorityDomain.Cell
  valid : deployment.Valid
  observed : served.canonicalBytes (cellIdOf deployment) = cellBytes cell
  /-- The cell's authorization projection, computed once per served state: every request's
  snapshot (`snapshotOn`) carries this one, not a projection rebuilt per reference. -/
  authState : AuthState
  authStateExact : authState = CredentialAuthorityDomain.authStateOf cell
  /-- The cell's issued index (`CredentialAuthorityDomain.issuedOf`), held beside it and
  forced at its first issuer check: every request's snapshot shares it. -/
  issued : Thunk (List (IssuerId × Epoch × Digest))
  issuedExact : issued.get = CredentialAuthorityDomain.issuedOf deployment.domain cell

def loadServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) : Option (ServedAuthority deployment served) :=
  if valid : deployment.Valid then
    match decoded : decodeCell (served.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell => some ⟨cell, valid, (decodeCell_canonical decoded).symm,
        CredentialAuthorityDomain.authStateOf cell, rfl,
        Thunk.mk fun _ => CredentialAuthorityDomain.issuedOf deployment.domain cell, rfl⟩
  else none

/-- The authority snapshot for a request: the clock is the served height and
the spent markers are the footprint's answers at that height (a marker whose
nullifier the request did not declare reads as its footprint says: a family
must declare it, `DurableView.Family.covers`). -/
def ServedAuthority.snapshotOn {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) : CredentialAuthorityDomain.Snapshot :=
  ⟨deployment.domain, served.height, spentOf deployment.domain (served.viewAt footprint), authority.cell,
    authority.authState, authority.authStateExact, authority.issued, authority.issuedExact⟩

/-- `snapshotOn` is the snapshot `Snapshot.ofCell` builds; only the projection is the held one. -/
theorem ServedAuthority.snapshotOn_eq {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    authority.snapshotOn footprint =
      CredentialAuthorityDomain.Snapshot.ofCell deployment.domain served.height
        (spentOf deployment.domain (served.viewAt footprint)) authority.cell := by
  obtain ⟨cell, valid, observed, authState, exact, issued, issuedExact⟩ := authority
  subst exact
  have held : issued = Thunk.mk fun _ => CredentialAuthorityDomain.issuedOf deployment.domain cell :=
    Thunk.ext issuedExact
  subst held
  rfl

/-- The light authority over a view is the full authority load of that view,
up to the clock: the full shape's clock (`clockOf`, its history length) is its
height (`Served.history_length_eq_height`). -/
theorem ServedAuthority.snapshotOn_cell {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    (authority.snapshotOn footprint).cell = authority.cell ∧
      (authority.snapshotOn footprint).revision = served.height := ⟨rfl, rfl⟩

/-- **The light authority of the full shape's state decodes the full shape's
authority cell.** -/
theorem loadServedAuthority_ofLoaded (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (loadServedAuthority deployment (Served.ofLoaded loaded sameStart)).map (·.cell) =
      (loadDeployment deployment loaded.snapshot).map (·.snapshot.cell) := by
  unfold loadServedAuthority loadDeployment loadDeploymentAt
  by_cases valid : deployment.Valid
  · rw [dif_pos valid, dif_pos valid]
    have bytes : (Served.ofLoaded loaded sameStart).canonicalBytes (cellIdOf deployment) =
        loaded.snapshot.canonicalBytes (cellIdOf deployment) := by
      rw [Served.ofLoaded_canonicalBytes]
    split
    · rename_i servedNone
      split
      · rfl
      · rename_i _ fullSome
        rw [bytes, fullSome] at servedNone
        cases servedNone
    · rename_i _ servedSome
      split
      · rename_i fullNone
        rw [bytes, fullNone] at servedSome
        cases servedSome
      · rename_i _ fullSome
        rw [bytes, fullSome] at servedSome
        cases servedSome
        rfl
  · rw [dif_neg valid, dif_neg valid]
    rfl

/-! ## A later served state, loaded against an earlier one

A session's next served state differs from the one it validated in the cells its
records wrote. These loads reuse the earlier decode wherever a cell's canonical
bytes are unchanged; each is the plain load (`loadServedDirectoryStep_eq`,
`loadServedDirectoryFrom_eq`, `loadServedAuthorityFrom_eq`). -/

/-- `loadServedDirectory` of a state one step after a held one, decoding only the cells the
step wrote (`Served.Moved`: every other cell kept its bytes, so its held image stands). -/
def loadServedDirectoryStep {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) (written : List CellId)
    (moved : Served.Moved before served written) : Option (ServedDirectory served) :=
  if absentDefault : served.absentBytes = [] then
    match stepped : HeldImages.write (fun identifier => served.canonicalBytes ⟨identifier⟩) held.held
        (written.map (·.value)) with
    | none => none
    | some after => some ⟨after, fun identifier => by
        rw [HeldImages.write_some stepped identifier]
        split
        · rfl
        · rename_i unwritten
          rw [held.exact identifier]
          exact (moved.keeps ⟨identifier⟩ fun member =>
            unwritten (List.mem_map.mpr ⟨_, member, rfl⟩)).symm,
        absentDefault⟩
  else none

/-- **The step load is the load**: same refusal, same directory. -/
theorem loadServedDirectoryStep_eq {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) (written : List CellId)
    (moved : Served.Moved before served written) :
    loadServedDirectoryStep held served written moved = loadServedDirectory served := by
  cases stepped : loadServedDirectoryStep held served written moved with
  | some loaded => exact (ServedDirectory.load_eq loaded).symm
  | none =>
      cases computed : loadServedDirectory served with
      | none => rfl
      | some loaded =>
          exfalso
          unfold loadServedDirectoryStep at stepped
          rw [dif_pos loaded.absentDefault] at stepped
          split at stepped
          · rename_i missing
            obtain ⟨identifier, _, decoded⟩ := HeldImages.write_none missing
            rw [loaded.decodes identifier] at decoded
            cases decoded
          · cases stepped

/-- The cells whose bytes differ between two states, over both enumerations. -/
def changedCells {earlier store : StoreIdentity} (before : State earlier) (served : State store) :
    List CellId :=
  (served.cellIds ++ before.cellIds).filter fun cellId =>
    !bytesBEq (before.canonicalBytes cellId) (served.canonicalBytes cellId)

theorem changedCells_moved {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) (absent : served.absentBytes = []) :
    Served.Moved before served (changedCells before served) where
  keeps cellId unchanged := by
    by_cases enumerated : cellId ∈ served.cellIds ++ before.cellIds
    · have same : bytesBEq (before.canonicalBytes cellId) (served.canonicalBytes cellId) = true := by
        by_contra different
        exact unchanged (List.mem_filter.mpr ⟨enumerated, by simpa using different⟩)
      exact (bytesBEq_iff.mp same).symm
    · simp only [List.mem_append, not_or] at enumerated
      rw [served.canonicalBytes_outside cellId enumerated.1, before.canonicalBytes_outside cellId enumerated.2,
        absent, held.absentDefault]

/-- `loadServedDirectory` of a later state, decoding only the cells whose bytes differ from
`held`'s state (`loadServedDirectoryFrom_eq`). -/
def loadServedDirectoryFrom {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) : Option (ServedDirectory served) :=
  if absent : served.absentBytes = [] then
    loadServedDirectoryStep held served (changedCells before served) (changedCells_moved held served absent)
  else none

/-- **The incremental served load is the served load**: same refusal, same directory. -/
theorem loadServedDirectoryFrom_eq {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) :
    loadServedDirectoryFrom held served = loadServedDirectory served := by
  unfold loadServedDirectoryFrom
  split
  · exact loadServedDirectoryStep_eq _ _ _ _
  · rename_i absent
    unfold loadServedDirectory
    rw [dif_neg absent]

/-- Two authorities of one served state are equal. -/
theorem ServedAuthority.unique {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (left right : ServedAuthority deployment served) : left = right := by
  have same : left.cell = right.cell := by
    have decoded := congrArg decodeCell (left.observed.symm.trans right.observed)
    rw [decodeCell_bytes, decodeCell_bytes] at decoded
    exact Option.some.inj decoded
  obtain ⟨leftCell, _, _, leftState, leftExact, leftIssued, leftIssuedExact⟩ := left
  obtain ⟨rightCell, _, _, rightState, rightExact, rightIssued, rightIssuedExact⟩ := right
  simp only at same
  subst same leftExact rightExact
  have issued : leftIssued = rightIssued := Thunk.ext (leftIssuedExact.trans rightIssuedExact.symm)
  subst issued
  rfl

/-- Loading a state that has an authority yields that authority. -/
theorem ServedAuthority.load_eq {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) :
    loadServedAuthority deployment served = some authority := by
  unfold loadServedAuthority
  rw [dif_pos authority.valid]
  split
  · rename_i missing
    rw [authority.observed, decodeCell_bytes] at missing
    cases missing
  · exact congrArg some (ServedAuthority.unique _ authority)

/-- `loadServedAuthority` of a later state: the held cell when the authority
cell's bytes are unchanged, otherwise the bytes decoded and stepped relative to
`held.cell` (`loadServedAuthorityFrom_eq`). -/
def loadServedAuthorityFrom {deployment : CanonicalCellRegistry.Deployment} {earlier store : StoreIdentity}
    {before : State earlier} (held : ServedAuthority deployment before) (served : State store) :
    Option (ServedAuthority deployment served) :=
  if same : bytesBEq (served.canonicalBytes (cellIdOf deployment))
      (before.canonicalBytes (cellIdOf deployment)) then
    some ⟨held.cell, held.valid, (bytesBEq_iff.mp same).trans held.observed,
      held.authState, held.authStateExact, held.issued, held.issuedExact⟩
  else
    match decoded : decodeCell (served.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell =>
        let stepped := held.cell.relativeTo cell
        some ⟨stepped, held.valid,
          (decodeCell_canonical decoded).symm.trans
            (congrArg cellBytes (CellState.Materialized.relativeTo_eq held.cell cell).symm),
          CredentialAuthorityDomain.authStateOf stepped, rfl,
          Thunk.mk fun _ => CredentialAuthorityDomain.issuedOf deployment.domain stepped, rfl⟩

theorem loadServedAuthorityFrom_eq {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (held : ServedAuthority deployment before)
    (served : State store) :
    loadServedAuthorityFrom held served = loadServedAuthority deployment served := by
  unfold loadServedAuthorityFrom
  split
  · exact (ServedAuthority.load_eq _).symm
  · split
    · rename_i missing
      unfold loadServedAuthority
      rw [dif_pos held.valid]
      split
      · rfl
      · rename_i _ present
        rw [missing] at present
        cases present
    · exact (ServedAuthority.load_eq _).symm

/-- An authority cell the Host itself wrote, beside the bytes it encoded it to: a write's
post-cell (`ResourceBirthAuthority.post`, a patch applied to the pre-cell, so its kept trie
follows the pre-cell's by the patch instead of being built). -/
structure HeldCell where
  cell : CredentialAuthorityDomain.Cell
  bytes : List UInt8
  exact : bytes = cellBytes cell

/-- The held cell of a post-cell. -/
def HeldCell.ofCell (cell : CredentialAuthorityDomain.Cell) : HeldCell := ⟨cell, cellBytes cell, rfl⟩

/-- `loadServedAuthorityFrom` given the post-cell of the write that produced `served`: when
the served authority bytes are that cell's, the cell is taken as it is, without decoding the
bytes or rebuilding its trie; otherwise `loadServedAuthorityFrom`. `loadServedAuthorityHeld_eq`:
it is `loadServedAuthority`. -/
def loadServedAuthorityHeld {deployment : CanonicalCellRegistry.Deployment} {earlier store : StoreIdentity}
    {before : State earlier} (prior : ServedAuthority deployment before) (held : Option HeldCell)
    (served : State store) : Option (ServedAuthority deployment served) :=
  match held with
  | some post =>
      if same : bytesBEq (served.canonicalBytes (cellIdOf deployment)) post.bytes then
        some ⟨post.cell, prior.valid, (bytesBEq_iff.mp same).trans post.exact,
          CredentialAuthorityDomain.authStateOf post.cell, rfl,
          Thunk.mk fun _ => CredentialAuthorityDomain.issuedOf deployment.domain post.cell, rfl⟩
      else loadServedAuthorityFrom prior served
  | none => loadServedAuthorityFrom prior served

theorem loadServedAuthorityHeld_eq {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (prior : ServedAuthority deployment before)
    (held : Option HeldCell) (served : State store) :
    loadServedAuthorityHeld prior held served = loadServedAuthority deployment served := by
  unfold loadServedAuthorityHeld
  split
  · split
    · exact (ServedAuthority.load_eq _).symm
    · exact loadServedAuthorityFrom_eq prior served
  · exact loadServedAuthorityFrom_eq prior served

/-- Teeth: a held cell whose bytes are not the served ones is not taken; the served bytes are
decoded instead. -/
theorem loadServedAuthorityHeld_other {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (prior : ServedAuthority deployment before)
    (post : HeldCell) (served : State store)
    (other : served.canonicalBytes (cellIdOf deployment) ≠ post.bytes) :
    loadServedAuthorityHeld prior (some post) served = loadServedAuthorityFrom prior served := by
  dsimp only [loadServedAuthorityHeld]
  rw [dif_neg (fun same => other (bytesBEq_iff.mp same))]

/-- Satisfiable: a held cell whose bytes are the served ones is the loaded cell. -/
theorem loadServedAuthorityHeld_taken {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (prior : ServedAuthority deployment before)
    (post : HeldCell) (served : State store)
    (same : served.canonicalBytes (cellIdOf deployment) = post.bytes) :
    ((loadServedAuthorityHeld prior (some post) served).map (·.cell)) = some post.cell := by
  dsimp only [loadServedAuthorityHeld]
  rw [dif_pos (bytesBEq_iff.mpr same)]
  rfl

#assert_axioms loadServedAuthorityHeld_eq
#assert_axioms loadServedAuthorityHeld_other
#assert_axioms loadServedAuthorityHeld_taken

#assert_axioms ServedDirectory.bytes_exact
#assert_axioms ServedDirectory.slots_eq_of_bytes
#assert_axioms loadServedDirectory_ofLoaded
#assert_axioms loadServedAuthority_ofLoaded
#assert_axioms loadServedDirectoryFrom_eq
#assert_axioms loadServedDirectoryStep_eq
#assert_axioms ServedDirectory.unique
#assert_axioms loadServedAuthorityFrom_eq

end Minidregg.Compiler.CredentialAuthorityServed
