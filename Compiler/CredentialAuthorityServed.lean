/-
# Compiler.CredentialAuthorityServed — the directory and the authority cell of a served state

KN2 stage 2b-1. The light counterparts of `CredentialAuthorityDomainReceiver`'s
`LoadedDirectory` and `Loaded` (the authority domain), over a `Served` state
instead of the full verified materialization:

* `ServedDirectory served`: the complete physical directory of the served
  state (every enumerable cell, tombstones included), decoded once;
  `bytes_exact` holds at every identifier, inside or outside the enumeration.
* `ServedAuthority deployment served`: the deployment's authority cell decoded
  from the served bytes. It carries NO spent function: the authority clock is
  the served height (`snapshotOn`'s revision) and a spent marker is read only
  through a `VerifiedFootprint` that declares its nullifier (`snapshotOn`).

`loadServedDirectory_ofLoaded` / `loadServedAuthority_ofLoaded`: on the full
shape's state the light loads decode exactly what the full loads decode.
-/
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.DurableServed

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

/-- The complete physical directory of a served state, decoded once. -/
structure ServedDirectory {store : StoreIdentity} (served : State store) where
  private mk ::
  directory : Directory Nat registry
  decoded : DirectoryImage.decode registry (servedRows served) = some directory
  absentDefault : served.absentBytes = []

def loadServedDirectory {store : StoreIdentity} (served : State store) : Option (ServedDirectory served) :=
  if absentDefault : served.absentBytes = [] then
    match decoded : DirectoryImage.decode registry (servedRows served) with
    | none => none
    | some directory => some ⟨directory, decoded, absentDefault⟩
  else none

private theorem lookup_enumeration (identifiers : List CellId)
    (bytes : CellId → List UInt8) (identifier : Nat) :
    ((identifiers.map fun selected => (selected.value, bytes selected)).lookup identifier).getD [] =
      if (⟨identifier⟩ : CellId) ∈ identifiers then bytes ⟨identifier⟩ else [] := by
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
theorem ServedDirectory.bytes_exact {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) (identifier : Nat) :
    LifecycleImage.bytes registry (LifecycleImage.view registry loaded.directory identifier) =
      served.canonicalBytes ⟨identifier⟩ := by
  rw [DirectoryImage.decode_exact registry loaded.decoded identifier]
  simp only [servedRows, Served.cells, List.map_map, Function.comp_def]
  rw [lookup_enumeration]
  split
  next => rfl
  next outside => exact ((served.canonicalBytes_outside ⟨identifier⟩ outside).trans loaded.absentDefault).symm

/-- Two directories of one served state are equal. -/
theorem ServedDirectory.unique {store : StoreIdentity} {served : State store}
    (left right : ServedDirectory served) : left = right := by
  have same : left.directory = right.directory :=
    Option.some.inj (left.decoded.symm.trans right.decoded)
  cases left
  cases right
  simp only at same
  subst same
  rfl

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
  simp only [servedRows, directoryRows, Served.cells, DurableReceiverIO.Loaded.cells_eq_cellsCached,
    DurableReceiverIO.Loaded.cellsCached, List.map_map, Function.comp_def]
  rfl

theorem loadServedDirectory_ofLoaded {store : StoreIdentity}
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (loadServedDirectory (Served.ofLoaded loaded sameStart)).map (·.directory) =
      (loadDirectory loaded).map (·.directory) := by
  unfold loadServedDirectory loadDirectory
  have absent : (Served.ofLoaded loaded sameStart).absentBytes = loaded.image.seed.absentBytes := rfl
  by_cases fresh : loaded.image.seed.absentBytes = []
  · rw [dif_pos (absent.trans fresh), dif_pos fresh]
    have rows := servedRows_ofLoaded loaded sameStart
    split
    · rename_i servedNone
      split
      · rfl
      · rename_i _ fullSome
        rw [rows, fullSome] at servedNone
        cases servedNone
    · rename_i _ servedSome
      split
      · rename_i fullNone
        rw [rows, fullNone] at servedSome
        cases servedSome
      · rename_i _ fullSome
        rw [rows, fullSome] at servedSome
        cases servedSome
        rfl
  · rw [dif_neg (fun h => fresh (absent.symm.trans h)), dif_neg fresh]
    rfl

/-- The deployment's authority cell, decoded from the served bytes. No spent
function and no clock are carried: `snapshotOn` takes the clock from the
served height and the spent markers from a verified footprint. -/
structure ServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) where
  private mk ::
  cell : CredentialAuthorityDomain.Cell
  valid : deployment.Valid
  observed : served.canonicalBytes (cellIdOf deployment) = cellBytes cell

def loadServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) : Option (ServedAuthority deployment served) :=
  if valid : deployment.Valid then
    match decoded : decodeCell (served.canonicalBytes (cellIdOf deployment)) with
    | none => none
    | some cell => some ⟨cell, valid, (decodeCell_canonical decoded).symm⟩
  else none

/-- The authority snapshot for a request: the clock is the served height and
the spent markers are the footprint's answers at that height (a marker whose
nullifier the request did not declare reads as its footprint says: a family
must declare it, `DurableView.Family.covers`). -/
def ServedAuthority.snapshotOn {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) : CredentialAuthorityDomain.Snapshot :=
  CredentialAuthorityDomain.Snapshot.ofCell deployment.domain served.height
    (spentOf deployment.domain (served.viewAt footprint)) authority.cell

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
  unfold loadServedAuthority loadDeployment
  by_cases valid : deployment.Valid
  · rw [dif_pos valid, dif_pos valid]
    have bytes : (Served.ofLoaded loaded sameStart).canonicalBytes (cellIdOf deployment) =
        loaded.snapshot.canonicalBytes (cellIdOf deployment) := rfl
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

#assert_axioms ServedDirectory.bytes_exact
#assert_axioms ServedDirectory.slots_eq_of_bytes
#assert_axioms loadServedDirectory_ofLoaded
#assert_axioms loadServedAuthority_ofLoaded

end Minidregg.Compiler.CredentialAuthorityServed
