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
open Minidregg.Compiler.CredentialAuthorityLayout (RealizesAuthority loadCell stepCell loadCell_realizes
  loadCell_of_realizes stepCell_realizes stepCell_of_realizes)
open Minidregg.Compiler.DurableServed (Served)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (VerifiedFootprint)
open Minidregg.Kernel.DurableDataIntent (CellId)
open Minidregg.Kernel.DurableView (Keys)

set_option autoImplicit false

abbrev State (store : StoreIdentity) := Served ResourceBirthCodec.rootBytes store

def servedRows {store : StoreIdentity} (served : State store) : List (Nat × List UInt8) :=
  served.cells.map fun row => (row.1.value, row.2)

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

theorem loadServedDirectory_ofLoaded {store : StoreIdentity}
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (loadServedDirectory (Served.ofLoaded loaded sameStart)).map (·.directory) =
      (loadDirectory loaded).map (·.directory) := by
  have absent : (Served.ofLoaded loaded sameStart).absentBytes = loaded.image.seed.absentBytes := rfl
  cases light : loadServedDirectory (Served.ofLoaded loaded sameStart) with
  | some lightLoaded =>
      cases full : loadDirectory loaded with
      | some fullLoaded =>
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
          exfalso
          unfold loadDirectory at full
          rw [dif_pos (absent.symm.trans lightLoaded.absentDefault)] at full
          obtain ⟨identifier, _, decoded⟩ := loadDirectoryWriting_none full
          have decodes := lightLoaded.decodes identifier
          rw [Served.ofLoaded_canonicalBytes, decoded] at decodes
          cases decodes
  | none =>
      cases full : loadDirectory loaded with
      | none => rfl
      | some fullLoaded =>
          exfalso
          unfold loadServedDirectory at light
          rw [dif_pos (absent.trans fullLoaded.absentDefault)] at light
          split at light
          · rename_i missing
            obtain ⟨identifier, _, decoded⟩ := HeldImages.write_none missing
            rw [Served.ofLoaded_canonicalBytes, fullLoaded.decodes identifier] at decoded
            cases decoded
          · cases light

/-- The enumerable cells of a served state, as identifiers. -/
def servedEnumerated {store : StoreIdentity} (served : State store) : List Nat :=
  served.cellIds.map (·.value)

/-- Outside its enumeration a served state whose absent default is `[]` holds no bytes. -/
theorem servedEnumerated_support {store : StoreIdentity} (served : State store)
    (absentDefault : served.absentBytes = []) (cellId : Nat) (outside : cellId ∉ servedEnumerated served) :
    served.canonicalBytes ⟨cellId⟩ = [] :=
  (served.canonicalBytes_outside ⟨cellId⟩ fun member =>
    outside (List.mem_map.mpr ⟨_, member, rfl⟩)).trans absentDefault

/-- The deployment's authority store, as the cells of the served state realise it (the head at
the pinned identifier and one entry cell per address: `RealizesAuthority`). No spent
function and no clock are carried: `snapshotOn` takes the clock from the
served height and the spent markers from a verified footprint. -/
structure ServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) where
  private mk ::
  cell : CredentialAuthorityDomain.Cell
  valid : deployment.Valid
  absentDefault : served.absentBytes = []
  observed : RealizesAuthority served.canonicalBytes deployment.authorityCellId cell.logical
  /-- The cell's authorization projection, computed once per served state: every request's
  snapshot (`snapshotOn`) carries this one, not a projection rebuilt per reference. -/
  authState : AuthState
  authStateExact : authState = CredentialAuthorityDomain.authStateOf cell

/-- The served authority over a cell the served cells realise. -/
private def ServedAuthority.ofCell (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) (cell : CredentialAuthorityDomain.Cell) (valid : deployment.Valid)
    (absentDefault : served.absentBytes = [])
    (observed : RealizesAuthority served.canonicalBytes deployment.authorityCellId cell.logical) :
    ServedAuthority deployment served :=
  ⟨cell, valid, absentDefault, observed, CredentialAuthorityDomain.authStateOf cell, rfl⟩

/-- An open: every enumerable cell read once, the head checked against the store they hold
(`CredentialAuthorityLayout.loadCell`). -/
def loadServedAuthority (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (served : State store) : Option (ServedAuthority deployment served) :=
  if valid : deployment.Valid then
    if absentDefault : served.absentBytes = [] then
      match loaded : loadCell served.canonicalBytes deployment.authorityCellId (servedEnumerated served) with
      | none => none
      | some cell => some (ServedAuthority.ofCell deployment served cell valid absentDefault
          (loadCell_realizes (servedEnumerated_support served absentDefault) loaded))
    else none
  else none

/-- The authority snapshot for a request: the clock is the served height and
the spent markers are the footprint's answers at that height (a marker whose
nullifier the request did not declare reads as its footprint says: a family
must declare it, `DurableView.Family.covers`). -/
def ServedAuthority.snapshotOn {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) : CredentialAuthorityDomain.Snapshot :=
  ⟨deployment.domain, served.height, spentOf deployment.domain (served.viewAt footprint), authority.cell,
    authority.authState, authority.authStateExact⟩

/-- `snapshotOn` is the snapshot `Snapshot.ofCell` builds; only the projection is the held one. -/
theorem ServedAuthority.snapshotOn_eq {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    authority.snapshotOn footprint =
      CredentialAuthorityDomain.Snapshot.ofCell deployment.domain served.height
        (spentOf deployment.domain (served.viewAt footprint)) authority.cell := by
  obtain ⟨cell, valid, absentDefault, observed, authState, exact⟩ := authority
  subst exact
  rfl

/-- The light authority over a view is the full authority load of that view,
up to the clock: the full shape's clock (`clockOf`, its history length) is its
height (`Served.history_length_eq_height`). -/
theorem ServedAuthority.snapshotOn_cell {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    (authority.snapshotOn footprint).cell = authority.cell ∧
      (authority.snapshotOn footprint).revision = served.height := ⟨rfl, rfl⟩

/-- Two authorities of one served state are equal: the cells determine the store. -/
theorem ServedAuthority.unique {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (left right : ServedAuthority deployment served) : left = right := by
  have same : left.cell = right.cell :=
    CellState.Materialized.ext (left.observed.unique right.observed)
  obtain ⟨leftCell, _, _, _, leftState, leftExact⟩ := left
  obtain ⟨rightCell, _, _, _, rightState, rightExact⟩ := right
  simp only at same
  subst same leftExact rightExact
  rfl

/-- The open loads every store the served cells realise. -/
theorem loadServedAuthority_of_realizes {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (valid : deployment.Valid) (absentDefault : served.absentBytes = [])
    {logical : Theory.Store.Store CredentialAuthorityState.layout}
    (realized : RealizesAuthority served.canonicalBytes deployment.authorityCellId logical) :
    ∃ authority, loadServedAuthority deployment served = some authority ∧ authority.cell.logical = logical := by
  obtain ⟨cell, found, same⟩ :=
    loadCell_of_realizes (servedEnumerated_support served absentDefault) realized
  unfold loadServedAuthority
  rw [dif_pos valid, dif_pos absentDefault]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other loaded
    rw [found] at loaded
    cases loaded
    exact ⟨_, rfl, same⟩

/-- Loading a state that has an authority yields that authority. -/
theorem ServedAuthority.load_eq {deployment : CanonicalCellRegistry.Deployment} {store : StoreIdentity}
    {served : State store} (authority : ServedAuthority deployment served) :
    loadServedAuthority deployment served = some authority := by
  obtain ⟨other, found, _⟩ :=
    loadServedAuthority_of_realizes authority.valid authority.absentDefault authority.observed
  rw [found, ServedAuthority.unique other authority]

/-- **The light authority of the full shape's state is the full shape's authority**: the same
cell, and the same refusal. -/
theorem loadServedAuthority_ofLoaded (deployment : CanonicalCellRegistry.Deployment) {store : StoreIdentity}
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (loadServedAuthority deployment (Served.ofLoaded loaded sameStart)).map (·.cell) =
      (loadDeployment deployment loaded).map (·.snapshot.cell) := by
  have bytes : (Served.ofLoaded loaded sameStart).canonicalBytes = loaded.snapshot.canonicalBytes :=
    Served.ofLoaded_canonicalBytes loaded sameStart
  have absent : (Served.ofLoaded loaded sameStart).absentBytes = loaded.image.seed.absentBytes := rfl
  cases light : loadServedAuthority deployment (Served.ofLoaded loaded sameStart) with
  | some lightLoaded =>
      have realized : RealizesAuthority loaded.snapshot.canonicalBytes deployment.authorityCellId
          lightLoaded.cell.logical := bytes ▸ lightLoaded.observed
      obtain ⟨fullLoaded, found, same⟩ := loadDeployment_exact deployment loaded lightLoaded.valid
        (absent.symm.trans lightLoaded.absentDefault) lightLoaded.cell.logical realized
      rw [found]
      exact congrArg some (CellState.Materialized.ext same.symm)
  | none =>
      cases full : loadDeployment deployment loaded with
      | none => rfl
      | some fullLoaded =>
          exfalso
          have absentDefault : loaded.image.seed.absentBytes = [] := by
            unfold loadDeployment loadDeploymentAt at full
            split at full
            · assumption
            · cases full
          have realized : RealizesAuthority (Served.ofLoaded loaded sameStart).canonicalBytes
              deployment.authorityCellId fullLoaded.snapshot.cell.logical := bytes ▸ fullLoaded.observed
          obtain ⟨_, found, _⟩ := loadServedAuthority_of_realizes fullLoaded.valid
            (absent.trans absentDefault) realized
          rw [found] at light
          cases light

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
    (beforeAbsent : before.absentBytes = []) (served : State store) (absent : served.absentBytes = []) :
    Served.Moved before served (changedCells before served) where
  keeps cellId unchanged := by
    by_cases enumerated : cellId ∈ served.cellIds ++ before.cellIds
    · have same : bytesBEq (before.canonicalBytes cellId) (served.canonicalBytes cellId) = true := by
        by_contra different
        exact unchanged (List.mem_filter.mpr ⟨enumerated, by simpa using different⟩)
      exact (bytesBEq_iff.mp same).symm
    · simp only [List.mem_append, not_or] at enumerated
      rw [served.canonicalBytes_outside cellId enumerated.1, before.canonicalBytes_outside cellId enumerated.2,
        absent, beforeAbsent]

/-- `loadServedDirectory` of a later state, decoding only the cells whose bytes differ from
`held`'s state (`loadServedDirectoryFrom_eq`). -/
def loadServedDirectoryFrom {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) : Option (ServedDirectory served) :=
  if absent : served.absentBytes = [] then
    loadServedDirectoryStep held served (changedCells before served) (changedCells_moved held.absentDefault served absent)
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

/-- `loadServedAuthority` of a state one step after a held one: the held cell is followed along
the cells the step wrote (`CredentialAuthorityLayout.stepCell`: one decode and one path of the
kept structure per written entry), then the head is checked against it. The rest of the store is
not read. `loadServedAuthorityStep_eq`: it is `loadServedAuthority`. -/
def loadServedAuthorityStep {deployment : CanonicalCellRegistry.Deployment} {earlier store : StoreIdentity}
    {before : State earlier} (prior : ServedAuthority deployment before) (served : State store)
    (written : List CellId) (moved : Served.Moved before served written) :
    Option (ServedAuthority deployment served) :=
  if absentDefault : served.absentBytes = [] then
    match stepped : stepCell before.canonicalBytes served.canonicalBytes deployment.authorityCellId
        prior.cell (written.map (·.value)) with
    | none => none
    | some cell => some (ServedAuthority.ofCell deployment served cell prior.valid absentDefault
        (stepCell_realizes prior.observed (fun cellId unwritten => moved.keeps ⟨cellId⟩ fun member =>
          unwritten (List.mem_map.mpr ⟨_, member, rfl⟩)) stepped))
  else none

theorem loadServedAuthorityStep_eq {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (prior : ServedAuthority deployment before)
    (served : State store) (written : List CellId) (moved : Served.Moved before served written) :
    loadServedAuthorityStep prior served written moved = loadServedAuthority deployment served := by
  cases stepped : loadServedAuthorityStep prior served written moved with
  | some loaded => exact (ServedAuthority.load_eq loaded).symm
  | none =>
      cases full : loadServedAuthority deployment served with
      | none => rfl
      | some other =>
          exfalso
          obtain ⟨cell, found, _⟩ := stepCell_of_realizes (written := written.map (·.value))
            prior.observed (fun cellId unwritten => moved.keeps ⟨cellId⟩ fun member =>
              unwritten (List.mem_map.mpr ⟨_, member, rfl⟩)) other.observed
          unfold loadServedAuthorityStep at stepped
          rw [dif_pos other.absentDefault] at stepped
          split at stepped
          · rename_i missing
            rw [found] at missing
            cases missing
          · cases stepped

/-- `loadServedAuthority` of a later state against a held one, with no record of what was
written: the cells whose bytes differ are found by comparison (`changedCells`) and the held cell
is stepped along them. `loadServedAuthorityFrom_eq`: it is `loadServedAuthority`. -/
def loadServedAuthorityFrom {deployment : CanonicalCellRegistry.Deployment} {earlier store : StoreIdentity}
    {before : State earlier} (held : ServedAuthority deployment before) (served : State store) :
    Option (ServedAuthority deployment served) :=
  if absent : served.absentBytes = [] then
    loadServedAuthorityStep held served (changedCells before served)
      (changedCells_moved held.absentDefault served absent)
  else none

theorem loadServedAuthorityFrom_eq {deployment : CanonicalCellRegistry.Deployment}
    {earlier store : StoreIdentity} {before : State earlier} (held : ServedAuthority deployment before)
    (served : State store) :
    loadServedAuthorityFrom held served = loadServedAuthority deployment served := by
  unfold loadServedAuthorityFrom
  split
  · exact loadServedAuthorityStep_eq _ _ _ _
  · rename_i absent
    unfold loadServedAuthority
    split
    all_goals first | rfl | simp [absent]

#assert_axioms loadServedAuthorityStep_eq

#assert_axioms ServedDirectory.bytes_exact
#assert_axioms ServedDirectory.slots_eq_of_bytes
#assert_axioms loadServedDirectory_ofLoaded
#assert_axioms loadServedAuthority_ofLoaded
#assert_axioms loadServedDirectoryFrom_eq
#assert_axioms loadServedDirectoryStep_eq
#assert_axioms ServedDirectory.unique
#assert_axioms loadServedAuthorityFrom_eq

end Minidregg.Compiler.CredentialAuthorityServed
