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
  simp only [servedRows, directoryRows, Served.cells, Served.ofLoaded_canonicalBytes,
    DurableReceiverIO.Loaded.cells_eq_cellsCached, DurableReceiverIO.Loaded.cellsCached, List.map_map,
    Function.comp_def]
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
bytes are unchanged; each is the plain load (`loadServedDirectoryFrom_eq`,
`loadServedAuthorityFrom_eq`). -/

/-- Loading a state that has a directory yields that directory. -/
theorem ServedDirectory.load_eq {store : StoreIdentity} {served : State store}
    (loaded : ServedDirectory served) : loadServedDirectory served = some loaded := by
  unfold loadServedDirectory
  rw [dif_pos loaded.absentDefault]
  split
  · rename_i missing
    rw [loaded.decoded] at missing
    cases missing
  · exact congrArg some (ServedDirectory.unique _ loaded)

/-- One directory row of a later state: the held view when the identifier's
bytes equal the held state's, otherwise the bytes decoded and stepped relative
to the held view. -/
def decodeServedRowFrom {earlier : StoreIdentity} {before : State earlier} (held : ServedDirectory before)
    (identifier : Nat) (bytes : List UInt8) : Option (LifecycleImage registry) :=
  let priorView := LifecycleImage.view registry held.directory identifier
  if bytesBEq (before.canonicalBytes ⟨identifier⟩) bytes then
    some priorView
  else
    ((LifecycleImage.codec registry).decode bytes).map
      (LifecycleImage.relativeTo registry priorView)

theorem decodeServedRowFrom_eq {earlier : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (identifier : Nat) (bytes : List UInt8) :
    decodeServedRowFrom held identifier bytes = (LifecycleImage.codec registry).decode bytes := by
  unfold decodeServedRowFrom
  split
  next same =>
    have exact : LifecycleImage.bytes registry
        (LifecycleImage.view registry held.directory identifier) = bytes :=
      (held.bytes_exact identifier).trans (bytesBEq_iff.mp same)
    rw [← exact]
    exact (LifecycleImage.decode_encode registry _).symm
  next =>
    cases (LifecycleImage.codec registry).decode bytes <;> simp [LifecycleImage.relativeTo_eq]

def decodeServedRowsFrom {earlier : StoreIdentity} {before : State earlier} (held : ServedDirectory before) :
    List (Nat × List UInt8) → Option (DirectoryImage.Rows registry)
  | [] => some []
  | (identifier, bytes) :: rest => do
      let image ← decodeServedRowFrom held identifier bytes
      let tail ← decodeServedRowsFrom held rest
      some ((identifier, image) :: tail)

theorem decodeServedRowsFrom_eq {earlier : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) :
    ∀ input : List (Nat × List UInt8),
      decodeServedRowsFrom held input = DirectoryImage.decodeRows registry input
  | [] => rfl
  | (identifier, bytes) :: rest => by
      simp only [decodeServedRowsFrom, DirectoryImage.decodeRows, decodeServedRowFrom_eq,
        decodeServedRowsFrom_eq held rest]

/-- The served directory of `input`; its identity check is one hashed pass over the row ids
(`CompiledListOps.nodupNat`), not the pairwise `List.Nodup` decision, which compared every pair of
big-number ids on every submit. -/
def decodeServedFrom {earlier : StoreIdentity} {before : State earlier} (held : ServedDirectory before)
    (input : List (Nat × List UInt8)) : Option (Directory Nat registry) := do
  let rows ← decodeServedRowsFrom held input
  if CompiledListOps.nodupNat (rows.map Prod.fst) then some (DirectoryImage.ofRows registry rows) else none

theorem decodeServedFrom_eq {earlier : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (input : List (Nat × List UInt8)) :
    decodeServedFrom held input = DirectoryImage.decode registry input := by
  simp only [decodeServedFrom, DirectoryImage.decode, decodeServedRowsFrom_eq]
  cases DirectoryImage.decodeRows registry input with
  | none => rfl
  | some rows =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      by_cases unique : (rows.map Prod.fst).Nodup
      · rw [if_pos unique, if_pos ((CompiledListOps.nodupNat_iff _).mpr unique)]
      · rw [if_neg unique, if_neg (fun fast => unique ((CompiledListOps.nodupNat_iff _).mp fast))]

/-- `loadServedDirectory` of a later state, decoding only the rows whose bytes
differ from `held`'s state (`loadServedDirectoryFrom_eq`). -/
def loadServedDirectoryFrom {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) : Option (ServedDirectory served) :=
  if absentDefault : served.absentBytes = [] then
    match decoded : decodeServedFrom held (servedRows served) with
    | none => none
    | some directory =>
        some ⟨directory, (decodeServedFrom_eq held (servedRows served)).symm.trans decoded, absentDefault⟩
  else none

/-- **The incremental served load is the served load**: same refusal, same directory. -/
theorem loadServedDirectoryFrom_eq {earlier store : StoreIdentity} {before : State earlier}
    (held : ServedDirectory before) (served : State store) :
    loadServedDirectoryFrom held served = loadServedDirectory served := by
  cases computed : loadServedDirectory served with
  | some loaded =>
      cases incremental : loadServedDirectoryFrom held served with
      | some other => exact congrArg some (ServedDirectory.unique other loaded)
      | none =>
          exfalso
          unfold loadServedDirectoryFrom at incremental
          rw [dif_pos loaded.absentDefault] at incremental
          split at incremental
          · rename_i missing
            rw [decodeServedFrom_eq, loaded.decoded] at missing
            cases missing
          · cases incremental
  | none =>
      cases incremental : loadServedDirectoryFrom held served with
      | none => rfl
      | some other =>
          exfalso
          rw [ServedDirectory.load_eq other] at computed
          cases computed

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
#assert_axioms loadServedAuthorityFrom_eq

end Minidregg.Compiler.CredentialAuthorityServed
