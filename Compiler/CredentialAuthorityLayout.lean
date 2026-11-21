/-
# Compiler.CredentialAuthorityLayout -- the authority store's physical layout

The authority domain keeps one logical `Store` over `CredentialAuthorityState.layout` and its
logical root (`CredentialAuthorityCell.materializer`, a kept trie). Its physical image is the
cells of `Compiler.CredentialAuthorityEntry`, each the registry's `.authority` kind: one HEAD at
the deployment's pinned `authorityCellId` holding the logical root, and one ENTRY per store
address at that address's own injective coordinate.

* `RealizesAuthority bytesAt authorityCellId logical`: the cells `bytesAt` holds are the image of
  `logical`. The store is a function of the bytes (`RealizesAuthority.unique`).
* `lowerAuthority`: the lowering of a logical update, the head write and one write per touched
  address. `lower_realizes`: installing it over a state that realises the pre-store realises the
  post-store, whatever else the intent writes outside the authority kind.
* `Update`: a post cell with the addresses it touched and the proof that every other address
  kept its value. A writer hands the lowering an `Update`, so an omitted entry write is a type
  error, not a runtime divergence.
* `loadStore` (an open: every enumerable cell once) and `stepStore` (a step: the written cells
  only) rebuild the logical store from the cells; both are exact (`loadStore_exact`,
  `stepStore_exact`).
* `BirthAuthorityWritesBounded`: the keystone for a birth's authority writes.
-/
module

public import Kernel.DurableDataIntent
public import Compiler.CanonicalCellRegistry
public import Compiler.CredentialAuthorityEntry
public import Compiler.ResourceBirthCodec
public import Compiler.DurableReceiverCodec
public import Compiler.Sp800185Cshake256
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

@[expose] public section

namespace Minidregg.Compiler.CredentialAuthorityLayout

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityCell (keyStream valueStream)
open Minidregg.Compiler.CredentialAuthorityEntry
open Minidregg.Compiler.CanonicalCellRegistry (registry)
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CellRegistry (TypeRegistry PackedCell)

set_option autoImplicit false

/-! ## The lifecycle image of a live authority cell -/

def packedCell (cell : PhysicalCell) : PackedCell registry := ⟨.authority, cell⟩

/-- The canonical bytes of a live authority cell: the registry's lifecycle image. -/
def encodeCell (cell : PhysicalCell) : List UInt8 :=
  LifecycleImage.bytes registry (.live (packedCell cell))

/-- The eight octets every live authority image begins with: the live lifecycle tag and the
packed-cell envelope of kind tag 3. -/
def imagePrefix : List UInt8 := [68, 82, 2, 1, 68, 82, 1, 3]

/-- Decode a live cell of the authority kind; any other kind, a retired or a never-used image and
non-canonical bytes hold none. The prefix is compared first, so the bytes of a cell of another
kind are never decoded. -/
def decodeCell (bytes : List UInt8) : Option PhysicalCell :=
  if bytes.take 8 = imagePrefix then
    match (LifecycleImage.codec registry).decode bytes with
    | some (.live ⟨.authority, payload⟩) => some payload
    | _ => none
  else none

theorem encodeCell_eq (cell : PhysicalCell) : encodeCell cell = imagePrefix ++ cell.bytes := rfl

theorem encodeCell_length (cell : PhysicalCell) : (encodeCell cell).length = 8 + cell.bytes.length := by
  rw [encodeCell_eq, List.length_append]; rfl

/-- `decodeCell` on any bytes that decode to this live cell. Proved at a variable `bytes`, so the
kernel never runs the decoder on a concrete image. -/
theorem decodeCell_of_decode {bytes : List UInt8} {cell : PhysicalCell}
    (decoded : (LifecycleImage.codec registry).decode bytes = some (.live (packedCell cell))) :
    decodeCell bytes = some cell := by
  have exact : encodeCell cell = bytes := LifecycleImage.decode_canonical registry decoded
  have starts : bytes.take 8 = imagePrefix := by
    rw [← exact, encodeCell_eq]; rfl
  unfold decodeCell
  rw [if_pos starts, decoded]
  rfl

theorem decodeCell_encodeCell (cell : PhysicalCell) : decodeCell (encodeCell cell) = some cell :=
  decodeCell_of_decode (show (LifecycleImage.codec registry).decode
    ((LifecycleImage.codec registry).encode (.live (packedCell cell))) = _ from
      LifecycleImage.decode_encode _ _)

theorem decodeCell_canonical {bytes : List UInt8} {cell : PhysicalCell}
    (decoded : decodeCell bytes = some cell) : encodeCell cell = bytes := by
  unfold decodeCell at decoded
  split at decoded
  · split at decoded
    · rename_i payload image
      cases Option.some.inj decoded
      exact LifecycleImage.decode_canonical registry image
    · cases decoded
  · cases decoded

/-- A never-used identifier holds no authority cell. -/
theorem decodeCell_nil : decodeCell [] = none := rfl

/-- A live cell of any other kind holds no authority cell. -/
theorem decodeCell_other_kind {bytes : List UInt8} {cell : PackedCell registry}
    (decoded : (LifecycleImage.codec registry).decode bytes = some (.live cell))
    (other : cell.kind ≠ .authority) : decodeCell bytes = none := by
  unfold decodeCell
  split
  · rw [decoded]
    obtain ⟨kind, payload⟩ := cell
    cases kind <;> first | rfl | exact absurd rfl other
  · rfl

/-- The live image of a cell of any other kind holds no authority cell. -/
theorem decodeCell_live_other (cell : PackedCell registry) (other : cell.kind ≠ .authority) :
    decodeCell (LifecycleImage.bytes registry (.live cell)) = none :=
  decodeCell_other_kind (LifecycleImage.decode_encode registry (.live cell)) other

/-! ### A store of the old layout is refused by name

Before this layout the authority kind's payload was the whole logical store under the
`minidregg/credential-authority/v6` store frame, in one cell at the pinned identifier. That image
is not an authority cell now: its payload begins with the store codec's magic, not this cell's
frame, so it decodes to nothing and no load reads it as a head. -/

/-- The image the old layout held at the authority identifier: the live envelope of kind tag 3
over the whole store's v6 encoding. -/
def oldLayoutImage (store : Store layout) : List UInt8 :=
  imagePrefix ++ CredentialAuthorityCell.materializer.codec.encode store

/-- **An old-layout authority cell is refused**, whatever store it encodes: it holds no
authority cell (`decodeCell`), so it is neither a head nor an entry. -/
theorem old_layout_refused (store : Store layout) : decodeCell (oldLayoutImage store) = none := by
  obtain ⟨tail, encoded⟩ : ∃ tail, CredentialAuthorityCell.materializer.codec.encode store = 68 :: tail :=
    ⟨_, rfl⟩
  have framed : ∃ rest, spec.wireFrame = 109 :: rest := by
    cases frame : spec.wireFrame with
    | nil => exact absurd (congrArg List.length frame) (by decide +kernel)
    | cons first rest =>
        have head : spec.wireFrame.head? = some 109 := by decide +kernel
        rw [frame] at head
        cases head
        exact ⟨rest, rfl⟩
  obtain ⟨rest, frame⟩ := framed
  have refused : ProtectedCell.decode spec (68 :: tail) = none := by
    unfold ProtectedCell.decode
    rw [if_neg]
    rw [frame]
    intro same
    simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at same
    exact absurd same.1 (by decide)
  unfold decodeCell oldLayoutImage
  rw [encoded]
  have decoded : (LifecycleImage.codec registry).decode (imagePrefix ++ 68 :: tail) = none := by
    show LifecycleImage.rawDecode registry (68 :: 82 :: 2 :: 1 :: 68 :: 82 :: 1 :: 3 :: 68 :: tail) = none
    simp only [LifecycleImage.rawDecode, PackedCell.decode]
    show (((registry.materializer CanonicalCellRegistry.Kind.authority).codec.decode (68 :: tail)).map _).map _ = none
    rw [show (registry.materializer CanonicalCellRegistry.Kind.authority).codec.decode (68 :: tail) =
      ProtectedCell.decode spec (68 :: tail) from rfl, refused]
    rfl
  rw [decoded]
  split <;> rfl

abbrev PhysicalSnapshot := DataSnapshot ResourceBirthCodec.rootBytes

/-! ## What the cells hold -/

/-- The value the cells hold for an address: read at the address's own cell. -/
def valueAt (bytesAt : CellId → List UInt8) (address : Address layout) :
    Option (layout.Value address.1) :=
  (decodeCell (bytesAt ⟨entryCellId address⟩)).bind (cellValue address)

/-- The logical root the head cell holds. -/
def headAt (bytesAt : CellId → List UInt8) (authorityCellId : Nat) : Option Digest :=
  (decodeCell (bytesAt ⟨authorityCellId⟩)).bind cellHead

/-- **The cells realise a logical authority store**: the head sits below the authority space
and holds the store's logical root, and at every address the store's value is what the address's
own entry cell holds for it (canonical decoding of the image, the cell and the value; the cell is
read at the address's coordinate and must name the address; an absent address has no such
payload). -/
structure RealizesAuthority (bytesAt : CellId → List UInt8) (authorityCellId : Nat)
    (logical : Store layout) : Prop where
  below : authorityCellId < ProtectedCell.authorityBase
  head : headAt bytesAt authorityCellId = some (CredentialAuthorityCell.materializer.rootOf logical)
  entries : ∀ address, logical address = valueAt bytesAt address

/-- **The cells hold a logical authority store**: `RealizesAuthority` without the comparison of
the head's root. The head is a head (below the authority space), and every address reads its
value at its own entry cell. This is what a read of a state already sealed needs, and it costs no
root: the root comparison is the open's and the step's (`loadCell`, `stepCell`), made once per
state by whoever serves it. -/
structure HoldsAuthority (bytesAt : CellId → List UInt8) (authorityCellId : Nat)
    (logical : Store layout) : Prop where
  below : authorityCellId < ProtectedCell.authorityBase
  headed : (headAt bytesAt authorityCellId).isSome = true
  entries : ∀ address, logical address = valueAt bytesAt address

theorem RealizesAuthority.holds {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {logical : Store layout} (realized : RealizesAuthority bytesAt authorityCellId logical) :
    HoldsAuthority bytesAt authorityCellId logical :=
  ⟨realized.below, by rw [realized.head]; rfl, realized.entries⟩

/-- The logical store is a function of the cells: two stores held by the same bytes are equal. -/
theorem HoldsAuthority.unique {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {left right : Store layout} (first : HoldsAuthority bytesAt authorityCellId left)
    (second : HoldsAuthority bytesAt authorityCellId right) : left = right :=
  SparseMap.ext fun address => (first.entries address).trans (second.entries address).symm

/-- The logical store is a function of the cells: two stores realised by the same bytes are
equal. -/
theorem RealizesAuthority.unique {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {left right : Store layout} (first : RealizesAuthority bytesAt authorityCellId left)
    (second : RealizesAuthority bytesAt authorityCellId right) : left = right :=
  first.holds.unique second.holds

/-! ## The lowering -/

def cellWrite (physical : PhysicalSnapshot) (cellId : Nat) (cell : PhysicalCell) : DataWrite :=
  let bytes := encodeCell cell
  { cellId := ⟨cellId⟩
    expectedPre := physical.model.roots ⟨cellId⟩
    exactPost := ResourceBirthCodec.rootBytes bytes
    canonicalPostBytes := bytes }

/-- One address's write: its entry cell with the post value, guarded at the cell's root. -/
def entryWrite (physical : PhysicalSnapshot) (post : Store layout) (address : Address layout) :
    DataWrite :=
  cellWrite physical (entryCellId address) (entryCell address (post address))

/-- The head write: the post logical root, guarded at the head's root. -/
def headWrite (physical : PhysicalSnapshot) (authorityCellId : Nat) (root : Digest) : DataWrite :=
  cellWrite physical authorityCellId (headCell root)

/-- **The physical lowering of a logical authority update**: the head, then one write per touched
address. Nothing else of the store is read or written. -/
def lowerAuthority (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) : List DataWrite :=
  headWrite physical authorityCellId postRoot :: touched.map (entryWrite physical post)

theorem lowerAuthority_length (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    (lowerAuthority physical authorityCellId touched post postRoot).length = 1 + touched.length := by
  simp [lowerAuthority, Nat.add_comm]

theorem lowerAuthority_root_bound (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    ∀ write ∈ lowerAuthority physical authorityCellId touched post postRoot,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  simp only [lowerAuthority, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨address, _, rfl⟩ <;> rfl

theorem lowerAuthority_pre_exact (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    ∀ write ∈ lowerAuthority physical authorityCellId touched post postRoot,
      write.expectedPre = physical.model.roots write.cellId := by
  intro write member
  simp only [lowerAuthority, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨address, _, rfl⟩ <;> rfl

/-- Every lowered write is a live authority cell that obeys the registry's law at its id. -/
theorem lowerAuthority_decodes (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    ∀ write ∈ lowerAuthority physical authorityCellId touched post postRoot,
      ∃ cell, write.canonicalPostBytes = encodeCell cell ∧
        PhysicalLaw authorityCellId write.cellId.value cell.logical := by
  intro write member
  simp only [lowerAuthority, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨address, _, rfl⟩
  · exact ⟨_, rfl, headCell_law authorityCellId postRoot⟩
  · exact ⟨_, rfl, entryCell_law authorityCellId address (post address)⟩

/-- The cells the lowering writes: the head and each touched address's cell. -/
theorem lowerAuthority_cellIds (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    (lowerAuthority physical authorityCellId touched post postRoot).map DataWrite.cellId =
      ⟨authorityCellId⟩ :: touched.map fun address => (⟨entryCellId address⟩ : CellId) := by
  simp [lowerAuthority, headWrite, entryWrite, cellWrite, Function.comp_def]

/-- The lowered writes are at distinct cells when the touched addresses are distinct and the head
is below the authority space. -/
theorem lowerAuthority_nodup (physical : PhysicalSnapshot) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest)
    (distinct : touched.Nodup) (below : authorityCellId < ProtectedCell.authorityBase) :
    ((lowerAuthority physical authorityCellId touched post postRoot).map DataWrite.cellId).Nodup := by
  rw [lowerAuthority_cellIds, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro member
    obtain ⟨address, _, same⟩ := List.mem_map.mp member
    have ids : entryCellId address = authorityCellId := congrArg Digest.value same
    have above := entryCellId_authority address
    omega
  · exact distinct.map fun left right same => entryCellId_injective (congrArg Digest.value same)

/-- The writes of an intent outside the authority kind neither replace nor produce an authority
cell: each is over a cell that is not one and leaves a cell that is not one. -/
def Foreign (physical : PhysicalSnapshot) (other : List DataWrite) : Prop :=
  ∀ write ∈ other, decodeCell (physical.canonicalBytes write.cellId) = none ∧
    decodeCell write.canonicalPostBytes = none

/-! ### Reading an installed intent -/

theorem lookupPostBytes_some {cellId : CellId} :
    ∀ {writes : List DataWrite} {bytes}, DataSnapshot.lookupPostBytes cellId writes = some bytes →
      ∃ write ∈ writes, write.cellId = cellId ∧ write.canonicalPostBytes = bytes
  | [], _, found => by simp [DataSnapshot.lookupPostBytes] at found
  | write :: rest, bytes, found => by
      simp only [DataSnapshot.lookupPostBytes] at found
      split at found
      · rename_i same
        exact ⟨write, List.mem_cons_self, same, Option.some.inj found⟩
      · obtain ⟨other, member, same, exact⟩ := lookupPostBytes_some found
        exact ⟨other, List.mem_cons_of_mem _ member, same, exact⟩

theorem lookupPostBytes_of_mem :
    ∀ {writes : List DataWrite} {write : DataWrite}, write ∈ writes →
      (writes.map DataWrite.cellId).Nodup →
      DataSnapshot.lookupPostBytes write.cellId writes = some write.canonicalPostBytes
  | [], _, member, _ => by cases member
  | head :: rest, write, member, distinct => by
      simp only [List.map_cons, List.nodup_cons] at distinct
      simp only [DataSnapshot.lookupPostBytes]
      rcases List.mem_cons.mp member with rfl | inRest
      · rw [if_pos rfl]
      · have apart : head.cellId ≠ write.cellId := fun same =>
          distinct.1 (same ▸ List.mem_map_of_mem inRest)
        rw [if_neg apart]
        exact lookupPostBytes_of_mem inRest distinct.2

/-- **The lowering refines the logical update.** Over a physical state that realises `logical`,
an intent whose writes are the lowering of `post` (which agrees with `logical` outside `touched`)
together with writes outside the authority kind, all at distinct cells, installs a state that
realises `post`. No vacancy is asked: an address's cell is its own (`entryCellId_injective`). -/
theorem lower_realizes {physical : PhysicalSnapshot} {authorityCellId : Nat}
    {logical post : Store layout} {touched : List (Address layout)}
    (realized : HoldsAuthority physical.canonicalBytes authorityCellId logical)
    (frame : ∀ address, address ∉ touched → post address = logical address)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite)
    (writes : intent.writes = other ++ lowerAuthority physical authorityCellId touched
      post (CredentialAuthorityCell.materializer.rootOf post))
    (distinct : (intent.writes.map DataWrite.cellId).Nodup)
    (foreign : Foreign physical other) :
    RealizesAuthority (DataSnapshot.install physical intent).canonicalBytes authorityCellId post := by
  have headMember : headWrite physical authorityCellId
      (CredentialAuthorityCell.materializer.rootOf post) ∈ intent.writes := by
    rw [writes]; simp [lowerAuthority]
  have entryMember : ∀ address ∈ touched, entryWrite physical post address ∈ intent.writes := by
    intro address member
    rw [writes]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem member))
  refine ⟨realized.below, ?_, ?_⟩
  · unfold headAt
    rw [DataSnapshot.install_canonicalBytes]
    have found := lookupPostBytes_of_mem headMember distinct
    change DataSnapshot.lookupPostBytes ⟨authorityCellId⟩ intent.writes = _ at found
    rw [found]
    simp only [Option.getD_some, headWrite, cellWrite, decodeCell_encodeCell, Option.bind_some]
    exact cellHead_headCell _
  · intro address
    by_cases isTouched : address ∈ touched
    · unfold valueAt
      rw [DataSnapshot.install_canonicalBytes]
      have found := lookupPostBytes_of_mem (entryMember address isTouched) distinct
      change DataSnapshot.lookupPostBytes ⟨entryCellId address⟩ intent.writes = _ at found
      rw [found]
      simp only [Option.getD_some, entryWrite, cellWrite, decodeCell_encodeCell, Option.bind_some]
      exact (cellValue_entryCell address (post address)).symm
    · rw [frame address isTouched, realized.entries address]
      show valueAt physical.canonicalBytes address =
        (decodeCell ((DataSnapshot.install physical intent).canonicalBytes
          ⟨entryCellId address⟩)).bind (cellValue address)
      rw [DataSnapshot.install_canonicalBytes]
      cases looked : DataSnapshot.lookupPostBytes ⟨entryCellId address⟩ intent.writes with
      | none => rfl
      | some bytes =>
          obtain ⟨write, member, sameCell, exact⟩ := lookupPostBytes_some looked
          simp only [Option.getD_some]
          subst exact
          rw [writes] at member
          simp only [lowerAuthority, List.mem_append, List.mem_cons, List.mem_map] at member
          rcases member with outside | rfl | ⟨written, writtenMember, rfl⟩
          · -- a write outside the authority kind: no authority cell before or after
            obtain ⟨before, after⟩ := foreign write outside
            unfold valueAt
            rw [← sameCell, before, after]
          · -- the head write: the head is below the authority space, no address's cell
            have sameId : entryCellId address = authorityCellId :=
              (congrArg Digest.value sameCell).symm
            have above := entryCellId_authority address
            have below := realized.below
            omega
          · -- another touched address's entry: its cell is not this address's
            have sameCoordinate : entryCellId written = entryCellId address :=
              congrArg Digest.value sameCell
            exact absurd (entryCellId_injective sameCoordinate ▸ writtenMember) isTouched

/-- **Addresses outside the touched set read as before**, in the physical state itself. -/
theorem lower_frame {physical : PhysicalSnapshot} {authorityCellId : Nat}
    {logical post : Store layout} {touched : List (Address layout)}
    (realized : HoldsAuthority physical.canonicalBytes authorityCellId logical)
    (frame : ∀ address, address ∉ touched → post address = logical address)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite)
    (writes : intent.writes = other ++ lowerAuthority physical authorityCellId touched
      post (CredentialAuthorityCell.materializer.rootOf post))
    (distinct : (intent.writes.map DataWrite.cellId).Nodup)
    (foreign : Foreign physical other) (address : Address layout)
    (outside : address ∉ touched) :
    valueAt (DataSnapshot.install physical intent).canonicalBytes address =
      valueAt physical.canonicalBytes address := by
  have after := (lower_realizes realized frame intent other writes distinct foreign).entries address
  rw [← after, frame address outside, realized.entries address]

/-! ## Teeth -/

/-- Wrong head root: cells whose head holds any other root realise no such store. -/
theorem wrong_head_refused {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {logical : Store layout} {root : Digest}
    (held : headAt bytesAt authorityCellId = some root)
    (wrong : root ≠ CredentialAuthorityCell.materializer.rootOf logical) :
    ¬ RealizesAuthority bytesAt authorityCellId logical := fun realized =>
  wrong (Option.some.inj (held.symm.trans realized.head))

/-- **A store of the old layout loads nothing**: cells whose authority identifier holds the old
whole-store image realise no authority store, so every load refuses it. -/
theorem old_layout_unrealized {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    (store : Store layout) (old : bytesAt ⟨authorityCellId⟩ = oldLayoutImage store)
    (logical : Store layout) : ¬ RealizesAuthority bytesAt authorityCellId logical := by
  intro realized
  have head := realized.head
  unfold headAt at head
  rw [old, old_layout_refused] at head
  cases head

/-- False absence (and false presence, and a false value): a store that differs from what one
address's cell holds is not realised. -/
theorem false_value_refused {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {logical : Store layout} (address : Address layout)
    (wrong : logical address ≠ valueAt bytesAt address) :
    ¬ RealizesAuthority bytesAt authorityCellId logical := fun realized =>
  wrong (realized.entries address)

/-- Omitted entry write: an intent that writes nothing at the cell of an address whose value
moved does not install the post store. -/
theorem omitted_entry_refused {physical : PhysicalSnapshot} {authorityCellId : Nat}
    {logical post : Store layout}
    (realized : HoldsAuthority physical.canonicalBytes authorityCellId logical)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (address : Address layout)
    (moved : post address ≠ logical address)
    (omitted : (⟨entryCellId address⟩ : CellId) ∉ intent.writes.map DataWrite.cellId) :
    ¬ RealizesAuthority (DataSnapshot.install physical intent).canonicalBytes authorityCellId post := by
  intro after
  apply moved
  have unwritten : DataSnapshot.lookupPostBytes ⟨entryCellId address⟩ intent.writes = none := by
    cases looked : DataSnapshot.lookupPostBytes ⟨entryCellId address⟩ intent.writes with
    | none => rfl
    | some bytes =>
        obtain ⟨write, member, same, _⟩ := lookupPostBytes_some looked
        exact absurd (same ▸ List.mem_map_of_mem member) omitted
  have read := after.entries address
  unfold valueAt at read
  rw [DataSnapshot.install_canonicalBytes, unwritten] at read
  exact read.trans (realized.entries address).symm

/-- Incompatible reuse: an entry cell holds a value only for the address whose coordinate it sits
at; read at any other address's cell it holds nothing. -/
theorem entry_elsewhere_holds_nothing {bytesAt : CellId → List UInt8} {address other : Address layout}
    {cell : PhysicalCell} {value : layout.Value other.1}
    (stored : decodeCell (bytesAt ⟨entryCellId address⟩) = some cell)
    (held : cellValue other cell = some value) (lawful : ∃ authorityCellId,
      PhysicalLaw authorityCellId (entryCellId address) cell.logical) : other = address := by
  obtain ⟨authorityCellId, law⟩ := lawful
  unfold cellValue at held
  cases present : ProtectedCell.payloadAt spec cell.logical with
  | none => rw [present] at held; cases held
  | some payload =>
      rw [present] at held
      simp only [Option.bind_some, payloadValue] at held
      split at held
      · rename_i named
        exact (entryCellId_injective (law.names present named)).symm
      · cases held

/-! ## Reading authority: the head guard

A command that reads any authority address carries one read guard, on the head. The head's root
moves whenever the logical root moves, so a read of ANY entry that has since changed is refused.
Authority writes therefore stay serialised against authority readers exactly as they were under
the one-cell layout: this is no new concurrency. -/

def headReadGuard (physical : PhysicalSnapshot) (authorityCellId : Nat) : ReadGuard :=
  { cellId := ⟨authorityCellId⟩, expectedRoot := physical.model.roots ⟨authorityCellId⟩ }

/-- A head guard taken at `read` is refused at any state whose head root has moved. -/
theorem stale_authority_read_refused {read now : PhysicalSnapshot} {authorityCellId : Nat}
    (intent : DataIntent ResourceBirthCodec.rootBytes)
    (guarded : headReadGuard read authorityCellId ∈ intent.readGuards)
    (moved : now.model.roots ⟨authorityCellId⟩ ≠ read.model.roots ⟨authorityCellId⟩) :
    intent.preflight now = .error .staleReadGuard :=
  stale_read_guard_rejected now intent ⟨_, guarded, by simpa [headReadGuard] using moved⟩

/-- **A head guard that still matches pins the whole logical root.** `physicalRootBinds` is the
one cryptographic premise, at these two byte strings: the physical root (cSHAKE256) of the head's
bytes binds them. With it, the store read at `read` and the store now have the same logical root,
so no entry a command read has changed (up to the logical root's own binding of its entries). -/
theorem head_guard_pins_root {read now : PhysicalSnapshot} {authorityCellId : Nat}
    {before after : Store layout}
    (readRealized : RealizesAuthority read.canonicalBytes authorityCellId before)
    (nowRealized : RealizesAuthority now.canonicalBytes authorityCellId after)
    (matched : now.model.roots ⟨authorityCellId⟩ = (headReadGuard read authorityCellId).expectedRoot)
    (physicalRootBinds :
      ResourceBirthCodec.rootBytes (now.canonicalBytes ⟨authorityCellId⟩) =
          ResourceBirthCodec.rootBytes (read.canonicalBytes ⟨authorityCellId⟩) →
        now.canonicalBytes ⟨authorityCellId⟩ = read.canonicalBytes ⟨authorityCellId⟩) :
    CredentialAuthorityCell.materializer.rootOf after =
      CredentialAuthorityCell.materializer.rootOf before := by
  have bytes := physicalRootBinds (by rw [now.coherent, read.coherent]; exact matched)
  have nowHead := nowRealized.head
  have readHead := readRealized.head
  unfold headAt at nowHead readHead
  rw [bytes, readHead] at nowHead
  exact (Option.some.inj nowHead).symm

/-! ## Point reads: the parent plane as a parentage

A reader that holds no logical store (a read at a past height) reads an address at its own cell
(`valueAt`). The parent plane, read so, is a `Parentage`: its bound is the number of enumerable
cells, because distinct cells with a parent have distinct entry cells among them. -/

/-- The parent rows the cells hold, each read at its own entry cell. -/
def parentageAt (bytesAt : CellId → List UInt8) (cellIds : List Nat)
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = []) : Parentage where
  parentOf cell := valueAt bytesAt ⟨.parent, cell⟩
  bound := Trunc.mk ⟨cellIds.length, by
    classical
    let coordinate : Nat → Nat := fun cell => entryCellId ⟨AuthorityPlane.parent, cell⟩
    have injective : Function.Injective coordinate := fun left right same => by
      have addresses : (⟨AuthorityPlane.parent, left⟩ : Address layout) = ⟨AuthorityPlane.parent, right⟩ :=
        entryCellId_injective same
      exact eq_of_heq (Sigma.mk.inj addresses).2
    refine ⟨cellIds.toFinset.preimage coordinate injective.injOn, ?_, ?_⟩
    · exact (Finset.card_le_card_of_injOn coordinate
        (fun cell member => Finset.mem_coe.mpr (Finset.mem_preimage.mp (Finset.mem_coe.mp member)))
        injective.injOn).trans (List.toFinset_card_le cellIds)
    · intro cell recorded
      rw [Finset.mem_preimage, List.mem_toFinset]
      by_contra outside
      apply recorded
      show valueAt bytesAt ⟨AuthorityPlane.parent, cell⟩ = none
      unfold valueAt
      rw [support _ outside, decodeCell_nil]
      rfl⟩

/-- Where the cells realise a store, the parentage read at the cells is the store's. -/
theorem parentageAt_of_realizes {bytesAt : CellId → List UInt8} {authorityCellId : Nat}
    {logical : Store layout} (cellIds : List Nat)
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = [])
    (realized : RealizesAuthority bytesAt authorityCellId logical) :
    parentageAt bytesAt cellIds support = parentageOf logical :=
  Parentage.ext (funext fun cell => (realized.entries ⟨.parent, cell⟩).symm)

/-! ## Rebuilding the store from the cells

An open reads every enumerable cell once (`loadStore`); a step reads only the cells it wrote
(`stepStore`). Each cell holds at most one address's entry, at that address's coordinate
(`entryOf`), so both are exact with no search. -/

/-- Add what the cell at `cellId` holds to the store. -/
def foldEntry (bytesAt : CellId → List UInt8) (store : Store layout) (cellId : Nat) : Store layout :=
  match (decodeCell (bytesAt ⟨cellId⟩)).bind (entryOf cellId) with
  | some entry => store.set entry.1 (some entry.2)
  | none => store

/-- Remove what the cell at `cellId` holds from the store. -/
def clearEntry (bytesAt : CellId → List UInt8) (store : Store layout) (cellId : Nat) : Store layout :=
  match (decodeCell (bytesAt ⟨cellId⟩)).bind (entryOf cellId) with
  | some entry => store.set entry.1 none
  | none => store

/-- What the cell at an address's coordinate holds for it is the entry read back there. -/
theorem entry_of_valueAt {bytesAt : CellId → List UInt8} {address : Address layout}
    {value : layout.Value address.1} (held : valueAt bytesAt address = some value) :
    (decodeCell (bytesAt ⟨entryCellId address⟩)).bind (entryOf (entryCellId address)) =
      some ⟨address, value⟩ := by
  unfold valueAt at held
  cases opened : decodeCell (bytesAt ⟨entryCellId address⟩) with
  | none => rw [opened] at held; cases held
  | some cell =>
      rw [opened] at held
      exact entryOf_of_value held

/-- The entry read back at a cell is what that cell holds for the entry's address, whose
coordinate is the cell. -/
theorem valueAt_of_entry {bytesAt : CellId → List UInt8} {cellId : Nat} {address : Address layout}
    {value : layout.Value address.1}
    (found : (decodeCell (bytesAt ⟨cellId⟩)).bind (entryOf cellId) = some ⟨address, value⟩) :
    cellId = entryCellId address ∧ valueAt bytesAt address = some value := by
  cases opened : decodeCell (bytesAt ⟨cellId⟩) with
  | none => rw [opened] at found; cases found
  | some cell =>
      rw [opened] at found
      obtain ⟨placed, held⟩ := entryOf_some found
      refine ⟨placed, ?_⟩
      unfold valueAt
      rw [← placed, opened]
      exact held

theorem foldEntry_apply (bytesAt : CellId → List UInt8) (store : Store layout) (cellId : Nat)
    (address : Address layout) :
    foldEntry bytesAt store cellId address =
      if entryCellId address = cellId ∧ (valueAt bytesAt address).isSome then valueAt bytesAt address
      else store address := by
  cases found : (decodeCell (bytesAt ⟨cellId⟩)).bind (entryOf cellId) with
  | none =>
      have reduce : foldEntry bytesAt store cellId = store := by unfold foldEntry; rw [found]
      rw [reduce]
      split
      · rename_i holds
        obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp holds.2
        have entry := entry_of_valueAt held
        rw [holds.1, found] at entry
        cases entry
      · rfl
  | some entry =>
      obtain ⟨named, value⟩ := entry
      obtain ⟨placed, held⟩ := valueAt_of_entry found
      have reduce : foldEntry bytesAt store cellId = store.set named (some value) := by
        unfold foldEntry; rw [found]
      rw [reduce]
      by_cases same : address = named
      · subst same
        rw [Store.set_eq, held, if_pos ⟨placed.symm, rfl⟩]
      · rw [Store.set_ne _ _ _ _ same]
        have apart : ¬ (entryCellId address = cellId ∧ (valueAt bytesAt address).isSome) :=
          fun holds => same (entryCellId_injective (holds.1.trans placed))
        rw [if_neg apart]

theorem clearEntry_apply (bytesAt : CellId → List UInt8) (store : Store layout) (cellId : Nat)
    (address : Address layout) :
    clearEntry bytesAt store cellId address =
      if entryCellId address = cellId ∧ (valueAt bytesAt address).isSome then none
      else store address := by
  cases found : (decodeCell (bytesAt ⟨cellId⟩)).bind (entryOf cellId) with
  | none =>
      have reduce : clearEntry bytesAt store cellId = store := by unfold clearEntry; rw [found]
      rw [reduce]
      split
      · rename_i holds
        obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp holds.2
        have entry := entry_of_valueAt held
        rw [holds.1, found] at entry
        cases entry
      · rfl
  | some entry =>
      obtain ⟨named, value⟩ := entry
      obtain ⟨placed, held⟩ := valueAt_of_entry found
      have reduce : clearEntry bytesAt store cellId = store.set named none := by
        unfold clearEntry; rw [found]
      rw [reduce]
      by_cases same : address = named
      · subst same
        rw [Store.set_eq, if_pos ⟨placed.symm, by rw [held]; rfl⟩]
      · rw [Store.set_ne _ _ _ _ same]
        have apart : ¬ (entryCellId address = cellId ∧ (valueAt bytesAt address).isSome) :=
          fun holds => same (entryCellId_injective (holds.1.trans placed))
        rw [if_neg apart]

/-- The store the enumerable cells hold: each cell of the authority space read once. A cell
below the authority space is no entry's (`entryCellId_authority`) and its bytes are not read. -/
def loadStore (bytesAt : CellId → List UInt8) (cellIds : List Nat) : Store layout :=
  (cellIds.filter fun cellId => ProtectedCell.authorityBase ≤ cellId).foldl (foldEntry bytesAt) 0

theorem foldEntries_apply (bytesAt : CellId → List UInt8) :
    ∀ (cellIds : List Nat) (store : Store layout) (address : Address layout),
      cellIds.foldl (foldEntry bytesAt) store address =
        if entryCellId address ∈ cellIds ∧ (valueAt bytesAt address).isSome then valueAt bytesAt address
        else store address
  | [], store, address => by simp
  | cellId :: rest, store, address => by
      rw [List.foldl_cons, foldEntries_apply bytesAt rest, foldEntry_apply]
      by_cases held : (valueAt bytesAt address).isSome
      · by_cases inRest : entryCellId address ∈ rest
        · simp [held, inRest]
        · by_cases here : entryCellId address = cellId
          · simp [held, here]
          · simp [held, inRest, here]
      · simp [held]

/-- **The open is exact**: where every cell outside the enumeration is never used, the loaded
store's value at every address is what that address's cell holds. -/
theorem loadStore_exact (bytesAt : CellId → List UInt8) (cellIds : List Nat)
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = []) (address : Address layout) :
    loadStore bytesAt cellIds address = valueAt bytesAt address := by
  unfold loadStore
  rw [foldEntries_apply]
  split
  · rfl
  · rename_i absent
    show (none : Option _) = _
    by_cases listed : entryCellId address ∈ cellIds
    · have filtered : entryCellId address ∈
          cellIds.filter fun cellId => ProtectedCell.authorityBase ≤ cellId :=
        List.mem_filter.mpr ⟨listed, by simpa using entryCellId_authority address⟩
      have notSome : ¬ (valueAt bytesAt address).isSome := fun held => absent ⟨filtered, held⟩
      cases value : valueAt bytesAt address with
      | none => rfl
      | some _ => rw [value] at notSome; exact absurd rfl notSome
    · unfold valueAt
      rw [support _ listed, decodeCell_nil]
      rfl

/-- One written cell of a step: what it held before leaves the store, what it holds now enters. -/
def stepEntry (before after : CellId → List UInt8) (store : Store layout) (cellId : Nat) :
    Store layout :=
  foldEntry after (clearEntry before store cellId) cellId

/-- The store after a step, from the store before it and the cells the step wrote. -/
def stepStore (before after : CellId → List UInt8) (store : Store layout) (written : List Nat) :
    Store layout :=
  written.foldl (stepEntry before after) store

theorem stepEntry_apply (before after : CellId → List UInt8) (store : Store layout) (cellId : Nat)
    (address : Address layout)
    (held : store address = valueAt before address ∨ store address = valueAt after address) :
    stepEntry before after store cellId address =
      if entryCellId address = cellId then valueAt after address else store address := by
  unfold stepEntry
  rw [foldEntry_apply, clearEntry_apply]
  by_cases here : entryCellId address = cellId
  · rw [if_pos here]
    by_cases now : (valueAt after address).isSome
    · rw [if_pos ⟨here, now⟩]
    · rw [if_neg (fun both => now both.2)]
      have absent : valueAt after address = none := by
        cases value : valueAt after address with
        | none => rfl
        | some _ => rw [value] at now; exact absurd rfl now
      rw [absent]
      split
      · rfl
      · rename_i notBefore
        rcases held with old | new
        · rw [old]
          cases value : valueAt before address with
          | none => rfl
          | some _ => exact absurd ⟨here, by rw [value]; rfl⟩ notBefore
        · rw [new, absent]
  · rw [if_neg (fun both => here both.1), if_neg (fun both => here both.1), if_neg here]

theorem stepStore_apply (before after : CellId → List UInt8) :
    ∀ (written : List Nat) (store : Store layout),
      (∀ address, store address = valueAt before address ∨ store address = valueAt after address) →
      ∀ address, stepStore before after store written address =
        if entryCellId address ∈ written then valueAt after address else store address
  | [], store, _, address => by simp [stepStore]
  | cellId :: rest, store, held, address => by
      have next : ∀ other, stepEntry before after store cellId other = valueAt before other ∨
          stepEntry before after store cellId other = valueAt after other := by
        intro other
        rw [stepEntry_apply before after store cellId other (held other)]
        split
        · exact Or.inr rfl
        · exact held other
      have rest' := stepStore_apply before after rest (stepEntry before after store cellId) next address
      unfold stepStore at rest' ⊢
      rw [List.foldl_cons, rest', stepEntry_apply before after store cellId address (held address)]
      by_cases inRest : entryCellId address ∈ rest
      · simp [inRest]
      · by_cases here : entryCellId address = cellId
        · simp [here]
        · simp [inRest, here]

/-- **The step is exact**: from a store that is what the cells held before, where every cell
outside `written` kept its bytes, the stepped store is what the cells hold now. -/
theorem stepStore_exact (before after : CellId → List UInt8) (store : Store layout)
    (written : List Nat) (held : ∀ address, store address = valueAt before address)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩) (address : Address layout) :
    stepStore before after store written address = valueAt after address := by
  rw [stepStore_apply before after written store (fun other => Or.inl (held other))]
  split
  · rfl
  · rename_i unwritten
    rw [held address]
    unfold valueAt
    rw [kept _ unwritten]

/-- **The addresses a step can have moved**: for each written cell, the address its entry named
before and the address its entry names now. Every other address reads as it did
(`valueAt_unchanged`), so a check that follows the store (policy sourcing) revisits only these. -/
def changedAddresses (before after : CellId → List UInt8) (written : List Nat) :
    List (Address layout) :=
  written.flatMap fun cellId =>
    (((decodeCell (before ⟨cellId⟩)).bind (entryOf cellId)).toList.map Sigma.fst) ++
      (((decodeCell (after ⟨cellId⟩)).bind (entryOf cellId)).toList.map Sigma.fst)

/-- **The frame of a step, in the cells themselves.** An address the step's written cells neither
named before nor name now reads the same after the step, whatever the head says: it is never
inferred from the head being unwritten. -/
theorem valueAt_unchanged {before after : CellId → List UInt8} {written : List Nat}
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    {address : Address layout} (outside : address ∉ changedAddresses before after written) :
    valueAt after address = valueAt before address := by
  by_cases wrote : entryCellId address ∈ written
  · have absent : ∀ (bytesAt : CellId → List UInt8),
        (∀ value, (decodeCell (bytesAt ⟨entryCellId address⟩)).bind (entryOf (entryCellId address)) =
          some ⟨address, value⟩ → address ∈ changedAddresses before after written) →
        valueAt bytesAt address = none := by
      intro bytesAt named
      cases held : valueAt bytesAt address with
      | none => rfl
      | some value => exact absurd (named value (entry_of_valueAt held)) outside
    rw [absent after, absent before]
    · intro value found
      refine List.mem_flatMap.mpr ⟨entryCellId address, wrote, List.mem_append_left _ ?_⟩
      rw [found]
      simp
    · intro value found
      refine List.mem_flatMap.mpr ⟨entryCellId address, wrote, List.mem_append_right _ ?_⟩
      rw [found]
      simp
  · unfold valueAt
    rw [kept _ wrote]

/-- The frame between two held stores one step apart. -/
theorem HoldsAuthority.framed {before after : CellId → List UInt8} {authorityCellId : Nat}
    {old new : Store layout} {written : List Nat}
    (held : HoldsAuthority before authorityCellId old)
    (now : HoldsAuthority after authorityCellId new)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    (address : Address layout) (outside : address ∉ changedAddresses before after written) :
    new address = old address := by
  rw [now.entries, held.entries, valueAt_unchanged kept outside]

/-- The operations of one written cell of a step: free what it held, allocate what it holds. -/
def entryOps (before after : CellId → List UInt8) (cellId : Nat) : Patch layout :=
  (match (decodeCell (before ⟨cellId⟩)).bind (entryOf cellId) with
    | some entry => [Op.free entry.1.1 entry.1.2 entry.2]
    | none => []) ++
  (match (decodeCell (after ⟨cellId⟩)).bind (entryOf cellId) with
    | some entry => [Op.allocate entry.1.1 entry.1.2 entry.2]
    | none => [])

/-- The step as a patch, so a held cell's kept structure follows it by one `set` per entry. -/
def stepPatch (before after : CellId → List UInt8) (written : List Nat) : Patch layout :=
  written.flatMap (entryOps before after)

theorem run_entryOps (before after : CellId → List UInt8) (store : Store layout) (cellId : Nat) :
    Patch.run store (entryOps before after cellId) = stepEntry before after store cellId := by
  unfold entryOps stepEntry foldEntry clearEntry
  cases (decodeCell (before ⟨cellId⟩)).bind (entryOf cellId) <;>
    cases (decodeCell (after ⟨cellId⟩)).bind (entryOf cellId) <;> rfl

theorem run_stepPatch (before after : CellId → List UInt8) :
    ∀ (written : List Nat) (store : Store layout),
      Patch.run store (stepPatch before after written) = stepStore before after store written
  | [], _ => rfl
  | cellId :: rest, store => by
      unfold stepPatch stepStore
      rw [List.flatMap_cons, Patch.run_append, run_entryOps, List.foldl_cons]
      exact run_stepPatch before after rest _

/-! ## Loading the cell

Two pairs. `loadCell` and `stepCell` SEAL: they compare the head's root with the root of the store
the cells hold, the open once over the whole store and the step along the written cells only.
The serving Host runs them, once per served state. `readCell` and `followCell` READ a state
already sealed: the same store, no root computed. A receiver handed a durable image the Host
validated reads through these. -/

/-- **An open, sealed**: the store every enumerable cell holds, materialized, when the head is
below the authority space and holds that store's logical root. -/
def loadCell (bytesAt : CellId → List UInt8) (authorityCellId : Nat) (cellIds : List Nat) :
    Option CredentialAuthorityCell.Cell :=
  let cell := materialize CredentialAuthorityCell.materializer (loadStore bytesAt cellIds)
  if authorityCellId < ProtectedCell.authorityBase ∧ headAt bytesAt authorityCellId = some cell.root then
    some cell
  else none

theorem loadCell_realizes {bytesAt : CellId → List UInt8} {authorityCellId : Nat} {cellIds : List Nat}
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = [])
    {cell : CredentialAuthorityCell.Cell} (loaded : loadCell bytesAt authorityCellId cellIds = some cell) :
    RealizesAuthority bytesAt authorityCellId cell.logical := by
  unfold loadCell at loaded
  dsimp only at loaded
  split at loaded
  · rename_i sealed
    cases loaded
    exact ⟨sealed.1, sealed.2, fun address => loadStore_exact bytesAt cellIds support address⟩
  · cases loaded

/-- The open loads every realised store, and only it. -/
theorem loadCell_of_realizes {bytesAt : CellId → List UInt8} {authorityCellId : Nat} {cellIds : List Nat}
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = [])
    {logical : Store layout} (realized : RealizesAuthority bytesAt authorityCellId logical) :
    ∃ cell, loadCell bytesAt authorityCellId cellIds = some cell ∧ cell.logical = logical := by
  have same : loadStore bytesAt cellIds = logical := SparseMap.ext fun address =>
    (loadStore_exact bytesAt cellIds support address).trans (realized.entries address).symm
  refine ⟨materialize CredentialAuthorityCell.materializer (loadStore bytesAt cellIds), ?_, same⟩
  unfold loadCell
  rw [if_pos ⟨realized.below, by rw [same]; exact realized.head⟩]

/-- **An open, read**: the store every enumerable cell holds, materialized, when the head is a
head below the authority space. No root is computed. -/
def readCell (bytesAt : CellId → List UInt8) (authorityCellId : Nat) (cellIds : List Nat) :
    Option CredentialAuthorityCell.Cell :=
  if authorityCellId < ProtectedCell.authorityBase ∧ (headAt bytesAt authorityCellId).isSome = true then
    some (materialize CredentialAuthorityCell.materializer (loadStore bytesAt cellIds))
  else none

theorem readCell_holds {bytesAt : CellId → List UInt8} {authorityCellId : Nat} {cellIds : List Nat}
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = [])
    {cell : CredentialAuthorityCell.Cell} (read : readCell bytesAt authorityCellId cellIds = some cell) :
    HoldsAuthority bytesAt authorityCellId cell.logical := by
  unfold readCell at read
  split at read
  · rename_i headed
    cases read
    exact ⟨headed.1, headed.2, fun address => loadStore_exact bytesAt cellIds support address⟩
  · cases read

/-- The read loads every held store, and only it. -/
theorem readCell_of_holds {bytesAt : CellId → List UInt8} {authorityCellId : Nat} {cellIds : List Nat}
    (support : ∀ cellId, cellId ∉ cellIds → bytesAt ⟨cellId⟩ = [])
    {logical : Store layout} (held : HoldsAuthority bytesAt authorityCellId logical) :
    ∃ cell, readCell bytesAt authorityCellId cellIds = some cell ∧ cell.logical = logical := by
  have same : loadStore bytesAt cellIds = logical := SparseMap.ext fun address =>
    (loadStore_exact bytesAt cellIds support address).trans (held.entries address).symm
  refine ⟨materialize CredentialAuthorityCell.materializer (loadStore bytesAt cellIds), ?_, same⟩
  unfold readCell
  rw [if_pos ⟨held.below, held.headed⟩]

/-- **A step, sealed**: the held cell followed along the cells the step wrote, when the head now
holds its logical root. One decode and one path of the kept structure per written entry. -/
def stepCell (before after : CellId → List UInt8) (authorityCellId : Nat)
    (prior : CredentialAuthorityCell.Cell) (written : List Nat) : Option CredentialAuthorityCell.Cell :=
  let cell := prior.follow (stepPatch before after written)
  if headAt after authorityCellId = some cell.root then some cell else none

theorem stepCell_logical {before after : CellId → List UInt8} {authorityCellId : Nat}
    {prior cell : CredentialAuthorityCell.Cell} {written : List Nat}
    (stepped : stepCell before after authorityCellId prior written = some cell) :
    cell.logical = stepStore before after prior.logical written := by
  unfold stepCell at stepped
  dsimp only at stepped
  split at stepped
  · cases stepped
    exact run_stepPatch before after written prior.logical
  · cases stepped

theorem stepCell_realizes {before after : CellId → List UInt8} {authorityCellId : Nat}
    {prior cell : CredentialAuthorityCell.Cell} {written : List Nat}
    (held : HoldsAuthority before authorityCellId prior.logical)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    (stepped : stepCell before after authorityCellId prior written = some cell) :
    RealizesAuthority after authorityCellId cell.logical := by
  have logical := stepCell_logical stepped
  unfold stepCell at stepped
  dsimp only at stepped
  split at stepped
  · rename_i head
    cases stepped
    refine ⟨held.below, head, fun address => ?_⟩
    rw [logical]
    exact stepStore_exact before after prior.logical written held.entries kept address
  · cases stepped

/-- The step loads every store the cells now realise, and only it. -/
theorem stepCell_of_realizes {before after : CellId → List UInt8} {authorityCellId : Nat}
    {prior : CredentialAuthorityCell.Cell} {written : List Nat}
    (held : HoldsAuthority before authorityCellId prior.logical)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    {logical : Store layout} (realized : RealizesAuthority after authorityCellId logical) :
    ∃ cell, stepCell before after authorityCellId prior written = some cell ∧ cell.logical = logical := by
  have same : Patch.run prior.logical (stepPatch before after written) = logical := by
    rw [run_stepPatch]
    exact SparseMap.ext fun address =>
      (stepStore_exact before after prior.logical written held.entries kept address).trans
        (realized.entries address).symm
  refine ⟨prior.follow (stepPatch before after written), ?_, same⟩
  unfold stepCell
  rw [if_pos (by
    show headAt after authorityCellId = some (CredentialAuthorityCell.materializer.rootOf
      (Patch.run prior.logical (stepPatch before after written)))
    rw [same]; exact realized.head)]

/-- **A step, read**: the held cell followed along the cells the step wrote, when the head is
still a head. No root is computed. -/
def followCell (before after : CellId → List UInt8) (authorityCellId : Nat)
    (prior : CredentialAuthorityCell.Cell) (written : List Nat) : Option CredentialAuthorityCell.Cell :=
  if (headAt after authorityCellId).isSome = true then
    some (prior.follow (stepPatch before after written))
  else none

theorem followCell_holds {before after : CellId → List UInt8} {authorityCellId : Nat}
    {prior cell : CredentialAuthorityCell.Cell} {written : List Nat}
    (held : HoldsAuthority before authorityCellId prior.logical)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    (followed : followCell before after authorityCellId prior written = some cell) :
    HoldsAuthority after authorityCellId cell.logical := by
  unfold followCell at followed
  split at followed
  · rename_i headed
    cases followed
    refine ⟨held.below, headed, fun address => ?_⟩
    show Patch.run prior.logical (stepPatch before after written) address = _
    rw [run_stepPatch]
    exact stepStore_exact before after prior.logical written held.entries kept address
  · cases followed

/-- The followed cell is every store the cells now hold, and only it. -/
theorem followCell_of_holds {before after : CellId → List UInt8} {authorityCellId : Nat}
    {prior : CredentialAuthorityCell.Cell} {written : List Nat}
    (held : HoldsAuthority before authorityCellId prior.logical)
    (kept : ∀ cellId, cellId ∉ written → after ⟨cellId⟩ = before ⟨cellId⟩)
    {logical : Store layout} (now : HoldsAuthority after authorityCellId logical) :
    ∃ cell, followCell before after authorityCellId prior written = some cell ∧ cell.logical = logical := by
  refine ⟨prior.follow (stepPatch before after written), ?_, ?_⟩
  · unfold followCell
    rw [if_pos now.headed]
  · show Patch.run prior.logical (stepPatch before after written) = logical
    rw [run_stepPatch]
    exact SparseMap.ext fun address =>
      (stepStore_exact before after prior.logical written held.entries kept address).trans
        (now.entries address).symm

/-! ## An update: the post cell, what it touched, and the frame -/

/-- A logical authority update of `pre`: its post cell, the addresses it touched, and the proof
that every other address kept its value. The lowering takes an `Update`, so a writer cannot omit
a touched address's write. -/
structure Update (pre : CredentialAuthorityCell.Cell) where
  post : CredentialAuthorityCell.Cell
  touched : List (Address layout)
  frame : ∀ address, address ∉ touched → post.logical address = pre.logical address

/-- The addresses a patch writes, each once. -/
def patchTouched (patch : Patch layout) : List (Address layout) :=
  (patch.filterMap Op.writeAddress?).dedup

/-- The update of a validated patch: its applied cell and its write footprint. -/
def Update.ofValidated {pre : CredentialAuthorityCell.Cell} {root : Digest} {patch : Patch layout}
    (validated : ValidatedPatch CredentialAuthorityCell.materializer pre root patch) : Update pre where
  post := validated.apply
  touched := patchTouched patch
  frame address outside := Patch.run_frame pre.logical patch address (by
    simpa [Patch.writeFootprint, patchTouched] using outside)

@[simp] theorem Update.ofValidated_post {pre : CredentialAuthorityCell.Cell} {root : Digest}
    {patch : Patch layout}
    (validated : ValidatedPatch CredentialAuthorityCell.materializer pre root patch) :
    (Update.ofValidated validated).post = validated.apply := rfl

/-- The update of a validated patch whose applied cell is already held (`cell`, built once and
shared by every reader). -/
def Update.ofValidatedAt {pre : CredentialAuthorityCell.Cell} {root : Digest} {patch : Patch layout}
    (validated : ValidatedPatch CredentialAuthorityCell.materializer pre root patch)
    (cell : CredentialAuthorityCell.Cell) (exact : cell = validated.apply) : Update pre where
  post := cell
  touched := patchTouched patch
  frame := exact ▸ (Update.ofValidated validated).frame

/-- The lowered writes of an update. -/
def Update.writes {pre : CredentialAuthorityCell.Cell} (update : Update pre)
    (physical : PhysicalSnapshot) (authorityCellId : Nat) : List DataWrite :=
  lowerAuthority physical authorityCellId update.touched update.post.logical update.post.root

/-- **An update's lowering installs its post store.** -/
theorem Update.realizes {pre : CredentialAuthorityCell.Cell} (update : Update pre)
    {physical : PhysicalSnapshot} {authorityCellId : Nat}
    (realized : HoldsAuthority physical.canonicalBytes authorityCellId pre.logical)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite)
    (writes : intent.writes = other ++ update.writes physical authorityCellId)
    (distinct : (intent.writes.map DataWrite.cellId).Nodup)
    (foreign : Foreign physical other) :
    RealizesAuthority (DataSnapshot.install physical intent).canonicalBytes authorityCellId
      update.post.logical :=
  lower_realizes realized update.frame intent other writes distinct foreign

/-! ## The birth's authority writes -/

/-- The addresses a birth's authority batch touches: three per initial policy, two per grant, one
per parent row. -/
def birthTouched {registry : TypeRegistry Digest} (descriptor : Descriptor registry) :
    List (Address layout) :=
  (ResourceBirthAuthority.entries descriptor).map Sigma.fst

theorem birthTouched_length {registry : TypeRegistry Digest} (descriptor : Descriptor registry) :
    (birthTouched descriptor).length =
      3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
        descriptor.parentRows.length := by
  have policies : ∀ policies : List InitialPolicy,
      (policies.flatMap ResourceBirthAuthority.policyEntries).length = 3 * policies.length := by
    intro policies
    induction policies with
    | nil => rfl
    | cons policy rest step =>
        simp only [List.flatMap_cons, List.length_append, step, List.length_cons]
        simp [ResourceBirthAuthority.policyEntries]
        omega
  simp only [birthTouched, ResourceBirthAuthority.entries, List.length_map, List.length_append,
    policies]
  omega

/-- The update of a birth's authority batch: the batch applied to the pre cell, touching the
batch's own addresses. -/
def Update.ofBirth {registry : TypeRegistry Digest} (pre : CredentialAuthorityCell.Cell)
    (descriptor : Descriptor registry) (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor) :
    Update pre where
  post := ResourceBirthAuthority.post pre descriptor evidence
  touched := birthTouched descriptor
  frame address outside := by
    rw [ResourceBirthAuthority.post_logical]
    exact CredentialAuthorityEffects.setAll_frame _ _ _ outside

/-- The lowering of a birth's authority batch at its post cell. -/
def lowerBirth {registry : TypeRegistry Digest} (physical : PhysicalSnapshot)
    (authorityCellId : Nat) (descriptor : Descriptor registry) (post : CredentialAuthorityCell.Cell) :
    List DataWrite :=
  lowerAuthority physical authorityCellId (birthTouched descriptor) post.logical post.root

theorem Update.ofBirth_writes {registry : TypeRegistry Digest} (pre : CredentialAuthorityCell.Cell)
    (descriptor : Descriptor registry) (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor)
    (physical : PhysicalSnapshot) (authorityCellId : Nat) :
    (Update.ofBirth pre descriptor evidence).writes physical authorityCellId =
      lowerBirth physical authorityCellId descriptor (ResourceBirthAuthority.post pre descriptor evidence) :=
  rfl

/-- The length of a natural's wire encoding. -/
def natLen (value : Nat) : Nat := (StreamCodec.nat.encode value).length

/-- A bound on one authority cell's own bytes from its key and body lengths: frame, version,
presence octet, role octet, the two length-prefixed byte strings. -/
def cellBound (keyLength bodyLength : Nat) : Nat :=
  spec.wireFrame.length + natLen spec.wireVersion + 2 + natLen keyLength + keyLength +
    natLen bodyLength + bodyLength

/-- A bound on one encoded write whose cell identifier is at most `idBound`: the identifier, the
two roots (cSHAKE256 digests, below `2^256`), and the length-prefixed image (eight octets of
lifecycle and kind envelope, then the cell). -/
def writeBound (idBound cellLength : Nat) : Nat :=
  natLen idBound + 2 * natLen (2 ^ 256) + natLen (8 + cellLength) + (8 + cellLength)

structure AuthorityBirthBudget where
  maxWrites : Nat
  maxEncodedBytes : Nat

/-- **The birth's authority budget**: a closed computation from the pinned head identifier and
the member-authored descriptor's initial policies, grants and parent rows: their count, each
entry's own cell identifier (`entryCellId`, a function of its plane and key bytes) and its encoded
key and value lengths. It reads no snapshot, no height and no store support. -/
def authorityBirthBudget {registry : TypeRegistry Digest} (authorityCellId : Nat)
    (descriptor : Descriptor registry) : AuthorityBirthBudget where
  maxWrites := 1 + 3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
    descriptor.parentRows.length
  maxEncodedBytes :=
    natLen (1 + 3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
        descriptor.parentRows.length) +
      writeBound authorityCellId (cellBound 0 (natLen (2 ^ 256))) +
      ((ResourceBirthAuthority.entries descriptor).map fun entry =>
        writeBound (entryCellId entry.1)
          (cellBound (keyBytes entry.1).length ((valueStream entry.1.1).encode entry.2).length)).sum

/-- The budget reads only the member-authored part: the kernel's auxiliary allocations do not
enter it. -/
theorem authorityBirthBudget_userPart {registry : TypeRegistry Digest} (authorityCellId : Nat)
    (descriptor : Descriptor registry) :
    authorityBirthBudget authorityCellId { descriptor with auxiliaryCreates := [] } =
      authorityBirthBudget authorityCellId descriptor := rfl

/-- An entry's cell identifier is bounded by its key's length: below `2^257 + 256^(length + 2)`. -/
theorem entryCellId_lt (address : Address layout) :
    entryCellId address < ProtectedCell.authorityBase + 256 ^ ((keyBytes address).length + 2) := by
  have bound := natOfBytes_lt (CredentialAuthorityCell.planeTag address.1 :: keyBytes address)
  exact Nat.add_lt_add_left bound _

/-- The encoded bytes of a write list, as the record carries it. -/
def encodedLength (writes : List DataWrite) : Nat :=
  ((StreamCodec.list DurableReceiverCodec.writeStream).encode writes).length

/-- The count clause. -/
def BirthAuthorityWriteCount : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot)
    (authorityCellId : Nat) (descriptor : Descriptor registry) (post : CredentialAuthorityCell.Cell),
    (lowerBirth physical authorityCellId descriptor post).length ≤
      (authorityBirthBudget authorityCellId descriptor).maxWrites

/-- The byte clause, at the birth's own post cell (the batch applied to the pre cell under its
authority admission): the bound is computed from the descriptor and the codecs, never from the
lowered writes. It counts each write's framing (identifier, both roots, the length prefix), the
image envelope, and the head write as constants. -/
def BirthAuthorityWriteBytes : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot)
    (authorityCellId : Nat) (pre : CredentialAuthorityCell.Cell) (descriptor : Descriptor registry)
    (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor),
    encodedLength (lowerBirth physical authorityCellId descriptor
        (ResourceBirthAuthority.post pre descriptor evidence)) ≤
      (authorityBirthBudget authorityCellId descriptor).maxEncodedBytes

/-- The realisation and frame clauses, over the birth's authority admission (`BatchEvidence`, the
authority part of every admitted birth: `PreparedGrantBatch.mode`). -/
def BirthAuthorityRealized : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot)
    (authorityCellId : Nat) (pre : CredentialAuthorityCell.Cell) (descriptor : Descriptor registry)
    (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite),
    HoldsAuthority physical.canonicalBytes authorityCellId pre.logical →
    intent.writes = other ++ lowerBirth physical authorityCellId descriptor
      (ResourceBirthAuthority.post pre descriptor evidence) →
    (intent.writes.map DataWrite.cellId).Nodup →
    Foreign physical other →
    RealizesAuthority (DataSnapshot.install physical intent).canonicalBytes authorityCellId
        (ResourceBirthAuthority.post pre descriptor evidence).logical ∧
      ∀ address, address ∉ birthTouched descriptor →
        valueAt (DataSnapshot.install physical intent).canonicalBytes address =
          valueAt physical.canonicalBytes address

/-- **The keystone**: the authority writes of an admitted birth, as the lowering produces them, are
bounded in count and encoded bytes by the budget of the member-authored descriptor, with no term in
the store's key count; they realise the patched logical store; addresses outside the batch are
unchanged. It bounds the authority writes only: the complete record is NOT bounded by the
descriptor while the Book and the factory cell are written whole by every birth. -/
def BirthAuthorityWritesBounded : Prop :=
  BirthAuthorityWriteCount ∧ BirthAuthorityWriteBytes ∧ BirthAuthorityRealized

theorem birthAuthorityWriteCount : BirthAuthorityWriteCount := by
  intro registry physical authorityCellId descriptor post
  simp only [lowerBirth, lowerAuthority_length, birthTouched_length, authorityBirthBudget]
  omega

theorem birthAuthorityRealized : BirthAuthorityRealized := by
  intro registry physical authorityCellId pre descriptor evidence intent other realized
    writes distinct foreign
  have frame := (Update.ofBirth pre descriptor evidence).frame
  have writes' : intent.writes = other ++ lowerAuthority physical authorityCellId
      (birthTouched descriptor) (ResourceBirthAuthority.post pre descriptor evidence).logical
      (CredentialAuthorityCell.materializer.rootOf
        (ResourceBirthAuthority.post pre descriptor evidence).logical) := writes
  exact ⟨lower_realizes realized frame intent other writes' distinct foreign,
    fun address outside =>
      lower_frame realized frame intent other writes' distinct foreign address outside⟩

/-! ### The byte clause -/

theorem natLen_mono {small large : Nat} (le : small ≤ large) : natLen small ≤ natLen large := by
  simp only [natLen, StreamCodec.nat, StreamCodec.encodeNat, StreamCodec.natDigits,
    List.length_append, List.length_map, List.length_singleton]
  exact Nat.add_le_add_right (Nat.le_length_digits_le 255 small large le) 1

theorem rootBytes_lt (bytes) : (ResourceBirthCodec.rootBytes bytes).value < 2 ^ 256 :=
  Sp800185Cshake256.hash_digest_lt_two_pow_256 _ _

/-- The logical root is a cSHAKE256 digest. -/
theorem logicalRoot_lt (store : Store layout) :
    (CredentialAuthorityCell.materializer.rootOf store).value < 2 ^ 256 := by
  rw [show CredentialAuthorityCell.materializer.rootOf store = _ from
    PrivateCellRoot.materializer_rootOf CredentialAuthorityCell.wire (PrivateCellRoot.untagged _) store]
  exact Sp800185Cshake256.hash_digest_lt_two_pow_256 _ _

theorem write_length (write : DataWrite) :
    (DurableReceiverCodec.writeStream.encode write).length =
      natLen write.cellId.value + natLen write.expectedPre.value + natLen write.exactPost.value +
        natLen write.canonicalPostBytes.length + write.canonicalPostBytes.length := by
  simp only [DurableReceiverCodec.writeStream, StreamCodec.xmap, StreamCodec.product, digestStream,
    bytesStream, natLen, List.length_append]
  omega

theorem role_length (role : spec.Role) : (spec.roleStream.encode role).length = 1 := by
  cases role <;> rfl

/-- The length of a physical cell's own bytes. -/
theorem cell_length (payload : Option (ProtectedCell.Payload spec)) :
    (materialize (ProtectedCell.materializer spec) (ProtectedCell.stateOfOption spec payload)).bytes.length =
      spec.wireFrame.length + natLen spec.wireVersion +
        match payload with
        | none => 1
        | some held => 2 + natLen held.key.length + held.key.length + natLen held.body.length +
            held.body.length := by
  have encoded : (materialize (ProtectedCell.materializer spec)
      (ProtectedCell.stateOfOption spec payload)).bytes =
      spec.wireFrame ++ (ProtectedCell.wirePayloadStream spec).encode (spec.wireVersion, payload) := by
    show ProtectedCell.encode spec (ProtectedCell.stateOfOption spec payload) = _
    rw [ProtectedCell.encode, ProtectedCell.payloadAt_stateOfOption]
  rw [encoded]
  cases payload with
  | none =>
      simp only [ProtectedCell.wirePayloadStream, StreamCodec.product, StreamCodec.option,
        List.length_append, natLen, List.length_singleton]
      omega
  | some held =>
      have role := role_length held.role
      simp only [ProtectedCell.wirePayloadStream, ProtectedCell.payloadStream, StreamCodec.product,
        StreamCodec.option, StreamCodec.xmap, bytesStream, List.length_append, natLen,
        List.length_cons, role]
      omega

theorem cellWrite_length_le (physical : PhysicalSnapshot) (cellId idBound cellLength : Nat)
    (cell : PhysicalCell) (idLe : cellId ≤ idBound) (cellLe : cell.bytes.length ≤ cellLength) :
    (DurableReceiverCodec.writeStream.encode (cellWrite physical cellId cell)).length ≤
      writeBound idBound cellLength := by
  rw [write_length]
  have pre : (physical.model.roots ⟨cellId⟩).value ≤ 2 ^ 256 := by
    rw [← physical.coherent]; exact (rootBytes_lt _).le
  have post := (rootBytes_lt (encodeCell cell)).le
  have length : (encodeCell cell).length ≤ 8 + cellLength := by
    rw [encodeCell_length]; exact Nat.add_le_add_left cellLe _
  have idLength := natLen_mono idLe
  have preLength := natLen_mono pre
  have postLength := natLen_mono post
  have lengthLength := natLen_mono length
  simp only [cellWrite, writeBound]
  omega

theorem encodedLength_eq (writes : List DataWrite) :
    encodedLength writes = natLen writes.length +
      (writes.map fun write => (DurableReceiverCodec.writeStream.encode write).length).sum := by
  simp only [encodedLength, StreamCodec.list, List.length_append, natLen]
  congr 1
  induction writes with
  | nil => rfl
  | cons write rest step => simp [StreamCodec.encodeMany, step]

theorem birthAuthorityWriteBytes : BirthAuthorityWriteBytes := by
  intro registry physical authorityCellId pre descriptor evidence
  have headLe : (DurableReceiverCodec.writeStream.encode (headWrite physical authorityCellId
      (ResourceBirthAuthority.post pre descriptor evidence).root)).length ≤
      writeBound authorityCellId (cellBound 0 (natLen (2 ^ 256))) := by
    apply cellWrite_length_le physical _ _ _ _ (Nat.le_refl _)
    have rootLe := natLen_mono (logicalRoot_lt
      (ResourceBirthAuthority.post pre descriptor evidence).logical).le
    have body : (digestStream.encode (ResourceBirthAuthority.post pre descriptor evidence).root).length =
        natLen (CredentialAuthorityCell.materializer.rootOf
          (ResourceBirthAuthority.post pre descriptor evidence).logical).value := rfl
    have bodyLe : (digestStream.encode (ResourceBirthAuthority.post pre descriptor evidence).root).length ≤
        natLen (2 ^ 256) := by rw [body]; exact rootLe
    have bodyLength := natLen_mono bodyLe
    rw [headCell, cell_length]
    simp only [headPayload, List.length_nil, cellBound]
    omega
  have entryLe : ∀ entry ∈ ResourceBirthAuthority.entries descriptor,
      (DurableReceiverCodec.writeStream.encode (entryWrite physical
        (ResourceBirthAuthority.post pre descriptor evidence).logical entry.1)).length ≤
      writeBound (entryCellId entry.1)
        (cellBound (keyBytes entry.1).length ((valueStream entry.1.1).encode entry.2).length) := by
    intro entry member
    have value : (ResourceBirthAuthority.post pre descriptor evidence).logical entry.1 =
        some entry.2 := by
      rw [ResourceBirthAuthority.post_logical]
      exact CredentialAuthorityEffects.setAll_member _ _ evidence.slotsDistinct entry member
    apply cellWrite_length_le physical _ _ _ _ (Nat.le_refl _)
    rw [value, entryCell, Option.map_some, cell_length]
    simp only [entryPayload, cellBound]
    omega
  rw [encodedLength_eq]
  simp only [lowerBirth, lowerAuthority, birthTouched, List.map_cons, List.map_map, List.sum_cons,
    List.length_cons, List.length_map, authorityBirthBudget]
  have count : (ResourceBirthAuthority.entries descriptor).length =
      3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
        descriptor.parentRows.length := by
    have := birthTouched_length descriptor
    simpa [birthTouched] using this
  have sums := List.sum_le_sum (l := ResourceBirthAuthority.entries descriptor) entryLe
  have countLe : natLen ((ResourceBirthAuthority.entries descriptor).length + 1) ≤
      natLen (1 + 3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
        descriptor.parentRows.length) := natLen_mono (by omega)
  have total := Nat.add_le_add countLe (Nat.add_le_add headLe sums)
  simpa [Function.comp_def, Nat.add_assoc] using total

theorem birthAuthorityWritesBounded : BirthAuthorityWritesBounded :=
  ⟨birthAuthorityWriteCount, birthAuthorityWriteBytes, birthAuthorityRealized⟩

#assert_axioms old_layout_refused
#assert_axioms old_layout_unrealized
#assert_axioms lower_realizes
#assert_axioms lower_frame
#assert_axioms RealizesAuthority.unique
#assert_axioms omitted_entry_refused
#assert_axioms wrong_head_refused
#assert_axioms false_value_refused
#assert_axioms entry_elsewhere_holds_nothing
#assert_axioms stale_authority_read_refused
#assert_axioms head_guard_pins_root
#assert_axioms parentageAt_of_realizes
#assert_axioms loadStore_exact
#assert_axioms stepStore_exact
#assert_axioms valueAt_unchanged
#assert_axioms HoldsAuthority.framed
#assert_axioms Update.realizes
#assert_axioms loadCell_realizes
#assert_axioms loadCell_of_realizes
#assert_axioms stepCell_realizes
#assert_axioms stepCell_of_realizes
#assert_axioms readCell_holds
#assert_axioms readCell_of_holds
#assert_axioms followCell_holds
#assert_axioms followCell_of_holds
#assert_axioms lowerAuthority_nodup
#assert_axioms birthAuthorityWritesBounded

end Minidregg.Compiler.CredentialAuthorityLayout
