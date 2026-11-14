/-
# Compiler.CredentialAuthorityLayout -- the authority store's physical layout

The authority domain keeps one logical `Store` over `CredentialAuthorityState.layout` and its
logical root (`CredentialAuthorityCell.materializer`, a kept trie). This module is the physical
image of that store: one HEAD cell at the deployment's pinned `authorityCellId`, holding the
logical root, and one ENTRY cell per store address, at a protected coordinate
(`Kernel.ProtectedCell.coordinate`, at or above `2^256`, so no birth can install one), holding
that address's value with the address in its payload.

| cell  | identifier                                              | payload                         |
|-------|---------------------------------------------------------|---------------------------------|
| HEAD  | `deployment.authorityCellId`                            | `head`, `[]`, the logical root  |
| ENTRY | `2^256 + cSHAKE256(ADDRESS/v1, domain ‖ plane ‖ key)`   | `entry plane`, key, value bytes |

An address that is logically absent has no payload in its entry cell (or a cell never used): a
logical `free` empties the cell, it does not retire the identifier, so a later lawful allocation
at the same address writes the same cell again.

`lowerAuthority` is the lowering of a logical update: the HEAD write and one write per touched
address. `RealizesAuthority` is the relation between a physical snapshot and the logical store it
holds. `lower_realizes` is the refinement: installing the lowered writes over a snapshot that
realises the pre-store realises the post-store, whatever else the intent writes outside the
authority role. The birth instance and its budget are stated at the end
(`BirthAuthorityWritesBounded`).

The lifecycle envelope of a live cell (`Envelope`) is a parameter here: its instance is the
registry's `.authority` role once that role's payload is this module's cell.
-/
module

public import Kernel.ProtectedCell
public import Kernel.DurableDataIntent
public import Compiler.CredentialAuthorityCell
public import Compiler.ResourceBirthCodec
public import Compiler.DurableReceiverCodec
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
open Minidregg.Compiler.CredentialAuthorityCell (planeTag planeOfTag planeOfTag_tag planeOfTag_some
  keyStream valueStream)
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CellRegistry (TypeRegistry)

set_option autoImplicit false

/-! ## The role of an authority cell and its codec -/

/-- The two roles of the authority kind: the head, and the entry of one plane. -/
inductive Role where
  | head
  | entry (plane : AuthorityPlane)
  deriving DecidableEq

/-- The head's role octet; no plane tag is 255 (`planeTag_ne_headTag`). -/
def headTag : UInt8 := 255

theorem planeTag_ne_headTag (plane : AuthorityPlane) : planeTag plane ≠ headTag := by
  cases plane with
  | capability kind => cases kind <;> decide
  | _ => decide

def roleStream : StreamCodec Role where
  encode
    | .head => [headTag]
    | .entry plane => [planeTag plane]
  decodePrefix
    | tag :: suffix =>
        if tag = headTag then some (Role.head, suffix)
        else (planeOfTag tag).map fun plane => (Role.entry plane, suffix)
    | [] => none
  decodePrefix_encode := by
    intro role suffix
    cases role with
    | head => simp
    | entry plane => simp [planeTag_ne_headTag plane, planeOfTag_tag]
  encode_decodePrefix := by
    intro bytes role suffix decoded
    rcases bytes with _ | ⟨tag, bytes⟩
    · cases decoded
    · change (if tag = headTag then some (Role.head, bytes)
        else (planeOfTag tag).map fun plane => (Role.entry plane, bytes)) = some (role, suffix)
        at decoded
      by_cases isHead : tag = headTag
      · rw [if_pos isHead] at decoded
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        simp [isHead]
      · rw [if_neg isHead] at decoded
        cases found : planeOfTag tag with
        | none => simp [found] at decoded
        | some plane =>
            simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at decoded
            obtain ⟨rfl, rfl⟩ := decoded
            simp [planeOfTag_some found]

/-- The authority role as a protected family (`Kernel.ProtectedCell`): entry coordinates are
`2^256 + cSHAKE256(idCustomization, domain ‖ role ‖ key)`. -/
def spec : ProtectedCell.Spec where
  Role := Role
  roleStream := roleStream
  idCustomization := "DREGG.AUTHORITY.ADDRESS/v1".toUTF8.toList
  rootCustomization := "DREGG.AUTHORITY.CELL.ROOT/v1".toUTF8.toList
  wireFrame := "minidregg/credential-authority-cell/v7".toUTF8.toList
  wireVersion := 7

instance roleDecEq : DecidableEq spec.Role := inferInstanceAs (DecidableEq Role)

/-- One physical authority cell: the head or one entry. -/
abbrev PhysicalCell := Materialized (ProtectedCell.materializer spec)

/-! ## Entry and head cells -/

/-- The canonical bytes of an address's key: the preimage of its coordinate. -/
def keyBytes (address : Address layout) :=
  (keyStream address.1).encode address.2

/-- The cell an address lives at, in one deployment domain. -/
def entryCellId (domain : Digest) (address : Address layout) : Nat :=
  ProtectedCell.coordinate spec domain (.entry address.1) (keyBytes address)

theorem entryCellId_reserved (domain : Digest) (address : Address layout) :
    ProtectedCell.reservedBase ≤ entryCellId domain address :=
  ProtectedCell.coordinate_reserved spec domain _ _

def entryPayload (address : Address layout) (value : layout.Value address.1) :
    ProtectedCell.Payload spec :=
  ⟨.entry address.1, keyBytes address, (valueStream address.1).encode value⟩

/-- The entry cell of an address: its value, or no payload when the address is absent. -/
def entryCell (address : Address layout) (value : Option (layout.Value address.1)) : PhysicalCell :=
  materialize (ProtectedCell.materializer spec)
    (ProtectedCell.stateOfOption spec (value.map (entryPayload address)))

def headPayload (root : Digest) : ProtectedCell.Payload spec :=
  ⟨.head, [], digestStream.encode root⟩

/-- The head cell: the logical root of the authority store. -/
def headCell (root : Digest) : PhysicalCell :=
  materialize (ProtectedCell.materializer spec)
    (ProtectedCell.stateOfOption spec (some (headPayload root)))

/-- A payload names an address when it is that address's entry: same plane, same key bytes. -/
def Names (payload : ProtectedCell.Payload spec) (address : Address layout) : Prop :=
  payload.role = .entry address.1 ∧ payload.key = keyBytes address

instance namesDecidable (payload : ProtectedCell.Payload spec) (address : Address layout) :
    Decidable (Names payload address) :=
  @instDecidableAnd _ _ (roleDecEq payload.role (.entry address.1))
    (inferInstanceAs (Decidable (payload.key = keyBytes address)))

/-- A payload is the head's: the head role, no key. -/
def IsHead (payload : ProtectedCell.Payload spec) : Prop :=
  payload.role = .head ∧ payload.key = []

instance isHeadDecidable (payload : ProtectedCell.Payload spec) : Decidable (IsHead payload) :=
  @instDecidableAnd _ _ (roleDecEq payload.role .head)
    (inferInstanceAs (Decidable (payload.key = [])))

/-- A payload names at most one address: the key codec is injective. -/
theorem Names.unique {payload : ProtectedCell.Payload spec} {left right : Address layout}
    (first : Names payload left) (second : Names payload right) : left = right := by
  obtain ⟨leftPlane, leftKey⟩ := left
  obtain ⟨rightPlane, rightKey⟩ := right
  have planes : leftPlane = rightPlane := Role.entry.inj (first.1.symm.trans second.1)
  subst planes
  have keys : (keyStream leftPlane).encode leftKey = (keyStream leftPlane).encode rightKey :=
    first.2.symm.trans second.2
  have decodedLeft := (keyStream leftPlane).decodePrefix_encode leftKey []
  have decodedRight := (keyStream leftPlane).decodePrefix_encode rightKey []
  rw [keys, decodedRight] at decodedLeft
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at decodedLeft
  rw [decodedLeft]

theorem entryPayload_names (address : Address layout) (value : layout.Value address.1) :
    Names (entryPayload address value) address := ⟨rfl, rfl⟩

/-- The value a payload holds for an address: its decoded body when it names the address. -/
def payloadValue (address : Address layout) (payload : ProtectedCell.Payload spec) :
    Option (layout.Value address.1) :=
  if Names payload address then (valueStream address.1).toLawful.decode payload.body else none

/-- The value a physical cell holds for an address. -/
def cellValue (address : Address layout) (cell : PhysicalCell) : Option (layout.Value address.1) :=
  (ProtectedCell.payloadAt spec cell.logical).bind (payloadValue address)

/-- The logical root a physical cell holds as the head. -/
def cellHead (cell : PhysicalCell) : Option Digest :=
  (ProtectedCell.payloadAt spec cell.logical).bind fun payload =>
    if IsHead payload then digestStream.toLawful.decode payload.body else none

theorem cellValue_entryCell (address : Address layout) (value : Option (layout.Value address.1)) :
    cellValue address (entryCell address value) = value := by
  cases value with
  | none => simp [cellValue, entryCell, materialize]
  | some value =>
      have decoded := (valueStream address.1).toLawful.decode_encode value
      simp only [cellValue, entryCell, materialize, Option.map_some,
        ProtectedCell.payloadAt_stateOfOption, Option.bind_some, payloadValue,
        if_pos (entryPayload_names address value)]
      exact decoded

/-- An entry cell holds nothing for any other address. -/
theorem cellValue_entryCell_other {address other : Address layout} (different : other ≠ address)
    (value : Option (layout.Value address.1)) :
    cellValue other (entryCell address value) = none := by
  cases value with
  | none => simp [cellValue, entryCell, materialize]
  | some value =>
      have unnamed : ¬ Names (entryPayload address value) other := fun named =>
        different (Names.unique named (entryPayload_names address value))
      simp only [cellValue, entryCell, materialize, Option.map_some,
        ProtectedCell.payloadAt_stateOfOption, Option.bind_some, payloadValue, if_neg unnamed]

theorem cellHead_headCell (root : Digest) : cellHead (headCell root) = some root := by
  have decoded := digestStream.toLawful.decode_encode root
  have isHead : IsHead (headPayload root) := ⟨rfl, rfl⟩
  simp only [cellHead, headCell, materialize, ProtectedCell.payloadAt_stateOfOption,
    Option.bind_some, if_pos isHead]
  exact decoded

/-- A cell that holds a head holds no entry. -/
theorem cellValue_of_cellHead {cell : PhysicalCell} {root : Digest}
    (head : cellHead cell = some root) (address : Address layout) : cellValue address cell = none := by
  unfold cellHead at head
  unfold cellValue
  cases present : ProtectedCell.payloadAt spec cell.logical with
  | none => rfl
  | some payload =>
      rw [present] at head
      simp only [Option.bind_some] at head ⊢
      by_cases isHead : IsHead payload
      · have unnamed : ¬ Names payload address := fun named => by
          have roles := isHead.1.symm.trans named.1
          cases roles
        simp only [payloadValue, if_neg unnamed]
      · rw [if_neg isHead] at head
        cases head

/-! ## The lifecycle envelope of a live authority cell -/

/-- How a live authority cell is spelled as a durable cell's canonical bytes, and read back.
`overhead` bounds what the envelope adds to the cell's own bytes. The instance is the registry's
lifecycle image of the `.authority` role. -/
structure Envelope where
  encode : PhysicalCell → List UInt8
  decode : List UInt8 → Option PhysicalCell
  decode_encode : ∀ cell, decode (encode cell) = some cell
  encode_decode : ∀ {bytes cell}, decode bytes = some cell → encode cell = bytes
  /-- A never-used identifier (`[]`) holds no authority cell. -/
  decode_nil : decode [] = none
  overhead : Nat
  encode_length : ∀ cell, (encode cell).length ≤ overhead + cell.bytes.length

abbrev PhysicalSnapshot := DataSnapshot ResourceBirthCodec.rootBytes

variable (envelope : Envelope)

/-- The value the physical state holds for an address: read at the address's own cell. -/
def valueAt (physical : PhysicalSnapshot) (domain : Digest) (address : Address layout) :
    Option (layout.Value address.1) :=
  (envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩)).bind (cellValue address)

/-- The logical root the physical state's head cell holds. -/
def headAt (physical : PhysicalSnapshot) (authorityCellId : Nat) : Option Digest :=
  (envelope.decode (physical.canonicalBytes ⟨authorityCellId⟩)).bind cellHead

/-- **A physical state realises a logical authority store**: its head cell holds the store's
logical root, and at every address the store's value is what the address's own entry cell holds
for it (canonical decoding of the envelope, the cell and the value; the cell is read at the
address's coordinate and must name the address; an absent address has no such payload). -/
structure RealizesAuthority (physical : PhysicalSnapshot) (domain : Digest) (authorityCellId : Nat)
    (logical : Store layout) : Prop where
  head : headAt envelope physical authorityCellId =
    some (CredentialAuthorityCell.materializer.rootOf logical)
  entries : ∀ address, logical address = valueAt envelope physical domain address

/-- The logical store is a function of the physical state: two stores realised by one state are
equal. -/
theorem RealizesAuthority.unique {physical : PhysicalSnapshot} {domain : Digest}
    {authorityCellId : Nat} {left right : Store layout}
    (first : RealizesAuthority envelope physical domain authorityCellId left)
    (second : RealizesAuthority envelope physical domain authorityCellId right) : left = right :=
  SparseMap.ext fun address => (first.entries address).trans (second.entries address).symm

/-! ## The lowering -/

def cellWrite (physical : PhysicalSnapshot) (cellId : Nat) (cell : PhysicalCell) : DataWrite :=
  let bytes := envelope.encode cell
  { cellId := ⟨cellId⟩
    expectedPre := physical.model.roots ⟨cellId⟩
    exactPost := ResourceBirthCodec.rootBytes bytes
    canonicalPostBytes := bytes }

/-- One address's write: its entry cell with the post value, guarded at the cell's root. -/
def entryWrite (physical : PhysicalSnapshot) (domain : Digest) (post : Store layout)
    (address : Address layout) : DataWrite :=
  cellWrite envelope physical (entryCellId domain address) (entryCell address (post address))

/-- The head write: the post logical root, guarded at the head's root. -/
def headWrite (physical : PhysicalSnapshot) (authorityCellId : Nat) (root : Digest) : DataWrite :=
  cellWrite envelope physical authorityCellId (headCell root)

/-- **The physical lowering of a logical authority update**: the head, then one write per touched
address. Nothing else of the store is read or written. -/
def lowerAuthority (physical : PhysicalSnapshot) (domain : Digest) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) : List DataWrite :=
  headWrite envelope physical authorityCellId postRoot ::
    touched.map (entryWrite envelope physical domain post)

theorem lowerAuthority_length (physical : PhysicalSnapshot) (domain : Digest) (authorityCellId : Nat)
    (touched : List (Address layout)) (post : Store layout) (postRoot : Digest) :
    (lowerAuthority envelope physical domain authorityCellId touched post postRoot).length =
      1 + touched.length := by
  simp [lowerAuthority, Nat.add_comm]

theorem lowerAuthority_root_bound (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (touched : List (Address layout)) (post : Store layout)
    (postRoot : Digest) :
    ∀ write ∈ lowerAuthority envelope physical domain authorityCellId touched post postRoot,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  simp only [lowerAuthority, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨address, _, rfl⟩ <;> rfl

theorem lowerAuthority_pre_exact (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (touched : List (Address layout)) (post : Store layout)
    (postRoot : Digest) :
    ∀ write ∈ lowerAuthority envelope physical domain authorityCellId touched post postRoot,
      write.expectedPre = physical.model.roots write.cellId := by
  intro write member
  simp only [lowerAuthority, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨address, _, rfl⟩ <;> rfl

/-- **An address's cell is vacant for it**: never used, or an authority cell whose payload, if any,
names this address. A cell that holds another address (a coordinate collision), a retired image or
another role is not vacant, and an update that touches the address is refused. -/
def Vacant (physical : PhysicalSnapshot) (domain : Digest) (address : Address layout) : Prop :=
  match envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩) with
  | some cell => ∀ payload, ProtectedCell.payloadAt spec cell.logical = some payload →
      Names payload address
  | none => physical.canonicalBytes ⟨entryCellId domain address⟩ = []

/-- A vacant cell holds nothing for any other address. -/
theorem Vacant.other_absent {physical : PhysicalSnapshot} {domain : Digest}
    {address other : Address layout} (vacant : Vacant envelope physical domain address)
    (sameCell : entryCellId domain other = entryCellId domain address) (different : other ≠ address) :
    valueAt envelope physical domain other = none := by
  unfold Vacant at vacant
  unfold valueAt
  rw [sameCell]
  cases opened : envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩) with
  | none => rfl
  | some cell =>
      rw [opened] at vacant
      simp only [Option.bind_some, cellValue]
      cases present : ProtectedCell.payloadAt spec cell.logical with
      | none => rfl
      | some payload =>
          have unnamed : ¬ Names payload other := fun named =>
            different (Names.unique named (vacant payload present))
          simp only [Option.bind_some, payloadValue, if_neg unnamed]

/-- The writes of an intent outside the authority role neither replace nor produce an authority
cell: each is over a cell that is not one and leaves a cell that is not one. -/
def Foreign (physical : PhysicalSnapshot) (other : List DataWrite) : Prop :=
  ∀ write ∈ other, envelope.decode (physical.canonicalBytes write.cellId) = none ∧
    envelope.decode write.canonicalPostBytes = none

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
an intent whose writes are the lowering of `post` (which agrees with `logical` outside `touched`,
each touched address's cell vacant for it) together with writes outside the authority role,
all at distinct cells, installs a state that realises `post`. -/
theorem lower_realizes {physical : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {logical post : Store layout} {touched : List (Address layout)}
    (realized : RealizesAuthority envelope physical domain authorityCellId logical)
    (vacant : ∀ address ∈ touched, Vacant envelope physical domain address)
    (frame : ∀ address, address ∉ touched → post address = logical address)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite)
    (writes : intent.writes = other ++ lowerAuthority envelope physical domain authorityCellId touched
      post (CredentialAuthorityCell.materializer.rootOf post))
    (distinct : (intent.writes.map DataWrite.cellId).Nodup)
    (foreign : Foreign envelope physical other) :
    RealizesAuthority envelope (DataSnapshot.install physical intent) domain authorityCellId post := by
  have headMember : headWrite envelope physical authorityCellId
      (CredentialAuthorityCell.materializer.rootOf post) ∈ intent.writes := by
    rw [writes]; simp [lowerAuthority]
  have entryMember : ∀ address ∈ touched,
      entryWrite envelope physical domain post address ∈ intent.writes := by
    intro address member
    rw [writes]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem member))
  refine ⟨?_, ?_⟩
  · unfold headAt
    rw [DataSnapshot.install_canonicalBytes]
    have found := lookupPostBytes_of_mem headMember distinct
    change DataSnapshot.lookupPostBytes ⟨authorityCellId⟩ intent.writes = _ at found
    rw [found]
    simp only [Option.getD_some, headWrite, cellWrite, envelope.decode_encode, Option.bind_some]
    exact cellHead_headCell _
  · intro address
    by_cases isTouched : address ∈ touched
    · unfold valueAt
      rw [DataSnapshot.install_canonicalBytes]
      have found := lookupPostBytes_of_mem (entryMember address isTouched) distinct
      change DataSnapshot.lookupPostBytes ⟨entryCellId domain address⟩ intent.writes = _ at found
      rw [found]
      simp only [Option.getD_some, entryWrite, cellWrite, envelope.decode_encode, Option.bind_some]
      exact (cellValue_entryCell address (post address)).symm
    · rw [frame address isTouched, realized.entries address]
      show valueAt envelope physical domain address =
        (envelope.decode ((DataSnapshot.install physical intent).canonicalBytes
          ⟨entryCellId domain address⟩)).bind (cellValue address)
      rw [DataSnapshot.install_canonicalBytes]
      cases looked : DataSnapshot.lookupPostBytes ⟨entryCellId domain address⟩ intent.writes with
      | none => rfl
      | some bytes =>
          obtain ⟨write, member, sameCell, exact⟩ := lookupPostBytes_some looked
          simp only [Option.getD_some]
          subst exact
          rw [writes] at member
          simp only [lowerAuthority, List.mem_append, List.mem_cons, List.mem_map] at member
          rcases member with outside | rfl | ⟨written, writtenMember, rfl⟩
          · -- a write outside the authority role: no authority cell before or after
            obtain ⟨before, after⟩ := foreign write outside
            unfold valueAt
            rw [← sameCell, before, after]
          · -- the head write: the cell was the head and is the head
            have preHead := realized.head
            unfold headAt at preHead
            have sameId : (⟨entryCellId domain address⟩ : CellId) = ⟨authorityCellId⟩ := sameCell.symm
            unfold valueAt
            rw [sameId]
            cases opened : envelope.decode (physical.canonicalBytes ⟨authorityCellId⟩) with
            | none => rw [opened] at preHead; cases preHead
            | some cell =>
                rw [opened] at preHead
                simp only [Option.bind_some] at preHead
                simp only [headWrite, cellWrite, envelope.decode_encode, Option.bind_some]
                rw [cellValue_of_cellHead preHead address,
                  cellValue_of_cellHead (cellHead_headCell _) address]
          · -- another touched address's entry at the same coordinate: vacant before, its own after
            have different : address ≠ written := fun same => isTouched (same ▸ writtenMember)
            have sameCoordinate : entryCellId domain address = entryCellId domain written := by
              have := congrArg Digest.value sameCell
              exact this.symm
            rw [(vacant written writtenMember).other_absent envelope sameCoordinate different]
            simp only [entryWrite, cellWrite, envelope.decode_encode, Option.bind_some]
            exact (cellValue_entryCell_other different _).symm

/-- **Addresses outside the touched set read as before**, in the physical state itself. -/
theorem lower_frame {physical : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {logical post : Store layout} {touched : List (Address layout)}
    (realized : RealizesAuthority envelope physical domain authorityCellId logical)
    (vacant : ∀ address ∈ touched, Vacant envelope physical domain address)
    (frame : ∀ address, address ∉ touched → post address = logical address)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite)
    (writes : intent.writes = other ++ lowerAuthority envelope physical domain authorityCellId touched
      post (CredentialAuthorityCell.materializer.rootOf post))
    (distinct : (intent.writes.map DataWrite.cellId).Nodup)
    (foreign : Foreign envelope physical other) (address : Address layout)
    (outside : address ∉ touched) :
    valueAt envelope (DataSnapshot.install physical intent) domain address =
      valueAt envelope physical domain address := by
  have after := (lower_realizes envelope realized vacant frame intent other writes distinct
    foreign).entries address
  rw [← after, frame address outside, realized.entries address]

/-! ## Teeth -/

/-- Wrong head root: a state whose head holds any other root realises no such store. -/
theorem wrong_head_refused {physical : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {logical : Store layout} {root : Digest}
    (held : headAt envelope physical authorityCellId = some root)
    (wrong : root ≠ CredentialAuthorityCell.materializer.rootOf logical) :
    ¬ RealizesAuthority envelope physical domain authorityCellId logical := fun realized =>
  wrong (Option.some.inj (held.symm.trans realized.head))

/-- False absence (and false presence, and a false value): a store that differs from what one
address's cell holds is not realised. -/
theorem false_value_refused {physical : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {logical : Store layout} (address : Address layout)
    (wrong : logical address ≠ valueAt envelope physical domain address) :
    ¬ RealizesAuthority envelope physical domain authorityCellId logical := fun realized =>
  wrong (realized.entries address)

/-- Omitted entry write: an intent that writes the head and every touched entry except one whose
value moved, and nothing at that entry's cell, does not install the post store. -/
theorem omitted_entry_refused {physical : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {logical post : Store layout}
    (realized : RealizesAuthority envelope physical domain authorityCellId logical)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (address : Address layout)
    (moved : post address ≠ logical address)
    (omitted : (⟨entryCellId domain address⟩ : CellId) ∉ intent.writes.map DataWrite.cellId) :
    ¬ RealizesAuthority envelope (DataSnapshot.install physical intent) domain authorityCellId post := by
  intro after
  apply moved
  have unwritten : DataSnapshot.lookupPostBytes ⟨entryCellId domain address⟩ intent.writes = none := by
    cases looked : DataSnapshot.lookupPostBytes ⟨entryCellId domain address⟩ intent.writes with
    | none => rfl
    | some bytes =>
        obtain ⟨write, member, same, _⟩ := lookupPostBytes_some looked
        exact absurd (same ▸ List.mem_map_of_mem member) omitted
  have read := after.entries address
  unfold valueAt at read
  rw [DataSnapshot.install_canonicalBytes, unwritten] at read
  exact read.trans (realized.entries address).symm

/-- Incompatible reuse: a cell that holds another address's entry is not vacant. -/
theorem occupied_not_vacant {physical : PhysicalSnapshot} {domain : Digest}
    {address occupant : Address layout} (different : occupant ≠ address)
    (sameCell : entryCellId domain occupant = entryCellId domain address)
    (present : (valueAt envelope physical domain occupant).isSome) :
    ¬ Vacant envelope physical domain address := fun vacant => by
  rw [vacant.other_absent envelope sameCell different] at present
  cases present

/-- Incompatible reuse: a cell whose bytes are neither never-used nor an authority cell (a retired
image, another role) is not vacant. -/
theorem foreign_not_vacant {physical : PhysicalSnapshot} {domain : Digest} {address : Address layout}
    (used : physical.canonicalBytes ⟨entryCellId domain address⟩ ≠ [])
    (foreign : envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩) = none) :
    ¬ Vacant envelope physical domain address := fun vacant => by
  unfold Vacant at vacant
  rw [foreign] at vacant
  exact used vacant

/-! ## The named refusal of an occupied coordinate

Two addresses whose coordinates are equal (a cSHAKE256 collision on the `ADDRESS/v1` preimages:
the one cryptographic assumption of the placement) cannot both be present. The second to be
written is refused by name; nothing is overwritten. That is a loss of liveness for that one
address and no loss of safety. -/

inductive LowerReject where
  /-- A touched address's cell holds another address's entry, a retired image or another role. -/
  | coordinateOccupied (cellId : Nat)
  deriving DecidableEq, Repr

def vacantCheck (physical : PhysicalSnapshot) (domain : Digest) (address : Address layout) : Bool :=
  match envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩) with
  | some cell =>
      match ProtectedCell.payloadAt spec cell.logical with
      | some payload => decide (Names payload address)
      | none => true
  | none => (physical.canonicalBytes ⟨entryCellId domain address⟩).isEmpty

theorem vacantCheck_iff (physical : PhysicalSnapshot) (domain : Digest) (address : Address layout) :
    vacantCheck envelope physical domain address = true ↔ Vacant envelope physical domain address := by
  unfold vacantCheck Vacant
  cases envelope.decode (physical.canonicalBytes ⟨entryCellId domain address⟩) with
  | none => simp
  | some cell =>
      cases present : ProtectedCell.payloadAt spec cell.logical with
      | none => simp [present]
      | some payload => simp [present]

/-- The lowering's admission: every touched address's cell is vacant for it, or the first that is
not is named. -/
def checkVacant (physical : PhysicalSnapshot) (domain : Digest) (touched : List (Address layout)) :
    Except LowerReject Unit :=
  match touched.find? fun address => !vacantCheck envelope physical domain address with
  | some address => .error (.coordinateOccupied (entryCellId domain address))
  | none => .ok ()

theorem checkVacant_ok_iff (physical : PhysicalSnapshot) (domain : Digest)
    (touched : List (Address layout)) :
    checkVacant envelope physical domain touched = .ok () ↔
      ∀ address ∈ touched, Vacant envelope physical domain address := by
  unfold checkVacant
  cases found : touched.find? fun address => !vacantCheck envelope physical domain address with
  | none =>
      simp only [true_iff]
      intro address member
      have passed := List.find?_eq_none.mp found address member
      exact (vacantCheck_iff envelope physical domain address).mp (by simpa using passed)
  | some address =>
      simp only [reduceCtorEq, false_iff]
      intro all
      have failed := List.find?_some found
      have vacant := (vacantCheck_iff envelope physical domain address).mpr
        (all address (List.mem_of_find?_eq_some found))
      simp [vacant] at failed

/-- A colliding address is refused by name: with another address present at the same coordinate,
the check does not pass. -/
theorem collision_refused {physical : PhysicalSnapshot} {domain : Digest}
    {address occupant : Address layout} {touched : List (Address layout)}
    (member : address ∈ touched) (different : occupant ≠ address)
    (sameCell : entryCellId domain occupant = entryCellId domain address)
    (present : (valueAt envelope physical domain occupant).isSome) :
    checkVacant envelope physical domain touched ≠ .ok () := fun passed =>
  occupied_not_vacant envelope different sameCell present
    ((checkVacant_ok_iff envelope physical domain touched).mp passed address member)

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
theorem head_guard_pins_root {read now : PhysicalSnapshot} {domain : Digest} {authorityCellId : Nat}
    {before after : Store layout}
    (readRealized : RealizesAuthority envelope read domain authorityCellId before)
    (nowRealized : RealizesAuthority envelope now domain authorityCellId after)
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

/-- The lowering of a birth's authority batch at its post cell. -/
def lowerBirth {registry : TypeRegistry Digest} (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (descriptor : Descriptor registry) (post : CredentialAuthorityCell.Cell) :
    List DataWrite :=
  lowerAuthority envelope physical domain authorityCellId (birthTouched descriptor) post.logical
    post.root

/-- The length of a natural's wire encoding. -/
def natLen (value : Nat) : Nat := (StreamCodec.nat.encode value).length

/-- A bound on one authority cell's own bytes from its key and body lengths: frame, version,
presence octet, role octet, the two length-prefixed byte strings. -/
def cellBound (keyLength bodyLength : Nat) : Nat :=
  spec.wireFrame.length + natLen spec.wireVersion + 2 + natLen keyLength + keyLength +
    natLen bodyLength + bodyLength

/-- A bound on one encoded write whose cell identifier is below `idBound`: the identifier, the two
roots (cSHAKE256 digests, below `2^256`), and the length-prefixed enveloped cell. -/
def writeBound (idBound cellLength : Nat) : Nat :=
  natLen idBound + 2 * natLen (2 ^ 256) + natLen (envelope.overhead + cellLength) +
    (envelope.overhead + cellLength)

structure AuthorityBirthBudget where
  maxWrites : Nat
  maxEncodedBytes : Nat

/-- **The birth's authority budget**: a closed computation from the envelope's constant, the
pinned head identifier and the member-authored descriptor's initial policies, grants and parent
rows (their count and their encoded key and value lengths). It reads no snapshot, no height and no
store support. -/
def authorityBirthBudget {registry : TypeRegistry Digest} (authorityCellId : Nat)
    (descriptor : Descriptor registry) : AuthorityBirthBudget where
  maxWrites := 1 + 3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
    descriptor.parentRows.length
  maxEncodedBytes :=
    natLen (1 + 3 * descriptor.initialPolicies.length + 2 * descriptor.grants.length +
        descriptor.parentRows.length) +
      writeBound envelope (authorityCellId + 1) (cellBound 0 (natLen (2 ^ 256))) +
      ((ResourceBirthAuthority.entries descriptor).map fun entry =>
        writeBound envelope (2 ^ 257)
          (cellBound (keyBytes entry.1).length ((valueStream entry.1.1).encode entry.2).length)).sum

/-- The budget reads only the member-authored part: the kernel's auxiliary allocations do not
enter it. -/
theorem authorityBirthBudget_userPart {registry : TypeRegistry Digest} (authorityCellId : Nat)
    (descriptor : Descriptor registry) :
    authorityBirthBudget envelope authorityCellId { descriptor with auxiliaryCreates := [] } =
      authorityBirthBudget envelope authorityCellId descriptor := rfl

/-- The encoded bytes of a write list, as the record carries it. -/
def encodedLength (writes : List DataWrite) : Nat :=
  ((StreamCodec.list DurableReceiverCodec.writeStream).encode writes).length

/-- The count clause. -/
def BirthAuthorityWriteCount : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (descriptor : Descriptor registry) (post : CredentialAuthorityCell.Cell),
    (lowerBirth envelope physical domain authorityCellId descriptor post).length ≤
      (authorityBirthBudget envelope authorityCellId descriptor).maxWrites

/-- The byte clause, at the birth's own post cell (the batch applied to the pre cell under its
authority admission): the bound is computed from the descriptor and the codecs, never from the
lowered writes. It counts each write's framing (identifier, both roots, the length prefix), the
envelope, and the head write as constants. -/
def BirthAuthorityWriteBytes : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (pre : CredentialAuthorityCell.Cell) (descriptor : Descriptor registry)
    (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor),
    encodedLength (lowerBirth envelope physical domain authorityCellId descriptor
        (ResourceBirthAuthority.post pre descriptor evidence)) ≤
      (authorityBirthBudget envelope authorityCellId descriptor).maxEncodedBytes

/-- The realisation and frame clauses, over the birth's authority admission (`BatchEvidence`, the
authority part of every admitted birth: `PreparedGrantBatch.mode`). -/
def BirthAuthorityRealized : Prop :=
  ∀ {registry : TypeRegistry Digest} (physical : PhysicalSnapshot) (domain : Digest)
    (authorityCellId : Nat) (pre : CredentialAuthorityCell.Cell) (descriptor : Descriptor registry)
    (evidence : ResourceBirthAuthority.BatchEvidence pre descriptor)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (other : List DataWrite),
    RealizesAuthority envelope physical domain authorityCellId pre.logical →
    (∀ address ∈ birthTouched descriptor, Vacant envelope physical domain address) →
    intent.writes = other ++ lowerBirth envelope physical domain authorityCellId descriptor
      (ResourceBirthAuthority.post pre descriptor evidence) →
    (intent.writes.map DataWrite.cellId).Nodup →
    Foreign envelope physical other →
    RealizesAuthority envelope (DataSnapshot.install physical intent) domain authorityCellId
        (ResourceBirthAuthority.post pre descriptor evidence).logical ∧
      ∀ address, address ∉ birthTouched descriptor →
        valueAt envelope (DataSnapshot.install physical intent) domain address =
          valueAt envelope physical domain address

/-- **The keystone**: the authority writes of an admitted birth, as the lowering produces them, are
bounded in count and encoded bytes by the budget of the member-authored descriptor, with no term in
the store's key count; they realise the patched logical store; addresses outside the batch are
unchanged. It bounds the authority writes only: the complete record is NOT bounded by the
descriptor while the Book and the factory cell are written whole by every birth. -/
def BirthAuthorityWritesBounded : Prop :=
  BirthAuthorityWriteCount envelope ∧ BirthAuthorityWriteBytes envelope ∧
    BirthAuthorityRealized envelope

theorem birthAuthorityWriteCount : BirthAuthorityWriteCount envelope := by
  intro registry physical domain authorityCellId descriptor post
  simp only [lowerBirth, lowerAuthority_length, birthTouched_length, authorityBirthBudget]
  omega

theorem birthAuthorityRealized : BirthAuthorityRealized envelope := by
  intro registry physical domain authorityCellId pre descriptor evidence intent other realized
    vacant writes distinct foreign
  have frame : ∀ address, address ∉ birthTouched descriptor →
      (ResourceBirthAuthority.post pre descriptor evidence).logical address = pre.logical address := by
    intro address outside
    rw [ResourceBirthAuthority.post_logical]
    exact CredentialAuthorityEffects.setAll_frame _ _ _ outside
  have writes' : intent.writes = other ++ lowerAuthority envelope physical domain authorityCellId
      (birthTouched descriptor) (ResourceBirthAuthority.post pre descriptor evidence).logical
      (CredentialAuthorityCell.materializer.rootOf
        (ResourceBirthAuthority.post pre descriptor evidence).logical) := writes
  exact ⟨lower_realizes envelope realized vacant frame intent other writes' distinct foreign,
    fun address outside =>
      lower_frame envelope realized vacant frame intent other writes' distinct foreign address outside⟩

#assert_axioms lower_realizes
#assert_axioms lower_frame
#assert_axioms omitted_entry_refused
#assert_axioms birthAuthorityWriteCount
#assert_axioms birthAuthorityRealized
#assert_axioms checkVacant_ok_iff
#assert_axioms collision_refused
#assert_axioms head_guard_pins_root
#assert_axioms stale_authority_read_refused

end Minidregg.Compiler.CredentialAuthorityLayout
