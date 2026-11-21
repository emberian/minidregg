/-
# Compiler.CredentialAuthorityEntry -- the cells of the authority store

The physical image of the logical authority `Store` (`CredentialAuthorityState.layout`) is one
HEAD cell at the deployment's pinned `authorityCellId`, holding the logical root, and one ENTRY
cell per store address, holding that address's value with the address in its payload. Both are the
registry's `.authority` kind (`CanonicalCellRegistry`), whose payload is this module's cell.

| cell  | identifier                                             | payload                         |
|-------|--------------------------------------------------------|---------------------------------|
| HEAD  | `deployment.authorityCellId`                           | `head`, `[]`, the logical root  |
| ENTRY | `2^257 + ofDigits 256 (plane tag :: key bytes ++ [1])` | `entry plane`, key, value bytes |

The entry coordinate is injective (`entryCellId_injective`): no two addresses share a cell, so a
lowering never evicts another address and there is no collision to refuse. It is in the authority
space (`ProtectedCell.authorityBase = 2^257`): above every id a birth may choose (below `2^256`)
and above every protected coordinate of the object kernel (`[2^256, 2^257)`).

An address that is logically absent has no payload in its entry cell (or a cell never used): a
logical `free` empties the cell, it does not retire the identifier.

`PhysicalLaw` is the registry's law of the kind: a head sits at the pinned identifier, an entry at
the coordinate of its own plane and key, an emptied cell in the authority space.
-/
module

public import Kernel.ProtectedCell
public import Compiler.CredentialAuthorityCell

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

namespace Minidregg.Compiler.CredentialAuthorityEntry

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CredentialAuthorityCell (planeTag planeOfTag planeOfTag_tag planeOfTag_some
  keyStream valueStream)
open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization

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

/-- The authority role's cell, in the shape of a protected cell (`Kernel.ProtectedCell`: role, key
bytes, body). Its coordinate is not the family's hashed one: an entry sits at `entryId`, an
injective image of its plane and key, so `idCustomization` is unused. -/
def spec : ProtectedCell.Spec where
  Role := Role
  roleStream := roleStream
  idCustomization := []
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

/-- A byte string as a natural, injectively: its bytes as base-256 digits under a leading 1. -/
def natOfBytes (bytes : List UInt8) : Nat :=
  Nat.ofDigits 256 (bytes.map UInt8.toNat ++ [1])

theorem natOfBytes_injective {left right : List UInt8} (same : natOfBytes left = natOfBytes right) :
    left = right := by
  have digits : ∀ bytes : List UInt8,
      Nat.digits 256 (natOfBytes bytes) = bytes.map UInt8.toNat ++ [1] := by
    intro bytes
    apply Nat.digits_ofDigits 256 (by decide)
    · intro digit member
      rcases List.mem_append.mp member with inBytes | last
      · obtain ⟨byte, _, rfl⟩ := List.mem_map.mp inBytes
        exact byte.toNat_lt
      · rw [List.mem_singleton.mp last]; decide
    · intro _; simp
  have lists := (digits left).symm.trans ((congrArg (Nat.digits 256) same).trans (digits right))
  have mapped := List.append_cancel_right lists
  exact (List.map_injective_iff.mpr fun _ _ equal => UInt8.toNat_inj.mp equal) mapped

/-- The length of a byte string bounds its natural: `natOfBytes bytes < 256 ^ (length + 1)`. -/
theorem natOfBytes_lt (bytes : List UInt8) : natOfBytes bytes < 256 ^ (bytes.length + 1) := by
  have bound := Nat.ofDigits_lt_base_pow_length (b := 256) (l := bytes.map UInt8.toNat ++ [1])
    (by decide) (by
      intro digit member
      rcases List.mem_append.mp member with inBytes | last
      · obtain ⟨byte, _, rfl⟩ := List.mem_map.mp inBytes
        exact byte.toNat_lt
      · rw [List.mem_singleton.mp last]; decide)
  simpa [natOfBytes] using bound

/-- The cell of a plane's key bytes: in the authority space (`ProtectedCell.authorityBase`),
injective in the plane and the bytes (`entryId_injective`). -/
def entryId (plane : AuthorityPlane) (key : List UInt8) : Nat :=
  ProtectedCell.authorityBase + natOfBytes (planeTag plane :: key)

theorem entryId_injective {left right : AuthorityPlane} {leftKey rightKey : List UInt8}
    (same : entryId left leftKey = entryId right rightKey) : left = right ∧ leftKey = rightKey := by
  have bytes := natOfBytes_injective (Nat.add_left_cancel same)
  obtain ⟨tags, keys⟩ := List.cons.inj bytes
  have planes := (planeOfTag_tag left).symm.trans ((congrArg planeOfTag tags).trans (planeOfTag_tag right))
  exact ⟨Option.some.inj planes, keys⟩

/-- The cell an address lives at. -/
def entryCellId (address : Address layout) : Nat :=
  entryId address.1 (keyBytes address)

theorem entryCellId_authority (address : Address layout) :
    ProtectedCell.authorityBase ≤ entryCellId address := Nat.le_add_right _ _

/-- **No two addresses share a cell.** -/
theorem entryCellId_injective {left right : Address layout}
    (same : entryCellId left = entryCellId right) : left = right := by
  obtain ⟨leftPlane, leftKey⟩ := left
  obtain ⟨rightPlane, rightKey⟩ := right
  obtain ⟨planes, keys⟩ := entryId_injective same
  subst planes
  have decodedLeft := (keyStream leftPlane).decodePrefix_encode leftKey []
  have decodedRight := (keyStream leftPlane).decodePrefix_encode rightKey []
  change (keyStream leftPlane).encode leftKey = (keyStream leftPlane).encode rightKey at keys
  rw [keys, decodedRight] at decodedLeft
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at decodedLeft
  rw [decodedLeft]

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


/-! ## The law of the kind -/

/-- **The registry's law of an authority cell at `cellId`**: a head sits at the deployment's
pinned identifier with no key; an entry sits at the coordinate of its own plane and key bytes; a
cell with no payload (an emptied entry) is in the authority space. -/
def PhysicalLaw (authorityCellId cellId : Nat) (state : Store (ProtectedCell.layout spec)) : Prop :=
  match ProtectedCell.payloadAt spec state with
  | none => ProtectedCell.authorityBase ≤ cellId
  | some payload =>
      match payload.role with
      | .head => payload.key = [] ∧ cellId = authorityCellId
      | .entry plane => cellId = entryId plane payload.key

instance physicalLawDecidable (authorityCellId cellId : Nat) (state : Store (ProtectedCell.layout spec)) :
    Decidable (PhysicalLaw authorityCellId cellId state) := by
  unfold PhysicalLaw
  split
  · infer_instance
  · split <;> infer_instance

theorem headCell_law (authorityCellId : Nat) (root : Digest) :
    PhysicalLaw authorityCellId authorityCellId (headCell root).logical := by
  simp [PhysicalLaw, headCell, materialize, headPayload]

theorem entryCell_law (authorityCellId : Nat) (address : Address layout)
    (value : Option (layout.Value address.1)) :
    PhysicalLaw authorityCellId (entryCellId address) (entryCell address value).logical := by
  cases value with
  | none => simpa [PhysicalLaw, entryCell, materialize] using entryCellId_authority address
  | some value => simp [PhysicalLaw, entryCell, materialize, entryPayload, entryCellId]

/-- A lawful cell that holds a payload naming an address sits at that address's cell. -/
theorem PhysicalLaw.names {authorityCellId cellId : Nat} {cell : PhysicalCell}
    {payload : ProtectedCell.Payload spec} {address : Address layout}
    (law : PhysicalLaw authorityCellId cellId cell.logical)
    (present : ProtectedCell.payloadAt spec cell.logical = some payload)
    (named : Names payload address) : cellId = entryCellId address := by
  unfold PhysicalLaw at law
  rw [present] at law
  simp only [named.1] at law
  rw [law, named.2]
  rfl

/-! ## Reading one cell back as an entry -/

/-- The entry a cell at `cellId` holds: its plane, the key and value its bytes decode to
(canonically), when it sits at that key's own coordinate. A head, an emptied cell, a payload whose
key or body does not decode and a cell at another coordinate hold none. -/
def entryOf (cellId : Nat) (cell : PhysicalCell) : Option (Entry layout) :=
  (ProtectedCell.payloadAt spec cell.logical).bind fun payload =>
    match payload.role with
    | .head => none
    | .entry plane =>
        ((keyStream plane).toLawful.decode payload.key).bind fun key =>
          ((valueStream plane).toLawful.decode payload.body).bind fun value =>
            if cellId = entryId plane payload.key then some ⟨⟨plane, key⟩, value⟩ else none

/-- What `entryOf` returns is what the cell holds for that address, at that address's cell. -/
theorem entryOf_some {cellId : Nat} {cell : PhysicalCell} {address : Address layout}
    {value : layout.Value address.1} (found : entryOf cellId cell = some ⟨address, value⟩) :
    cellId = entryCellId address ∧ cellValue address cell = some value := by
  unfold entryOf at found
  cases present : ProtectedCell.payloadAt spec cell.logical with
  | none => rw [present] at found; cases found
  | some payload =>
      rw [present] at found
      simp only [Option.bind_some] at found
      cases role : payload.role with
      | head => simp [role] at found
      | entry plane =>
          simp only [role] at found
          cases keyDecoded : (keyStream plane).toLawful.decode payload.key with
          | none => simp [keyDecoded] at found
          | some key =>
              cases valueDecoded : (valueStream plane).toLawful.decode payload.body with
              | none => simp [keyDecoded, valueDecoded] at found
              | some decoded =>
                  simp only [keyDecoded, valueDecoded, Option.bind_some] at found
                  split at found
                  · rename_i placed
                    cases found
                    have keyExact : (keyStream plane).encode key = payload.key :=
                      (keyStream plane).toLawful_canonical _ _ keyDecoded
                    have named : Names payload ⟨plane, key⟩ := ⟨role, keyExact.symm⟩
                    refine ⟨?_, ?_⟩
                    · rw [placed, ← keyExact]; rfl
                    · simp only [cellValue, present, Option.bind_some, payloadValue, if_pos named]
                      exact valueDecoded
                  · cases found

/-- A value a cell holds for an address is the entry `entryOf` returns at the address's cell. -/
theorem entryOf_of_value {cell : PhysicalCell} {address : Address layout}
    {value : layout.Value address.1} (held : cellValue address cell = some value) :
    entryOf (entryCellId address) cell = some ⟨address, value⟩ := by
  unfold cellValue at held
  unfold entryOf
  cases present : ProtectedCell.payloadAt spec cell.logical with
  | none => rw [present] at held; cases held
  | some payload =>
      rw [present] at held
      simp only [Option.bind_some, payloadValue] at held ⊢
      split at held
      · rename_i named
        obtain ⟨plane, key⟩ := address
        have keyDecoded : (keyStream plane).toLawful.decode payload.key = some key := by
          rw [named.2]; exact (keyStream plane).toLawful.decode_encode key
        have placed : entryCellId ⟨plane, key⟩ = entryId plane payload.key := by
          rw [named.2]; rfl
        simp only [named.1, keyDecoded, Option.bind_some]
        change (((valueStream plane).toLawful.decode payload.body).bind fun value =>
          if entryCellId ⟨plane, key⟩ = entryId plane payload.key then
            some (⟨⟨plane, key⟩, value⟩ : Entry layout) else none) = _
        rw [held, Option.bind_some, if_pos placed]
      · cases held

#assert_axioms entryCellId_injective
#assert_axioms entryOf_some
#assert_axioms entryOf_of_value
#assert_axioms headCell_law
#assert_axioms entryCell_law

end Minidregg.Compiler.CredentialAuthorityEntry
