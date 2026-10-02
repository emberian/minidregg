/-
# Compiler.DeclaredEffectCell -- the declared-effect cell on the one store codec

A declared object, program or account-metadata cell IS a store over
`EffectDeclaration.effectLayout`: one RAM namespace keyed by the typed
`StateKey`s, holding exact integers.  Its wire representation is the generic
`StoreCodec` at the declared `wire` below, and its materializer is
`StoreCodec.materializer wire`.  Round trip, canonicity and injectivity are the
general theorems of `Compiler.StoreCodec`; nothing here re-proves them.

This replaces `Compiler.DeclaredEffectPageMaterializer`, which represented the
same store as one four-slot page (`slot0 … slot3`) in one of sixteen address
shards, with the capacity `4` and the shard modulus `16` pinned into its wire
frame `LOOM/EFFECT/PAGE ++ [1, 4, 16]`.  That page, its shard, its capacity
byte, its `overflow`/`unsupportedAddress` reject reasons and its 2⁴-way case
proofs are deleted.  A resource now has as many fields as it declares
(`resource_fields_roundtrip`, instantiated at 32), and a `create` at any fresh
field is accepted by the action semantics (`create_fresh_field_accepted`,
instantiated at the journey's field 103).  Whether the kernel admits it is the
cell's declaration's to say (K-FIELD-CLOSURE, `Kernel.FieldClosure`): a cell
holds only the fields it declared at birth, unless it declared itself open.

**What refuses to load.**  Every page-era cell began with the page frame's
`'L'` (76); the store frame begins with `'D'` (68).  `retired_page_frame_refused`
states that every old effect page is refused by the cell codec, whatever
follows its header.  There is no decoder for the old frame.
-/
import Compiler.IntStream
import Compiler.StoreCodec
import Theory.DeclaredActionLowering

namespace Minidregg.Compiler.DeclaredEffectCell

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.IntStream (intStream intCodecId)
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The declared wire of the effect layout -/

/-- Typed state keys: a kind tag, then the primary resource identifier, then
(for object fields and balances) the full field or resource digest. -/
def stateKeyStream : StreamCodec StateKey where
  encode
    | .objectField object field =>
        0 :: StreamCodec.nat.encode object.value ++ digestStream.encode field
    | .accountBalance account resource =>
        1 :: StreamCodec.nat.encode account.value ++ digestStream.encode resource
    | .programCode program =>
        2 :: StreamCodec.nat.encode program.value
    | .blinding => [3]
    | .fieldDeclared object field =>
        4 :: StreamCodec.nat.encode object.value ++ digestStream.encode field
    | .fieldsOpen object =>
        5 :: StreamCodec.nat.encode object.value
  decodePrefix
    | 0 :: bytes => do
        let (object, afterObject) <- StreamCodec.nat.decodePrefix bytes
        let (field, suffix) <- digestStream.decodePrefix afterObject
        some (.objectField ⟨object⟩ field, suffix)
    | 1 :: bytes => do
        let (account, afterAccount) <- StreamCodec.nat.decodePrefix bytes
        let (resource, suffix) <- digestStream.decodePrefix afterAccount
        some (.accountBalance ⟨account⟩ resource, suffix)
    | 2 :: bytes => do
        let (program, suffix) <- StreamCodec.nat.decodePrefix bytes
        some (.programCode ⟨program⟩, suffix)
    | 3 :: suffix => some (.blinding, suffix)
    | 4 :: bytes => do
        let (object, afterObject) <- StreamCodec.nat.decodePrefix bytes
        let (field, suffix) <- digestStream.decodePrefix afterObject
        some (.fieldDeclared ⟨object⟩ field, suffix)
    | 5 :: bytes => do
        let (object, suffix) <- StreamCodec.nat.decodePrefix bytes
        some (.fieldsOpen ⟨object⟩, suffix)
    | _ => none
  decodePrefix_encode := by
    intro key suffix
    cases key with
    | objectField object field =>
        simp [List.append_assoc, StreamCodec.nat.decodePrefix_encode,
          digestStream.decodePrefix_encode]
    | accountBalance account resource =>
        simp [List.append_assoc, StreamCodec.nat.decodePrefix_encode,
          digestStream.decodePrefix_encode]
    | programCode program =>
        simp [StreamCodec.nat.decodePrefix_encode]
    | blinding => rfl
    | fieldDeclared object field =>
        simp [List.append_assoc, StreamCodec.nat.decodePrefix_encode,
          digestStream.decodePrefix_encode]
    | fieldsOpen object =>
        simp [StreamCodec.nat.decodePrefix_encode]

/-- v3 (INTEGRATOR-3): tag 3 is the blinding (K-NARROW-HIDE, the proof braid's v2), tags 4 and 5
a cell's declaration (K-FIELD-CLOSURE, the compute braid's v2 at tags 3 and 4). Both v2s and v1
lay out a different digest, so every earlier declared cell is refused
(`StoreCodec.decode_other_layout`), never reinterpreted. -/
def stateKeyCodecId : String := "state-key/tagged-v3"

/-- The effect layout on the wire.  Its single namespace contributes no bytes;
keys are typed state keys and values are zigzag integers. -/
def wire : Wire effectLayout where
  name := "minidregg/declared-effect/v1"
  namespaces := [()]
  namespaces_complete := by intro space; cases space; simp
  namespaceStream := unitStream
  keyStream := fun _ => stateKeyStream
  valueStream := fun _ => intStream
  keyCodecId := fun _ => stateKeyCodecId
  valueCodecId := fun _ => intCodecId
  blinding := some StateKey.blinding.address

/-- The declared cell's blinding (K-HIDE-ROTATE): `StateKey.blinding`, an
integer; a ratchet link is its non-negative natural. -/
def blinding : Blinding wire where
  space := ()
  key := .blinding
  isBlinding := rfl
  ofLink value := Int.ofNat value

/-- The declared-effect cell materializer: the generic store codec at `wire`,
rooted by `StoreCodec.rootBytes`. -/
def materializer : Materializer effectLayout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

@[simp] theorem materializer_encode (store : Store effectLayout) :
    materializer.codec.encode store = StoreCodec.encode wire store :=
  rfl

@[simp] theorem materializer_decode (bytes : List UInt8) :
    materializer.codec.decode bytes = StoreCodec.decode wire bytes :=
  rfl

/-- The cell bytes are exactly the store encoding of the cell's logical store. -/
theorem cell_bytes (cell : Cell) : cell.bytes = StoreCodec.encode wire cell.logical :=
  rfl

/-- A cell's bytes are accepted and denote exactly its store. -/
theorem cell_decode (cell : Cell) :
    StoreCodec.decode wire cell.bytes = some cell.logical := by
  rw [cell_bytes]
  exact decode_encode wire cell.logical

/-! ## Unbounded fields at one resource (the K4 exit, stated at the cell) -/

/-- Field `i` of object `object`, holding `i`. -/
def objectEntry (object : ResourceId .object) (index : Nat) : Entry effectLayout :=
  ⟨(StateKey.objectField object ⟨index⟩).address, (index : Int)⟩

/-- The object resource with exactly the fields `0 … size-1`. -/
def objectFields (object : ResourceId .object) (size : Nat) : Store effectLayout :=
  fromEntries ((List.range size).map (objectEntry object))

private theorem objectEntry_addresses (object : ResourceId .object) (size : Nat) :
    ((List.range size).map (objectEntry object)).map Sigma.fst =
      (List.range size).map fun index =>
        (StateKey.objectField object ⟨index⟩).address := by
  rw [List.map_map]
  rfl

private theorem objectEntry_addresses_nodup (object : ResourceId .object) (size : Nat) :
    (((List.range size).map (objectEntry object)).map Sigma.fst).Nodup := by
  rw [objectEntry_addresses]
  apply List.Nodup.map _ List.nodup_range
  intro left right same
  have keys := StateKey.address_injective same
  simpa using keys

/-- Every field below `size` is present with its value. -/
theorem objectFields_read (object : ResourceId .object) (size index : Nat)
    (below : index < size) :
    objectFields object size (StateKey.objectField object ⟨index⟩).address =
      some (index : Int) :=
  fromEntries_apply_of_mem _ (objectEntry_addresses_nodup object size)
    (List.mem_map.mpr ⟨index, List.mem_range.mpr below, rfl⟩)

/-- Every field at or above `size` is absent. -/
theorem objectFields_fresh (object : ResourceId .object) (size index : Nat)
    (above : size ≤ index) :
    objectFields object size (StateKey.objectField object ⟨index⟩).address = none := by
  unfold objectFields
  rw [fromEntries_apply_eq_none_iff, objectEntry_addresses]
  intro member
  obtain ⟨other, inRange, same⟩ := List.mem_map.mp member
  have keys := StateKey.address_injective same
  simp only [StateKey.objectField.injEq, Digest.mk.injEq, true_and] at keys
  have := List.mem_range.mp inRange
  omega

/-- The store's support is exactly `size` addresses, all of one object. -/
theorem objectFields_support_card (object : ResourceId .object) (size : Nat) :
    (objectFields object size).support.card = size := by
  have support : (objectFields object size).support =
      ((List.range size).map fun index =>
        (StateKey.objectField object ⟨index⟩).address).toFinset := by
    ext address
    rw [DFinsupp.mem_support_toFun, List.mem_toFinset, ← objectEntry_addresses]
    exact (fromEntries_apply_eq_none_iff _ address).not.trans not_not
  rw [support, List.toFinset_card_of_nodup]
  · rw [List.length_map]
    exact List.length_range
  · rw [← objectEntry_addresses]
    exact objectEntry_addresses_nodup object size

theorem objectFields_one_resource (object : ResourceId .object) (size : Nat)
    (address : Address effectLayout) (present : address ∈ (objectFields object size).support) :
    ∃ index < size, address = (StateKey.objectField object ⟨index⟩).address := by
  rw [DFinsupp.mem_support_toFun] at present
  have listed : address ∈ ((List.range size).map (objectEntry object)).map Sigma.fst := by
    by_contra absent
    exact present ((fromEntries_apply_eq_none_iff _ address).mpr absent)
  rw [objectEntry_addresses] at listed
  obtain ⟨index, inRange, same⟩ := List.mem_map.mp listed
  exact ⟨index, List.mem_range.mp inRange, same.symm⟩

/-- **A resource of any field count is one cell.**  The object with fields
`0 … size-1` materializes as one declared-effect cell; its support is exactly
those `size` fields of that one object; its bytes decode back to it. -/
theorem resource_fields_roundtrip (object : ResourceId .object) (size : Nat) :
    let cell := materialize materializer (objectFields object size)
    cell.logical.support.card = size ∧
      (∀ index < size,
        cell.logical (StateKey.objectField object ⟨index⟩).address = some (index : Int)) ∧
      materializer.codec.decode cell.bytes = some cell.logical :=
  ⟨objectFields_support_card object size,
    fun index below => objectFields_read object size index below,
    cell_decode _⟩

/-- The K4 growth exit: a 32-field resource round-trips through the cell. -/
theorem resource_32_fields_roundtrip (object : ResourceId .object) :
    let cell := materialize materializer (objectFields object 32)
    cell.logical.support.card = 32 ∧
      (∀ index < 32,
        cell.logical (StateKey.objectField object ⟨index⟩).address = some (index : Int)) ∧
      materializer.codec.decode cell.bytes = some cell.logical :=
  resource_fields_roundtrip object 32

/-! ## A fresh field is always creatable; a present one is guarded -/

/-- The one-action declaration creating field `index` of `object`. -/
def createField (object : ResourceId .object) (index : Nat) (initial : Int) :
    DeclaredActionLowering.Declaration object where
  schemaVersion := 1
  expectedPreRoot := ⟨0⟩
  nonce := 0
  actions := [.create (.objectField object ⟨index⟩) initial]

/-- There is no capacity: at every size, creating the next field is accepted
and yields a resource with one more field.  (The deleted page refused the fifth
field with `overflow`.) -/
theorem create_fresh_field_accepted (object : ResourceId .object) (size : Nat)
    (initial : Int) :
    (createField object size initial).run (objectFields object size) =
      some ((objectFields object size).set
        (StateKey.objectField object ⟨size⟩).address (some initial)) := by
  rw [Declaration.run_eq_some_iff]
  refine ⟨?_, ?_, rfl⟩
  · simp [Declaration.Admitted, Declaration.admissionCheck, createField,
      Action.admissionCheck, writableKeyCheck]
  · have fresh : objectFields object size ⟨(), .objectField object ⟨size⟩⟩ = none :=
      objectFields_fresh object size size le_rfl
    simp [Patch.ValidFrom, DeclaredActionLowering.Declaration.patch, createField, Action.ops,
      guardedSet, Op.Enabled, Store.Fresh, fresh]

/-- The journey's step: `create` at field 103 of a 103-field resource. -/
theorem create_field_103_accepted (object : ResourceId .object) (initial : Int) :
    (createField object 103 initial).run (objectFields object 103) ≠ none := by
  rw [create_fresh_field_accepted]
  simp

/-- Refuting pole: `create` at a present field is refused by its absence guard. -/
theorem create_present_field_refused (object : ResourceId .object) (size index : Nat)
    (below : index < size) (initial : Int) :
    (createField object index initial).run (objectFields object size) = none := by
  cases refused : (createField object index initial).run (objectFields object size) with
  | none => rfl
  | some post =>
      obtain ⟨_, valid, _⟩ := (Declaration.run_eq_some_iff _ _ _).mp refused
      have present : objectFields object size ⟨(), .objectField object ⟨index⟩⟩ =
          some (index : Int) := objectFields_read object size index below
      simp [Patch.ValidFrom, DeclaredActionLowering.Declaration.patch, createField, Action.ops,
        guardedSet, Op.Enabled, Store.Fresh, present] at valid

/-! ## Retired page cells refuse to load -/

/-- The header of the deleted effect page: `LOOM/EFFECT/PAGE`, version 1,
capacity 4, shard modulus 16.  Kept only to state its refusal. -/
def retiredPageFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 69, 70, 70, 69, 67, 84, 47, 80, 65, 71, 69, 1, 4, 16]

theorem retired_page_frame_refused (payload : List UInt8) :
    materializer.codec.decode (retiredPageFrame ++ payload) = none :=
  decode_other_first_byte wire 76 (retiredPageFrame.drop 1 ++ payload) (by decide)

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.DeclaredEffectCell.resource_fields_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resource_fields_roundtrip
/-- info: 'Minidregg.Compiler.DeclaredEffectCell.resource_32_fields_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resource_32_fields_roundtrip
/-- info: 'Minidregg.Compiler.DeclaredEffectCell.create_fresh_field_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms create_fresh_field_accepted
/-- info: 'Minidregg.Compiler.DeclaredEffectCell.create_field_103_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms create_field_103_accepted
/-- info: 'Minidregg.Compiler.DeclaredEffectCell.create_present_field_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms create_present_field_refused
/-- info: 'Minidregg.Compiler.DeclaredEffectCell.retired_page_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_page_frame_refused

end Minidregg.Compiler.DeclaredEffectCell
