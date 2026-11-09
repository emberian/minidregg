/-
# Compiler.StoreCodecHeld -- a store's payload, held encoded and moved by its writes

`StoreCodec.payloadStream` encodes a store as its entries sorted by address bytes
(`StoreCodec.entries`: the support sorted by `addressKey`, then each entry encoded). A store that
grows by a row per record (the World's system store: a journal row per turn) pays the sort and
every entry's encode at every encode. `HeldEntries W store` holds each present entry's encoding
keyed by its address's comparison key, in a balanced tree whose order IS the payload's order:

* `set` / `apply` / `run` move it by the addresses a write touches (O(log n) each);
* `payload` is the length prefix and the held encodings concatenated in key order, and
  `payload_eq` proves it is `payloadStream W` of the store, byte for byte.
-/
module

public import Compiler.StoreCodec
public import Std.Data.ExtTreeMap

@[expose] public section

namespace Minidregg.Compiler.StoreCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store

set_option autoImplicit false

/-- `compare` on lists of naturals is their lexicographic `<`. -/
theorem listNat_compare_lt : ∀ (a b : List Nat), compare a b = .lt ↔ a < b
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
      rw [List.compare_eq_compareLex, List.compareLex_cons_cons, ← List.compare_eq_compareLex,
        List.cons_lt_cons_iff, ← listNat_compare_lt xs ys]
      rcases Nat.lt_trichotomy x y with h | h | h
      · simp [Nat.compare_eq_lt.mpr h, h]
      · subst h; simp
      · simp [Nat.compare_eq_gt.mpr h, Nat.ne_of_gt h, Nat.not_lt.mpr (Nat.le_of_lt h)]

section Held

variable {L : Layout.{0, 0, 0}} (W : Wire L)

/-- One entry's encoding, written once. -/
def entryArray (entry : Entry L) : ByteArray := (entryStream W).encodeBytes entry

theorem entryArray_data (entry : Entry L) :
    (entryArray W entry).data.toList = (entryStream W).encode entry :=
  StreamCodec.encodeBytes_data _ _

/-- A store's present entries, each encoded once, keyed by its address's comparison key. -/
structure HeldEntries (store : Store L) where
  map : Std.ExtTreeMap (List Nat) ByteArray compare
  exact : ∀ address, map[addressKey W address]? =
    (store address).map fun value => entryArray W ⟨address, value⟩
  keyed : ∀ key, key ∈ map → ∃ address : Address L, addressKey W address = key

namespace HeldEntries

variable {W}

/-- The empty store's. -/
def empty : HeldEntries W (0 : Store L) where
  map := ∅
  exact := by intro address; simp [Minidregg.Theory.SparseMap.zero_apply]
  keyed := by intro key member; simp at member

/-- Moved by one `set`. -/
def set {store : Store L} (held : HeldEntries W store) (address : Address L)
    (value : Option (L.Value address.1)) : HeldEntries W (store.set address value) where
  map := match value with
    | none => held.map.erase (addressKey W address)
    | some found => held.map.insert (addressKey W address) (entryArray W ⟨address, found⟩)
  exact := by
    intro other
    by_cases same : other = address
    · subst same
      cases value <;> simp [Store.set_eq]
    · have distinct : addressKey W address ≠ addressKey W other :=
        fun h => same ((addressKey_injective W) h).symm
      rw [Store.set_ne _ _ _ _ same, ← held.exact other]
      cases value with
      | none => simp [Std.ExtTreeMap.getElem?_erase, distinct]
      | some found => simp [Std.ExtTreeMap.getElem?_insert, distinct]
  keyed := by
    intro key member
    cases value with
    | none =>
        exact held.keyed key (Std.ExtTreeMap.mem_of_mem_erase member)
    | some found =>
        rcases Std.ExtTreeMap.mem_insert.mp member with h | h
        · exact ⟨address, Std.LawfulEqCmp.eq_of_compare h⟩
        · exact held.keyed key h

/-- Moved by one operation: the address it writes, set to what it writes. -/
def apply {store : Store L} (held : HeldEntries W store) : (op : Op L) → HeldEntries W (op.apply store)
  | .read _ _ _ => held
  | .write space key _ after => held.set ⟨space, key⟩ (some after)
  | .allocate space key value => held.set ⟨space, key⟩ (some value)
  | .free space key _ => held.set ⟨space, key⟩ none

/-- Moved by a patch, one operation at a time. -/
def run {store : Store L} (held : HeldEntries W store) : (patch : Patch L) →
    HeldEntries W (Patch.run store patch)
  | [] => held
  | op :: rest => (held.apply op).run rest

/-- A list's reconstruction, one `set` per entry (`fromEntries`' own recursion). -/
def ofList : (entryList : List (Entry L)) → HeldEntries W (fromEntries entryList)
  | [] => empty
  | entry :: rest => (ofList rest).set entry.1 (some entry.2)

/-- A store's, built once (an open): its canonical entries, one `set` each. -/
def ofStore (store : Store L) : HeldEntries W store :=
  fromEntries_entries W store ▸ ofList (entries W store)

private theorem mem_entries {store : Store L} {entry : Entry L} :
    entry ∈ entries W store ↔ store entry.1 = some entry.2 := by
  unfold entries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨address, _, found⟩
    rw [Option.map_eq_some_iff] at found
    obtain ⟨value, present, rfl⟩ := found
    exact present
  · intro present
    refine ⟨entry.1, (mem_sortedSupport W store entry.1).mpr (by simp [present]), ?_⟩
    simp [present]

/-- **The held tree in key order is the canonical entry list, each entry encoded.** -/
theorem toList_eq {store : Store L} (held : HeldEntries W store) :
    held.map.toList = (entries W store).map fun entry => (addressKey W entry.1, entryArray W entry) := by
  have ordered : held.map.toList.Pairwise fun a b => compare a.1 b.1 = .lt :=
    Std.ExtTreeMap.ordered_keys_toList
  have canonical : ((entries W store).map fun entry => (addressKey W entry.1, entryArray W entry)).Pairwise
      fun a b => compare a.1 b.1 = .lt := by
    rw [List.pairwise_map]
    exact (entries_pairwise W store).imp fun less => (listNat_compare_lt _ _).mpr less
  have members : ∀ pair, pair ∈ held.map.toList ↔
      pair ∈ (entries W store).map fun entry => (addressKey W entry.1, entryArray W entry) := by
    rintro ⟨key, bytes⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, List.mem_map]
    constructor
    · intro found
      obtain ⟨address, rfl⟩ := held.keyed key (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [found]))
      rw [held.exact address, Option.map_eq_some_iff] at found
      obtain ⟨value, present, rfl⟩ := found
      exact ⟨⟨address, value⟩, mem_entries.mpr present, rfl⟩
    · rintro ⟨entry, member, same⟩
      cases same
      rw [held.exact entry.1, mem_entries.mp member]
      rfl
  have asymm : ∀ a b : List Nat × ByteArray, compare a.1 b.1 = .lt → compare b.1 a.1 = .lt → False := by
    intro a b first second
    rw [listNat_compare_lt] at first second
    exact absurd (first.trans second) (lt_irrefl _)
  have nodupOf : ∀ l : List (List Nat × ByteArray), l.Pairwise (fun a b => compare a.1 b.1 = .lt) → l.Nodup :=
    fun l sorted => sorted.imp fun {a b} less same => by
      subst same
      exact asymm a a less less
  exact List.Perm.eq_of_pairwise (fun a b _ _ first second => (asymm a b first second).elim) ordered canonical
    ((List.perm_ext_iff_of_nodup (nodupOf _ ordered) (nodupOf _ canonical)).mpr members)

/-- The payload: the entry count, then the held encodings in key order. -/
def payload {store : Store L} (held : HeldEntries W store) : ByteArray :=
  held.map.foldl (fun out _ bytes => out ++ bytes) (StreamCodec.nat.encodeBytes held.map.size)

private theorem foldl_append_data (pairs : List (List Nat × ByteArray)) (out : ByteArray) :
    (pairs.foldl (fun out pair => out ++ pair.2) out).data.toList =
      out.data.toList ++ pairs.flatMap fun pair => pair.2.data.toList := by
  induction pairs generalizing out with
  | nil => simp
  | cons pair rest ih =>
      rw [List.foldl_cons, ih, ByteArray.data_append, Array.toList_append, List.flatMap_cons,
        List.append_assoc]

private theorem encodeMany_eq (entryList : List (Entry L)) :
    StreamCodec.encodeMany (entryStream W) entryList =
      (entryList.map fun entry => (addressKey W entry.1, entryArray W entry)).flatMap
        fun pair => pair.2.data.toList := by
  induction entryList with
  | nil => rfl
  | cons entry rest ih =>
      rw [StreamCodec.encodeMany, ih, List.map_cons, List.flatMap_cons, entryArray_data]

/-- **The held payload is the store's payload encoding**, byte for byte. -/
theorem payload_eq {store : Store L} (held : HeldEntries W store) :
    held.payload.data.toList = (payloadStream W).encode store := by
  have size : held.map.size = (entries W store).length := by
    rw [← Std.ExtTreeMap.length_toList, held.toList_eq, List.length_map]
  rw [payload, Std.ExtTreeMap.foldl_eq_foldl_toList, foldl_append_data, held.toList_eq,
    payloadStream_encode, size, StreamCodec.encodeBytes_data, ← encodeMany_eq]
  rfl

end HeldEntries

end Held

end Minidregg.Compiler.StoreCodec

#assert_axioms Minidregg.Compiler.StoreCodec.HeldEntries.toList_eq
#assert_axioms Minidregg.Compiler.StoreCodec.HeldEntries.payload_eq
