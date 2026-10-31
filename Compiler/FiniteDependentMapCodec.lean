/-
# Compiler.FiniteDependentMapCodec -- one finite sparse encoding construction

Finite support is structural `DFinsupp` data. Keys are canonically sorted and
each dependent value is read at its actual key. The decoder reconstructs that
same finite map; there is no countability-selected enumeration or focused
codec. The whole-map stream (`xmap` of an entry list onto the map) is gone: it
decoded unsorted, duplicated and explicit-zero entry lists into the same map, so
it was not canonical, and nothing used it. Carriers compose `entryStream`.
-/
module

public import Compiler.Tower256ConcreteBackend
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.DFinsupp.Defs
public import Std.Data.DTreeMap.Lemmas

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

namespace Minidregg.Compiler.FiniteDependentMapCodec

open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

variable {K : Type} {V : K → Type} [DecidableEq K] [∀ key, Zero (V key)]

def fromEntries : List (Sigma V) → (Π₀ key : K, V key)
  | [] => 0
  | ⟨key, value⟩ :: entries => (fromEntries entries).update key value

/-- The mathematical order supplies the lawful comparison used by the decoder's tree. -/
private instance orderedTransCmp [LinearOrder K] :
    Std.TransCmp (fun a b : K => compareOfLessAndEq a b) :=
  Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    le_antisymm le_trans le_total not_le

private instance orderedEqCmp [LinearOrder K] :
    Std.LawfulEqCmp (fun a b : K => compareOfLessAndEq a b) where
  compare_self := by simp [compareOfLessAndEq]
  eq_of_compare := (compareOfLessAndEq_eq_eq le_refl not_le).mp

/-- Insert from the tail: the first occurrence still wins, including an explicit zero. -/
private def entryTree [LinearOrder K] : List (Sigma V) →
    Std.DTreeMap K V (fun a b => compareOfLessAndEq a b)
  | [] => ∅
  | ⟨key, value⟩ :: rest => (entryTree rest).insert key value

/-- Build finite support once and use a balanced dependent tree for subsequent lookups. -/
def fromEntriesFast [LinearOrder K] (items : List (Sigma V)) : (Π₀ key : K, V key) :=
  let tree := entryTree items
  DFinsupp.mk' (fun key => tree.getD key 0) (Trunc.mk
    ⟨(tree.keys : Multiset K), by
      intro key
      by_cases present : key ∈ tree
      · exact Or.inl (by simpa using (Std.DTreeMap.mem_keys.mpr present))
      · exact Or.inr (Std.DTreeMap.getD_eq_fallback present)⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Representation changes no map value, even for duplicates, arbitrary order, or zeros. -/
@[simp] theorem fromEntriesFast_eq [LinearOrder K] (items : List (Sigma V)) :
    fromEntriesFast items = fromEntries items := by
  apply DFinsupp.ext
  intro key
  change (entryTree items).getD key 0 = fromEntries items key
  induction items with
  | nil => simp [entryTree, fromEntries]
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      by_cases equal : head = key
      · subst head
        simp [entryTree, fromEntries]
      · rw [entryTree, Std.DTreeMap.getD_insert]
        have different : compareOfLessAndEq head key ≠ .eq := by
          intro same
          exact equal (Std.LawfulEqCmp.eq_of_compare (cmp := fun a b : K => compareOfLessAndEq a b) same)
        simp [different, fromEntries, DFinsupp.update, Function.update, Ne.symm equal, ih]

theorem fromEntries_map (keys : List K) (fields : Π₀ key : K, V key) (key : K) :
    fromEntries (keys.map (fun key => ⟨key, fields key⟩)) key =
      if key ∈ keys then fields key else 0 := by
  induction keys with
  | nil => simp [fromEntries]
  | cons head rest induction =>
      by_cases equal : key = head
      · subst key
        simp [fromEntries]
      · simp [fromEntries, DFinsupp.update, equal, induction]

def entries [LinearOrder K] [∀ key, DecidableEq (V key)]
    (fields : Π₀ key : K, V key) : List (Sigma V) :=
  (fields.support.sort (· ≤ ·)).map (fun key => ⟨key, fields key⟩)

theorem fromEntries_entries [LinearOrder K] [∀ key, DecidableEq (V key)]
    (fields : Π₀ key : K, V key) : fromEntries (entries fields) = fields := by
  apply DFinsupp.ext
  intro key
  rw [entries, fromEntries_map]
  simp only [Finset.mem_sort, DFinsupp.mem_support_toFun]
  split_ifs with present
  · rfl
  · simpa using (not_not.mp present).symm

/-- The decoded key chooses its own value type before payload decoding. -/
def entryStream (keyStream : StreamCodec K)
    (valueStream : (key : K) → StreamCodec (V key)) : StreamCodec (Sigma V) where
  encode entry := keyStream.encode entry.1 ++ (valueStream entry.1).encode entry.2
  decodePrefix bytes := do
    let (key, afterKey) ← keyStream.decodePrefix bytes
    let (value, suffix) ← (valueStream key).decodePrefix afterKey
    some (⟨key, value⟩, suffix)
  decodePrefix_encode := by
    rintro ⟨key, value⟩ suffix
    simp [List.append_assoc, keyStream.decodePrefix_encode,
      (valueStream key).decodePrefix_encode]
  encode_decodePrefix := by
    intro bytes entry suffix decoded
    cases keyOk : keyStream.decodePrefix bytes with
    | none => simp [keyOk] at decoded
    | some keyPair =>
      obtain ⟨key, afterKey⟩ := keyPair
      cases valueOk : (valueStream key).decodePrefix afterKey with
      | none => simp [keyOk, valueOk] at decoded
      | some valuePair =>
        obtain ⟨value, rest⟩ := valuePair
        simp only [keyOk, valueOk, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rw [List.append_assoc, (valueStream key).encode_decodePrefix _ _ _ valueOk,
          keyStream.encode_decodePrefix _ _ _ keyOk]
  decodeAt bytes start :=
    match keyStream.decodeAt bytes start with
    | some (key, afterKey) =>
        match (valueStream key).decodeAt bytes afterKey with
        | some (value, after) => some (⟨key, value⟩, after)
        | none => none
    | none => none
  decodeAt_spec := by
    intro bytes start inside
    rw [keyStream.decodeAt_spec bytes start inside]
    simp only [cursorOfPrefix]
    cases keyOk : keyStream.decodePrefix (bytes.data.toList.drop start) with
    | none => rfl
    | some keyPair =>
        obtain ⟨key, afterKey⟩ := keyPair
        simp only [Option.map_some]
        rw [(valueStream key).decodeAt_spec bytes _ (Nat.sub_le _ _)]
        simp only [cursorOfPrefix, keyStream.rest_at keyOk]
        cases valueOk : (valueStream key).decodePrefix afterKey <;> simp [valueOk]
  encodeInto out entry := (valueStream entry.1).encodeInto (keyStream.encodeInto out entry.1) entry.2
  encodeInto_spec := by
    intro out entry
    rw [(valueStream entry.1).encodeInto_spec, keyStream.encodeInto_spec, List.append_assoc]
  -- `cursorNative` stays false: whether every `valueStream key` is native is not computable
  -- for an arbitrary key type. A consumer that knows its keys sets the bit on the codec it
  -- decodes with (`StoreCodec.payloadStream`, by `StoreCodec.Wire.cursorReady`).

/-! ## Canonical finite sets and sparse maps

A finite set is spelled as its strictly increasing element list and a sparse
map as its strictly key-increasing list of non-default entries. The decoders
REFUSE every other list (unsorted, duplicated, explicit default), so each set
and each map has exactly one spelling; the bytes are those of the sorted list. -/

theorem sort_isChain {α : Type} [LinearOrder α] (values : Finset α) :
    (values.sort (· ≤ ·)).IsChain (· < ·) :=
  (Finset.sortedLT_sort values).isChain

theorem sort_toFinset_of_isChain {α : Type} [LinearOrder α] {values : List α}
    (chain : values.IsChain (· < ·)) : values.toFinset.sort (· ≤ ·) = values := by
  have pairwise : values.Pairwise (· < ·) := List.isChain_iff_pairwise.mp chain
  exact (List.toFinset_sort (· ≤ ·) pairwise.nodup).mpr (pairwise.imp le_of_lt)

/-- A finite set as its strictly increasing element list. -/
def finsetStream {α : Type} [LinearOrder α] (codec : StreamCodec α) : StreamCodec (Finset α) :=
  StreamCodec.xmap
    (StreamCodec.refine (StreamCodec.list codec) (List.IsChain (· < ·)))
    (fun values => ⟨values.sort (· ≤ ·), sort_isChain values⟩)
    (fun values => values.val.toFinset)
    (by intro values; exact Finset.sort_toFinset _ _)
    (by intro values; exact Subtype.ext (sort_toFinset_of_isChain values.property))

theorem finsetStream_encode {α : Type} [LinearOrder α] (codec : StreamCodec α) (values : Finset α) :
    (finsetStream codec).encode values = (StreamCodec.list codec).encode (values.sort (· ≤ ·)) :=
  rfl

/-- The canonical spelling of a sparse map: keys strictly increasing, no
explicit default value. -/
def CanonicalEntries [LinearOrder K] (items : List (Sigma V)) : Prop :=
  (items.map Sigma.fst).IsChain (· < ·) ∧ ∀ entry ∈ items, entry.2 ≠ 0

instance [LinearOrder K] [∀ key, DecidableEq (V key)] :
    DecidablePred (CanonicalEntries (K := K) (V := V)) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem entries_canonical [LinearOrder K] [∀ key, DecidableEq (V key)]
    (fields : Π₀ key : K, V key) : CanonicalEntries (entries fields) := by
  refine ⟨?_, ?_⟩
  · have keys : (entries fields).map Sigma.fst = fields.support.sort (· ≤ ·) := by
      simp [entries, List.map_map, Function.comp_def]
    rw [keys]
    exact sort_isChain _
  · intro entry member
    simp only [entries, List.mem_map, Finset.mem_sort] at member
    obtain ⟨key, present, rfl⟩ := member
    simpa using present

set_option backward.isDefEq.respectTransparency false in
theorem mem_keys_of_fromEntries_ne {items : List (Sigma V)} {key : K}
    (nonzero : fromEntries items key ≠ 0) : key ∈ items.map Sigma.fst := by
  induction items with
  | nil => simp [fromEntries] at nonzero
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      by_cases same : head = key
      · simp [same]
      · have restNonzero : fromEntries rest key ≠ 0 := by
          simpa [fromEntries, DFinsupp.update, Function.update, Ne.symm same] using nonzero
        simp [ih restNonzero]

set_option backward.isDefEq.respectTransparency false in
theorem entries_fromEntries_of_canonical [LinearOrder K] [∀ key, DecidableEq (V key)]
    (items : List (Sigma V)) (canonical : CanonicalEntries items) :
    entries (fromEntries items) = items := by
  induction items with
  | nil =>
      simp [entries, fromEntries]
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      obtain ⟨chain, nonzero⟩ := canonical
      have pairwise : ((⟨head, value⟩ :: rest : List (Sigma V)).map Sigma.fst).Pairwise (· < ·) :=
        List.isChain_iff_pairwise.mp chain
      simp only [List.map_cons, List.pairwise_cons] at pairwise
      obtain ⟨headLeast, restPairwise⟩ := pairwise
      have restCanonical : CanonicalEntries rest :=
        ⟨List.isChain_iff_pairwise.mpr restPairwise,
          fun entry member => nonzero entry (List.mem_cons_of_mem _ member)⟩
      have valueNonzero : value ≠ 0 := nonzero ⟨head, value⟩ List.mem_cons_self
      have below : ∀ key ∈ (fromEntries rest).support, head ≤ key := by
        intro key member
        exact le_of_lt (headLeast key (mem_keys_of_fromEntries_ne (DFinsupp.mem_support_iff.mp member)))
      have absent : head ∉ (fromEntries rest).support := by
        intro member
        exact lt_irrefl head (headLeast head (mem_keys_of_fromEntries_ne (DFinsupp.mem_support_iff.mp member)))
      have support : (fromEntries (⟨head, value⟩ :: rest)).support =
          insert head (fromEntries rest).support := by
        simp only [fromEntries]
        exact DFinsupp.support_update_ne_zero _ _ valueNonzero
      unfold entries
      rw [support, Finset.sort_insert (· ≤ ·) below absent, List.map_cons]
      have headValue : fromEntries (⟨head, value⟩ :: rest) head = value := by
        simp [fromEntries]
      rw [headValue]
      congr 1
      have tail : ((fromEntries rest).support.sort (· ≤ ·)).map
            (fun key => (⟨key, fromEntries (⟨head, value⟩ :: rest) key⟩ : Sigma V)) =
          ((fromEntries rest).support.sort (· ≤ ·)).map
            (fun key => (⟨key, fromEntries rest key⟩ : Sigma V)) := by
        apply List.map_congr_left
        intro key member
        have different : key ≠ head := by
          intro same
          subst same
          exact absent ((Finset.mem_sort _).mp member)
        simp [fromEntries, DFinsupp.update, Function.update, different]
      rw [tail]
      exact ih restCanonical

/-- A sparse map as its canonical entry list. -/
def mapStream [LinearOrder K] [∀ key, DecidableEq (V key)]
    (keyStream : StreamCodec K) (valueStream : (key : K) → StreamCodec (V key)) :
    StreamCodec (Π₀ key : K, V key) :=
  StreamCodec.xmap
    (StreamCodec.refine (StreamCodec.list (entryStream keyStream valueStream)) CanonicalEntries)
    (fun fields => ⟨entries fields, entries_canonical fields⟩)
    (fun items => fromEntriesFast items.val)
    (by intro fields; simpa using fromEntries_entries fields)
    (by
      intro items
      apply Subtype.ext
      simpa using entries_fromEntries_of_canonical items.val items.property)

theorem mapStream_encode [LinearOrder K] [∀ key, DecidableEq (V key)]
    (keyStream : StreamCodec K) (valueStream : (key : K) → StreamCodec (V key))
    (fields : Π₀ key : K, V key) :
    (mapStream keyStream valueStream).encode fields =
      (StreamCodec.list (entryStream keyStream valueStream)).encode (entries fields) :=
  rfl

end Minidregg.Compiler.FiniteDependentMapCodec
