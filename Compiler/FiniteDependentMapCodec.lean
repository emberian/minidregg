/-
# Compiler.FiniteDependentMapCodec -- one finite sparse encoding construction

Finite support is structural `DFinsupp` data. Keys are canonically sorted and
each dependent value is read at its actual key. The decoder reconstructs that
same finite map; there is no countability-selected enumeration or focused
codec. A carrier's outer canonical decoder additionally rejects duplicate,
out-of-order and explicit-zero entries by exact re-encoding.
-/
import Compiler.Tower256ConcreteBackend
import Mathlib.Data.Finset.Sort
import Std.Data.DTreeMap.Lemmas

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

def stream [LinearOrder K] [∀ key, DecidableEq (V key)]
    (keyStream : StreamCodec K)
    (valueStream : (key : K) → StreamCodec (V key)) :
    StreamCodec (Π₀ key : K, V key) :=
  StreamCodec.xmap (StreamCodec.list (entryStream keyStream valueStream))
    entries fromEntriesFast (by intro fields; simpa using fromEntries_entries fields)


/-- The complete stream codec is unchanged extensionally, including lax decoding. -/
theorem stream_eq [LinearOrder K] [∀ key, DecidableEq (V key)]
    (keyStream : StreamCodec K)
    (valueStream : (key : K) → StreamCodec (V key)) :
    stream keyStream valueStream =
      StreamCodec.xmap (StreamCodec.list (entryStream keyStream valueStream))
        entries fromEntries fromEntries_entries := by
  have same : (fromEntriesFast : List (Sigma V) → (Π₀ key : K, V key)) = fromEntries :=
    funext fromEntriesFast_eq
  simp only [stream, same]

end Minidregg.Compiler.FiniteDependentMapCodec
