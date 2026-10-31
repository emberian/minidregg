/- Lossless cached comparator keys: canonical address bytes are computed once
per inserted coordinate and once per lookup, rather than at every tree edge.
The dependent value remains indexed by the original typed address. -/
module

public import Compiler.FiniteDependentMapCodec
public import Mathlib.Data.Finset.Sort

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

namespace Minidregg.Compiler.FiniteDependentMapCachedOrdering

set_option autoImplicit false

/-- A one-pass Boolean decision of `<` on comparator keys: what the cached
order runs instead of the key type's generic `Decidable (a < b)`. -/
class FastKeyOrder (O : Type) [LinearOrder O] where
  ltb : O → O → Bool
  ltb_iff : ∀ a b, ltb a b = true ↔ a < b

/-- Strict lexicographic order on byte keys, one tight pass. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then lexLt as bs else false

theorem lexLt_iff : ∀ (a b : List Nat), lexLt a b = true ↔ a < b
  | [], [] => by simp [lexLt]
  | [], _ :: _ => by simp [lexLt, List.nil_lt_cons]
  | _ :: _, [] => by simp [lexLt, List.not_lt_nil]
  | a :: as, b :: bs => by
      rw [List.cons_lt_cons_iff, ← lexLt_iff as bs]
      show (if a < b then true else if a = b then lexLt as bs else false) = true ↔ _
      by_cases h : a < b
      · simp [h]
      · by_cases e : a = b
        · subst e; simp
        · simp [h, e]

/-- Any key order decides `<` by its own instance; byte keys override it below. -/
instance (priority := low) {O : Type} [LinearOrder O] : FastKeyOrder O :=
  ⟨fun a b => decide (a < b), fun _ _ => decide_eq_true_iff⟩

instance : FastKeyOrder (List Nat) := ⟨lexLt, lexLt_iff⟩

/-- `LinearOrder.lift'` along an injective key, deciding only on keys: `<` is one
`FastKeyOrder.ltb` pass, `≤` its flip negated, `=` the keys' equality; never
the source type's own equality, never `≤` both ways, never the generic boxed
`List.Lex` decision. Same `≤` and `<` as `LinearOrder.lift'`. -/
@[reducible] def FastKeyOrder.lift {α O : Type} [LinearOrder O] [FastKeyOrder O] (f : α → O)
    (inj : Function.Injective f) : LinearOrder α where
  le left right := f left ≤ f right
  lt left right := f left < f right
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ below above := inj (le_antisymm below above)
  le_total _ _ := le_total _ _
  toDecidableLE left right :=
    decidable_of_iff (FastKeyOrder.ltb (f right) (f left) = false)
      (by rw [← Bool.not_eq_true, FastKeyOrder.ltb_iff]; exact not_lt)
  toDecidableEq left right := decidable_of_iff (f left = f right) inj.eq_iff
  toDecidableLT left right :=
    decidable_of_iff (FastKeyOrder.ltb (f left) (f right) = true) (FastKeyOrder.ltb_iff _ _)

variable {K O : Type} (keyOf : K → O)

structure CachedKey where
  value : K
  orderKey : O
  bound : orderKey = keyOf value

def cache (value : K) : CachedKey keyOf := ⟨value, keyOf value, rfl⟩

theorem value_injective : Function.Injective (CachedKey.value (keyOf := keyOf)) := by
  rintro ⟨left, leftKey, leftExact⟩ ⟨right, rightKey, rightExact⟩ same
  cases same
  have keys : leftKey = rightKey := leftExact.trans rightExact.symm
  cases keys
  rfl

theorem cache_injective : Function.Injective (cache keyOf) := by
  intro left right same
  exact congrArg CachedKey.value same

theorem orderKey_injective (keyExact : Function.Injective keyOf) :
    Function.Injective (CachedKey.orderKey (keyOf := keyOf)) := by
  intro left right same
  apply value_injective keyOf
  apply keyExact
  exact left.bound.symm.trans (same.trans right.bound)

/-- The byte order on cached keys: `FastKeyOrder.lift` of the cached key. -/
@[reducible] def cachedOrder [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf) :
    LinearOrder (CachedKey keyOf) :=
  FastKeyOrder.lift CachedKey.orderKey (orderKey_injective keyOf keyExact)

variable [DecidableEq K] {V : K → Type} [∀ key, Zero (V key)]

/-- Sort using cached canonical keys without changing the original key list.
`Finset.map` needs no duplicate scan because the decoration is injective. -/
def sortedFinsetCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (keys : Finset K) : List K :=
  letI := cachedOrder keyOf keyExact
  ((keys.map ⟨cache keyOf, cache_injective keyOf⟩).sort (· ≤ ·)).map CachedKey.value

theorem sortedFinsetCached_eq [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (keys : Finset K) :
    sortedFinsetCached keyOf keyExact keys =
      (letI := FastKeyOrder.lift keyOf keyExact; keys.sort (· ≤ ·)) := by
  letI := FastKeyOrder.lift keyOf keyExact
  letI := cachedOrder keyOf keyExact
  have mapped := Finset.map_sort ⟨cache keyOf, cache_injective keyOf⟩ keys
    (· ≤ ·) (· ≤ ·) (fun _ _ _ _ => Iff.rfl)
  unfold sortedFinsetCached
  rw [← mapped]
  simp [List.map_map, Function.comp_def, cache]

private instance orderedTransCmp [LinearOrder K] :
    Std.TransCmp (fun a b : K => compareOfLessAndEq a b) :=
  Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    le_antisymm le_trans le_total not_le

private instance orderedEqCmp [LinearOrder K] :
    Std.LawfulEqCmp (fun a b : K => compareOfLessAndEq a b) where
  compare_self := by simp [compareOfLessAndEq]
  eq_of_compare := (compareOfLessAndEq_eq_eq le_refl not_le).mp

/-- Deduplicate with tree comparisons, retaining the tree's proved unique keys
instead of running the quadratic typed-key list dedup in `Multiset.toFinset`. -/
private def keyTree [LinearOrder K] : List K →
    Std.DTreeMap K (fun _ => Unit) (fun a b => compareOfLessAndEq a b)
  | [] => ∅
  | head :: rest => (keyTree rest).insert head ()

private theorem mem_keyTree [LinearOrder K] (keys : List K) (key : K) :
    key ∈ keyTree keys ↔ key ∈ keys := by
  induction keys with
  | nil => simp [keyTree]
  | cons head rest ih =>
      rw [keyTree, Std.DTreeMap.mem_insert, ih]
      simp [compareOfLessAndEq_eq_eq le_refl not_le, eq_comm]

def uniqueKeysCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (keys : List K) : Finset K :=
  letI := cachedOrder keyOf keyExact
  let tree := keyTree (keys.map (cache keyOf))
  let unique : Finset (CachedKey keyOf) := ⟨tree.keys, tree.nodup_keys⟩
  unique.map ⟨CachedKey.value, value_injective keyOf⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem mem_uniqueKeysCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (keys : List K) (key : K) :
    key ∈ uniqueKeysCached keyOf keyExact keys ↔ key ∈ keys := by
  letI := cachedOrder keyOf keyExact
  simp only [uniqueKeysCached, Finset.mem_map, Finset.mem_mk, Multiset.mem_coe,
    Std.DTreeMap.mem_keys, mem_keyTree, List.mem_map]
  constructor
  · rintro ⟨cached, ⟨original, member, rfl⟩, same⟩
    simpa [cache] using same ▸ member
  · intro member
    exact ⟨cache keyOf key, ⟨key, member, rfl⟩, rfl⟩

def uniqueMultisetCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (keys : Multiset K) : Finset K :=
  Quotient.lift (uniqueKeysCached keyOf keyExact)
    (by
      intro left right same
      ext key
      simp only [mem_uniqueKeysCached]
      exact same.mem_iff) keys

@[simp] theorem mem_uniqueMultisetCached [LinearOrder O] [FastKeyOrder O]
    (keyExact : Function.Injective keyOf) (keys : Multiset K) (key : K) :
    key ∈ uniqueMultisetCached keyOf keyExact keys ↔ key ∈ keys := by
  refine Quotient.inductionOn keys ?_
  intro values
  exact mem_uniqueKeysCached keyOf keyExact values key

def supportCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    [∀ key, DecidableEq (V key)] (fields : Π₀ key : K, V key) : Finset K :=
  fields.support'.lift (fun support =>
    (uniqueMultisetCached keyOf keyExact support.1).filter (fun key => fields key ≠ 0))
    (by
      intro left right
      ext key
      simp only [Finset.mem_filter, mem_uniqueMultisetCached]
      constructor
      · rintro ⟨_, nonzero⟩
        exact ⟨(right.2 key).resolve_right nonzero, nonzero⟩
      · rintro ⟨_, nonzero⟩
        exact ⟨(left.2 key).resolve_right nonzero, nonzero⟩)

@[simp] theorem supportCached_eq [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    [∀ key, DecidableEq (V key)] (fields : Π₀ key : K, V key) :
    supportCached keyOf keyExact fields = fields.support := by
  unfold supportCached DFinsupp.support
  refine Trunc.induction_on fields.support' ?_
  intro support
  change (uniqueMultisetCached keyOf keyExact support.1).filter (fun key => fields key ≠ 0) =
    support.1.toFinset.filter (fun key => fields key ≠ 0)
  ext key
  simp

def cachedEntries (items : List (Sigma V)) :
    List (Sigma (fun cached : CachedKey keyOf => V cached.value)) :=
  items.map fun item => ⟨cache keyOf item.1, item.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- For any decision of cached-key equality (they all agree). -/
theorem fromEntries_cached_apply [DecidableEq (CachedKey keyOf)] (items : List (Sigma V)) (key : K) :
    FiniteDependentMapCodec.fromEntries (cachedEntries keyOf items) (cache keyOf key) =
      FiniteDependentMapCodec.fromEntries items key := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨head, value⟩
      by_cases same : key = head
      · subst key
        simp [cachedEntries, FiniteDependentMapCodec.fromEntries, DFinsupp.update]
      · have different : cache keyOf key ≠ cache keyOf head := by
          intro equal
          exact same (cache_injective keyOf equal)
        simp [cachedEntries, FiniteDependentMapCodec.fromEntries, DFinsupp.update,
          Function.update_of_ne same, Function.update_of_ne different]
        exact ih

theorem fromEntries_zero_of_absent (items : List (Sigma V)) (key : K)
    (absent : key ∉ items.map Sigma.fst) :
    FiniteDependentMapCodec.fromEntries items key = 0 := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨head, value⟩
      have different : key ≠ head := by intro same; exact absent (by simp [same])
      have tail : key ∉ rest.map Sigma.fst := by intro member; exact absent (by simp [member])
      simpa [FiniteDependentMapCodec.fromEntries, DFinsupp.update, different] using ih tail

/-- The support witness carries original typed addresses; the tree carries
only a lossless decoration of each key. Duplicate/zero/first-wins behavior is
the original function, and canonical acceptance is unchanged. -/
def fromEntriesCached [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (items : List (Sigma V)) : (Π₀ key : K, V key) :=
  letI := cachedOrder keyOf keyExact
  let fields := FiniteDependentMapCodec.fromEntriesFast (cachedEntries keyOf items)
  DFinsupp.mk' (fun key => fields (cache keyOf key)) (fields.support'.map fun support =>
    ⟨support.1.map CachedKey.value, by
      intro key
      rcases support.2 (cache keyOf key) with present | zero
      · exact Or.inl (Multiset.mem_map.mpr ⟨cache keyOf key, present, rfl⟩)
      · exact Or.inr zero⟩)

@[simp] theorem fromEntriesCached_eq [LinearOrder O] [FastKeyOrder O] (keyExact : Function.Injective keyOf)
    (items : List (Sigma V)) :
    fromEntriesCached keyOf keyExact items = FiniteDependentMapCodec.fromEntries items := by
  letI := cachedOrder keyOf keyExact
  apply DFinsupp.ext
  intro key
  change FiniteDependentMapCodec.fromEntriesFast (cachedEntries keyOf items) (cache keyOf key) = _
  rw [FiniteDependentMapCodec.fromEntriesFast_eq, fromEntries_cached_apply]

end Minidregg.Compiler.FiniteDependentMapCachedOrdering

/-- info: 'Minidregg.Compiler.FiniteDependentMapCachedOrdering.fromEntriesCached_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.FiniteDependentMapCachedOrdering.fromEntriesCached_eq
/-- info: 'Minidregg.Compiler.FiniteDependentMapCachedOrdering.sortedFinsetCached_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.FiniteDependentMapCachedOrdering.sortedFinsetCached_eq
/-- info: 'Minidregg.Compiler.FiniteDependentMapCachedOrdering.supportCached_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.FiniteDependentMapCachedOrdering.supportCached_eq
