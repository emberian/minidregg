/-
# Compiler.PrivateCellIndex — a blinded cell's store as private trie entries

Owed item 1 of docs/PRIVATE-CELLS-STATE.md: the adapter from a cell's `Store` to
the `Theory.AuthTrie` entries of its private index.

**Semantics, decided by what the store means.** A `Store` is a finite map
(`Theory.Store.Store`, a `DFinsupp`): it has no insertion history and no
duplicate addresses, so "first value" versus "last value" is not a property of
the store at all. It arises only for entry LISTS: `StoreCodec.fromEntries` is
first-wins on an arbitrary list, `AuthTrie.lastVal` is last-wins. The adapter
reads the store's canonical entries (`StoreCodec.entries`), whose addresses are
distinct (`entries_keys`, `sortedSupport` is a sorted support), so the two
conventions agree on everything the adapter produces. The index is therefore
defined over canonical entries only, and the trie's last-wins is the operational
convention for its updates (an insert overwrites).

**The blinding stays out.** The index omits the wire's reserved blinding
address (`Wire.blinding`), which keys every salt of the flat format
(`IndexExact`'s blinding clause). Nothing here makes that address custody: an
arbitrary `Wire` may name a readable data address. The Kernel instantiation
owes that the wire's exclusion is `CanonicalCellRegistry.isBlinding`, so the
index agrees with `Visible` under full scope. Nor does anything here require a
blinding entry to exist; mask custody is admission's. The masked
commitment's mask is held separately (`Kernel.BlindedCellHiding.maskedTrieCommitment`).

Statements:
* `IndexExact`: the index's last value at every address is the store's value
  bytes there, and nothing at the blinding address.
* `IndexBindsData`: two stores of one wire with the same index agree at every
  non-blinding address.
* `IndexIgnoresBlinding`, its converse: stores agreeing off the blinding address
  have the same index (invariance under changes at that one address, not a
  secrecy claim). With `IndexBindsData` it pins the index's
  dependence exactly: an adapter leaking the blinding fails the converse, one
  dropping data fails `IndexBindsData`.

These bind the canonical entry LIST at one fixed wire; root binding composes
them with trie binding and the path invariant, and cross-wire binding is the
outer context's `layoutDigest W`.
-/
module

public import Compiler.StoreCodec
public import Theory.AuthTrieCache
public import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Compiler.PrivateCellIndex

set_option autoImplicit false

open Minidregg.Theory.Store
open Minidregg.Compiler.StoreCodec

variable {L : Layout.{0, 0, 0}} (W : Wire L)

/-- The bytes of a value at an address (its namespace's value codec). -/
def valueBytes (address : Address L) (value : L.Value address.1) : List UInt8 :=
  (W.valueStream address.1).encode value

/-- The private index's entries of a store: every canonical entry except the
blinding one, keyed by its address, valued by its value bytes. -/
def indexEntries (store : Store L) : List (Address L × List UInt8) :=
  ((entries W store).filter fun entry => decide (some entry.1 ≠ W.blinding)).map
    fun entry => (entry.1, valueBytes W entry.1 entry.2)

/-- **Adapter exactness (statement).** -/
def IndexExact : Prop :=
  ∀ (store : Store L) (address : Address L),
    Minidregg.Theory.AuthTrie.lastVal (indexEntries W store) address =
      if some address = W.blinding then none
      else (store address).map (valueBytes W address)

/-- **The index binds the data (statement).** -/
def IndexBindsData : Prop :=
  ∀ (left right : Store L), indexEntries W left = indexEntries W right →
    ∀ address, some address ≠ W.blinding → left address = right address

/-- **The index carries nothing of the blinding (statement).** -/
def IndexIgnoresBlinding : Prop :=
  ∀ (left right : Store L), (∀ address, some address ≠ W.blinding → left address = right address) →
    indexEntries W left = indexEntries W right

/-! ### Proofs -/

open Minidregg.Theory.AuthTrie (lastVal lastVal_cons lastVal_isSome)

theorem lastVal_eq_none_of_forall {K V : Type} [DecidableEq K] {es : List (K × V)} {k : K}
    (absent : ∀ e ∈ es, e.1 ≠ k) : lastVal es k = none :=
  Option.not_isSome_iff_eq_none.mp fun present => by
    obtain ⟨e, member, same⟩ := lastVal_isSome.mp present
    exact absent e member same

theorem lastVal_eq_some_of_nodup {K V : Type} [DecidableEq K] :
    ∀ {es : List (K × V)} {k : K} {v : V}, (es.map Prod.fst).Nodup → (k, v) ∈ es →
      lastVal es k = some v
  | [], _, _, _, member => by cases member
  | e :: es, k, v, distinct, member => by
      rw [lastVal_cons]
      rw [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        have absent : lastVal es k = none := lastVal_eq_none_of_forall fun f member same =>
          distinct.1 (by simpa [same] using List.mem_map_of_mem (f := Prod.fst) member)
        simp [absent]
      · rw [lastVal_eq_some_of_nodup distinct.2 inRest]
        rfl

theorem mem_entries {store : Store L} {entry : Entry L} :
    entry ∈ entries W store ↔ store entry.1 = some entry.2 := by
  unfold entries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨address, -, found⟩
    cases present : store address with
    | none => simp [present] at found
    | some value =>
        simp only [present, Option.map_some] at found
        obtain rfl := Option.some.inj found
        exact present
  · intro found
    refine ⟨entry.1, (mem_sortedSupport W store entry.1).mpr (by simp [found]), ?_⟩
    rw [found]
    rfl

theorem entries_keys_nodup (store : Store L) : ((entries W store).map Sigma.fst).Nodup := by
  rw [entries_keys, sortedSupport_eq]
  let _ := addressOrder W
  exact Finset.sort_nodup _ _

theorem indexEntries_keys_nodup (store : Store L) :
    ((indexEntries W store).map Prod.fst).Nodup := by
  unfold indexEntries
  rw [List.map_map]
  exact List.Nodup.sublist (List.filter_sublist.map Sigma.fst) (entries_keys_nodup W store)

theorem indexExact : IndexExact W := by
  intro store address
  split_ifs with blind
  · apply lastVal_eq_none_of_forall
    intro pair member same
    unfold indexEntries at member
    obtain ⟨entry, kept, rfl⟩ := List.mem_map.mp member
    rw [List.mem_filter, decide_eq_true_eq] at kept
    subst same
    exact kept.2 blind
  · cases found : store address with
    | none =>
        apply lastVal_eq_none_of_forall
        intro pair member same
        unfold indexEntries at member
        obtain ⟨entry, kept, rfl⟩ := List.mem_map.mp member
        rw [List.mem_filter, mem_entries] at kept
        subst same
        simp [found] at kept
    | some value =>
        simp only [Option.map_some]
        apply lastVal_eq_some_of_nodup (indexEntries_keys_nodup W store)
        unfold indexEntries
        exact List.mem_map.mpr ⟨⟨address, value⟩,
          List.mem_filter.mpr ⟨(mem_entries W).mpr found, by simpa using blind⟩, rfl⟩

theorem indexBindsData : IndexBindsData W := by
  intro left right same address off
  have onLeft := indexExact W left address
  have onRight := indexExact W right address
  rw [same] at onLeft
  simp only [off, ↓reduceIte] at onLeft onRight
  exact Option.map_injective (streamEncode_injective _) (onLeft.symm.trans onRight)

theorem indexIgnoresBlinding : IndexIgnoresBlinding W := by
  intro left right agree
  unfold indexEntries
  congr 1
  have nodupOf : ∀ store : Store L,
      ((entries W store).filter fun entry => decide (some entry.1 ≠ W.blinding)).Nodup :=
    fun store => (List.Nodup.sublist (List.filter_sublist.map Sigma.fst)
      (entries_keys_nodup W store)).of_map _
  refine List.Perm.eq_of_pairwise ?_ (List.Pairwise.sublist List.filter_sublist (entries_pairwise W left))
    (List.Pairwise.sublist List.filter_sublist (entries_pairwise W right))
    ((List.perm_ext_iff_of_nodup (nodupOf left) (nodupOf right)).mpr ?_)
  · intro a b _ _ first second
    exact (lt_asymm first second).elim
  · intro entry
    simp only [List.mem_filter, mem_entries, decide_eq_true_eq]
    constructor
    · rintro ⟨found, off⟩
      exact ⟨by rw [← agree entry.1 off]; exact found, off⟩
    · rintro ⟨found, off⟩
      exact ⟨by rw [agree entry.1 off]; exact found, off⟩

#assert_axioms indexExact
#assert_axioms indexBindsData
#assert_axioms indexIgnoresBlinding

end Minidregg.Compiler.PrivateCellIndex
