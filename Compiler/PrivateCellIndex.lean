/-
# Compiler.PrivateCellIndex — a blinded cell's store as private trie entries (statements)

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

**The blinding stays out.** The wire's reserved blinding address
(`Wire.blinding`) keys every salt of the flat format and is custody, never
data: the index omits it (`IndexExact`'s blinding clause). The masked
commitment's mask is held separately (`Kernel.BlindedCellHiding.maskedTrieCommitment`).

Statements:
* `IndexExact`: the index's last value at every address is the store's value
  bytes there, and nothing at the blinding address.
* `IndexBindsData`: two stores of one wire with the same index agree at every
  non-blinding address. Teeth: two stores differing only in their blinding value
  have the same index, so the index alone does not bind the blinding (by design:
  custody); stores differing at a data address have different indexes.
-/
module

public import Compiler.StoreCodec
public import Theory.AuthTrieCache

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

end Minidregg.Compiler.PrivateCellIndex
