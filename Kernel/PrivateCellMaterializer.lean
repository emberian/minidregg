/-
# Kernel.PrivateCellMaterializer -- the private kinds' persistent structure

The private cell kinds' instance of `Theory.CellStateAux.AuxCache` (root's KeptCell ruling,
option (b)). The specification is a function of the store alone: `privateRoot wire ctx`, with
`ctx` the kind-level context (protocol, layout, size bound) and the per-cell, per-version
separation carried by the blinding value, which the receiver writes as one custody operation
of each accepted patch (an injective encoding of cell id, version and mask; the encoding and
the composite-patch restatement of `accept` are the next statement).

The structure is total, the gate (`FitStore`) and custody stay outside it:
* `Kept`: the private index and the held blinding bytes.
* `aux`: `Holds` is "the index holds the store's index entries and the bytes are its blinding
  bytes"; `build` is one bulk build; `set` at the blinding address replaces the held bytes and
  leaves the index (`indexIgnoresBlinding`), at any other address is one index walk
  (`indexStep`: an insert or an erase); `root?` is always the outer hash of the held bytes and the
  kept digest.
* `keptBuild`: one bulk build over the key-distinct index entries (`Cache.buildNodup`, no
  canonicalization). It runs per materialization from bytes (each decode on open).
* `rootAvailable`: the read is present at every store, so `rootOr` never forces the bytes.
* `set_cost`: a removal is the erase walk whose interpreter count is `erase_cost`'s; an insert's
  metering is owed with the insert as a heap program.
-/
module

public import Kernel.PrivateCellReceiver
public import Theory.CellStateAux
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.PrivateCellMaterializer

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PrivateCellReceiver
open Minidregg.Compiler.PrivateCellIndex (indexEntries indexIgnoresBlinding)

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- The blinding bytes after a write at the blinding address. -/
def maskAfter (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) : List UInt8 :=
  (v.map (wire.valueStream a.1).encode).getD []

theorem maskOf_set_blind {store : Store (CanonicalCellRegistry.layout kind)}
    {a : Address (CanonicalCellRegistry.layout kind)} (blind : some a = wire.blinding)
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    maskOf wire (store.set a v) = maskAfter wire a v := by
  unfold maskOf StoreCodec.blindingKey maskAfter
  rw [← blind]
  simp [Store.set]

theorem index_set_blind {store : Store (CanonicalCellRegistry.layout kind)}
    {a : Address (CanonicalCellRegistry.layout kind)} (blind : some a = wire.blinding)
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    indexEntries wire (store.set a v) = indexEntries wire store :=
  indexIgnoresBlinding wire _ _ fun address other => by
    have : address ≠ a := fun same => other (same ▸ blind)
    simp [Store.set, Function.update_of_ne this]

/-- What a private cell carries: its index and its held blinding bytes. -/
structure Kept where
  index : Index wire
  mask : List UInt8

/-- The relation: the index holds the store's index entries, the bytes are its blinding bytes. -/
def KeptHolds (kept : Kept wire) (store : Store (CanonicalCellRegistry.layout kind)) : Prop :=
  kept.index.Holds (indexEntries wire store) ∧ kept.mask = maskOf wire store

/-- One write on the carried structure: the blinding bytes, or one index walk. -/
def keptSet (kept : Kept wire) (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) : Kept wire :=
  if some a = wire.blinding then ⟨kept.index, maskAfter wire a v⟩ else ⟨KeptCell.indexStep (wire := wire) kept.index a v, kept.mask⟩

theorem keptSet_holds {kept : Kept wire} {store : Store (CanonicalCellRegistry.layout kind)}
    (a : Address (CanonicalCellRegistry.layout kind)) (v : Option ((CanonicalCellRegistry.layout kind).Value a.1))
    (h : KeptHolds wire kept store) : KeptHolds wire (keptSet wire kept a v) (store.set a v) := by
  unfold keptSet
  by_cases blind : some a = wire.blinding
  · simp only [blind, if_true]
    exact ⟨(index_set_blind wire blind v).symm ▸ h.1, (maskOf_set_blind wire blind v).symm⟩
  · simp only [blind, if_false]
    refine ⟨?_, h.2.trans (maskOf_set_other wire blind v).symm⟩
    cases v with
    | some x =>
        exact (Theory.AuthTrie.Cache.insert_holds (bits_length wire) h.1 a _).congr fun k =>
          (lastVal_index_set_some wire store blind x k).symm
    | none =>
        exact (Theory.AuthTrie.Cache.erase_holds h.1 a).congr fun k =>
          (lastVal_index_set_none wire store blind k).symm

section Aux

variable (ctx : List UInt8)
  (codec : Minidregg.Theory.IndexedProgram.LawfulCodec (Store (CanonicalCellRegistry.layout kind)))
  (rootBytes : List UInt8 → Digest) (agree : ∀ store, rootBytes (codec.encode store) = privateRoot wire ctx store)

/-- The one bulk build, at birth or on open: the index entries are key-distinct, so no
canonicalization pass (`Cache.buildNodup`, linear in the entries). -/
def keptBuild (store : Store (CanonicalCellRegistry.layout kind)) : {kept : Kept wire // KeptHolds wire kept store} :=
  ⟨⟨Theory.AuthTrie.Cache.buildNodup (bits_length wire) (indexEntries wire store)
      (Compiler.PrivateCellIndex.indexEntries_keys_nodup wire store), maskOf wire store⟩,
    Theory.AuthTrie.Cache.buildNodup_holds (bits_length wire) _
      (Compiler.PrivateCellIndex.indexEntries_keys_nodup wire store), rfl⟩

/-- The read: the outer hash of the held bytes and the kept digest. -/
def keptRoot (kept : Kept wire) : Digest := outerRoot ctx kept.mask kept.index.digest

theorem keptRoot_eq {kept : Kept wire} {store : Store (CanonicalCellRegistry.layout kind)}
    (h : KeptHolds wire kept store) : keptRoot wire ctx kept = privateRoot wire ctx store := by
  unfold keptRoot privateRoot
  rw [BlindedCellHiding.maskedTrieCommitment, Theory.AuthTrie.Cache.digest_eq h.1, h.2]

/-- **The private kinds' persistent structure**, over any root bytes that read the private root
of the store at kind-level context `ctx`. -/
def aux : Theory.CellStateAux.AuxCache (fun store => rootBytes (codec.encode store)) where
  Aux := Kept wire
  Holds := KeptHolds wire
  build := keptBuild wire
  set := keptSet wire
  set_holds := fun a v h => keptSet_holds wire a v h
  root? kept := some (keptRoot wire ctx kept)
  root?_sound := fun h read => by
    cases Option.some.inj read
    exact (keptRoot_eq wire ctx h).trans (agree _).symm
  root?_agree := fun ha hb => by
    show some _ = some _
    rw [keptRoot_eq wire ctx ha, keptRoot_eq wire ctx hb]

end Aux

/-- **The fast path at every store**: the read is always present, so a private cell's root is
the outer hash of its carried bytes and kept digest, and its bytes are never encoded for it. -/
theorem rootAvailable (ctx : List UInt8)
    (codec : Minidregg.Theory.IndexedProgram.LawfulCodec (Store (CanonicalCellRegistry.layout kind)))
    (rootBytes : List UInt8 → Digest) (agree : ∀ store, rootBytes (codec.encode store) = privateRoot wire ctx store)
    (Admitted : Store (CanonicalCellRegistry.layout kind) → Prop) :
    Theory.CellStateAux.RootAvailable (aux wire ctx codec rootBytes agree) Admitted :=
  fun _ _ => rfl

/-- **Per write, no rebuild**: a write at a data address is exactly one index walk on the
carried index (`indexStep`: one insert or one erase), a write at the blinding address leaves
the index; neither reads the store. The erase walk's interpreter count is
`Theory.PrivateCellTrie.erase_cost`'s; the insert's is owed with the insert as a heap program. -/
theorem set_index (ctx : List UInt8)
    (codec : Minidregg.Theory.IndexedProgram.LawfulCodec (Store (CanonicalCellRegistry.layout kind)))
    (rootBytes : List UInt8 → Digest) (agree : ∀ store, rootBytes (codec.encode store) = privateRoot wire ctx store)
    (kept : Kept wire) (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    ((aux wire ctx codec rootBytes agree).set kept a v).index =
      if some a = wire.blinding then kept.index else KeptCell.indexStep (wire := wire) kept.index a v := by
  show (keptSet wire kept a v).index = _
  unfold keptSet
  by_cases blind : some a = wire.blinding <;> simp [blind]

#assert_axioms keptSet_holds
#assert_axioms keptRoot_eq
#assert_axioms rootAvailable
#assert_axioms set_index

end Minidregg.Kernel.PrivateCellMaterializer
