/-
# Kernel.PrivateCellReceiver — the private cell's receiving state machine

The receiver of docs/PRIVATE-CELLS-STATE.md, in Lean: a blinded cell's store
held beside its kept private index (`Theory.AuthTrie.Cache` over
`Compiler.PrivateCellIndex.indexEntries`, keyed by `Kernel.PrivateCellView`'s
deployed key paths and node digest), its mask, its accepted version, and the
outer commitment over the context, the mask and the index digest.

* `KeptCell`: a gated store (`FitStore`: every live address passes
  `addressFits 256`), its kept index with the proof it holds the store's
  entries, the mask bytes held directly (`mask_eq`: the store's blinding value's
  bytes), the cell's fixed parameters and its accepted version. Every
  constructor goes through the gate.
* `birth`: the whole store through `admit`, the first mask set at the
  blinding address, one bulk build of the index (linear in the store, once).
* `write`: one data address. The blinding address is refused (the mask moves
  only by `accept`); a key failing `addressFits` is refused, never left out of
  the index; a value is one `Cache.insert` walk, a removal one `Cache.erase`
  walk (metered at `7 L + 3` interpreter operations, `L = 516`, on injective
  live paths: a path collision is a cSHAKE256 collision among live addresses,
  `viewOpeningExact_deployed`).
* `accept`: one accepted version, atomically: the patch's writes, then the
  supplied mask at the blinding address and the version advanced, for a no-op
  patch too. The mask's freshness and secrecy are the host's custody obligation
  (independent randomness, or a PRF under an independent key); this module
  takes it as an argument.
* `root` / `root_eq`: the outer commitment from the kept digest and the held
  mask, under the context derived from the cell's state (`ctxOf`: protocol,
  cell, layout, accepted version, size bound), equals `privateRoot`, the
  specification over the whole store.

Owed: the insert walk metered (it backs the world root's hot path, so as a
proved `@[csimp]` equality to the oracle walk, not a rewrite); a cell
representation carrying `KeptCell` so `Materialized.rootCache` is `KeptCell.root`
(`rootExact` by `root_eq`) and patch application does not rematerialize; the
registry and native-host switch (a root-format change: fresh genesis, fixture
re-record, codec epoch agreed with the hot-path lane); retention of accepted
versions for retries.
-/
module

public import Kernel.PrivateCellView

@[expose] public section

namespace Minidregg.Kernel.PrivateCellReceiver

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PrivateCellScope (addressFits)
open Minidregg.Kernel.PrivateCellView
open Minidregg.Theory.AuthTrie (NodeIn root lastVal lastVal_snoc)
open Minidregg.Theory.AuthTrie.Cache (Holds)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes indexExact indexIgnoresBlinding)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec digestStream)

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- The deployed key path of a private index. -/
def bits : Address (CanonicalCellRegistry.layout kind) → List Bool := keyBits (hashedAddrBits wire 256 addressHash)

theorem bits_length (a : Address (CanonicalCellRegistry.layout kind)) : (bits wire a).length = 516 :=
  keyBits_length (hashedAddrBits_length wire 256 addressHash) a

/-- The kept private index of a cell. -/
abbrev Index := Theory.AuthTrie.Cache (deployedDig wire) (bits wire) 516

def outerCustomization : List UInt8 := "DREGG/PRIVATE-CELL/OUTER/v1".toUTF8.toList

/-- The outer commitment: cSHAKE256 over the context, the mask and the index digest. -/
def outerRoot (ctx mask : List UInt8) (inner : Digest) : Digest :=
  (Sp800185Cshake256.hash outerCustomization
    ((StreamCodec.product (StreamCodec.list StreamCodec.byte)
      (StreamCodec.product (StreamCodec.list StreamCodec.byte) digestStream)).encode (ctx, mask, inner))).digest

/-- The cell's fixed parameters: protocol version, cell identity, layout digest
bytes, public size bound, and the wire's blinding address. -/
structure Params where
  protocol : Nat
  cell : List UInt8
  layout : List UInt8
  sizeBound : Nat
  blinding : StoreCodec.Blinding wire

/-- The context of one accepted version. -/
def ctxBytes (params : Params wire) (version : Nat) : List UInt8 :=
  (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.list StreamCodec.byte)
    (StreamCodec.product (StreamCodec.list StreamCodec.byte) (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
    (params.protocol, params.cell, params.layout, version, params.sizeBound)

/-- The cell's mask: its blinding value's bytes (none: the empty mask). -/
def maskOf (store : Store (CanonicalCellRegistry.layout kind)) : List UInt8 :=
  (StoreCodec.blindingKey wire store).getD []

/-- **The private root (specification)**: the outer commitment over the mask and
the canonical root of the store's index, computed from the whole store. -/
def privateRoot (ctx : List UInt8) (store : Store (CanonicalCellRegistry.layout kind)) : Digest :=
  outerRoot ctx (maskOf wire store) (root (deployedDig wire) (bits wire) 516 (indexEntries wire store))

/-- A gated store with its kept index, mask, parameters and accepted version. -/
structure KeptCell where
  params : Params wire
  version : Nat
  fit : FitStore wire
  index : Index wire
  holds : index.Holds (indexEntries wire fit.store)
  mask : List UInt8
  mask_eq : maskOf wire fit.store = mask

namespace KeptCell

variable {wire}

/-- The context of the cell's current accepted version. -/
def ctx (cell : KeptCell wire) : List UInt8 := ctxBytes wire cell.params cell.version

/-- The root from the kept digest and the held mask: no rebuild, no store lookup. -/
def root (cell : KeptCell wire) : Digest := outerRoot cell.ctx cell.mask cell.index.digest

/-- **The kept root is the private root** under the cell's own context. -/
theorem root_eq (cell : KeptCell wire) : cell.root = privateRoot wire cell.ctx cell.fit.store := by
  rw [root, privateRoot, Theory.AuthTrie.Cache.digest_eq cell.holds, cell.mask_eq]

end KeptCell

/-- The gate holds of every store whose live addresses all pass. -/
theorem storeFits_of_forall {store : Store (CanonicalCellRegistry.layout kind)}
    (all : ∀ a, store a ≠ none → addressFits 256 kind a = true) : storeFits wire store = true := by
  refine List.all_eq_true.mpr fun entry member => all entry.1 ?_
  have : entry.1 ∈ (StoreCodec.entries wire store).map Sigma.fst := List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [StoreCodec.entries_keys] at this
  exact (StoreCodec.mem_sortedSupport wire store entry.1).mp this

/-- Writing a fitting address keeps the gate. -/
theorem storeFits_set {store : Store (CanonicalCellRegistry.layout kind)} (gate : storeFits wire store = true)
    {a : Address (CanonicalCellRegistry.layout kind)} (fits : addressFits 256 kind a = true)
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) : storeFits wire (store.set a v) = true := by
  refine storeFits_of_forall wire fun b live => ?_
  by_cases same : b = a
  · subst same; exact fits
  · rw [Store.set_ne store a v b same] at live
    exact admitted_of_storeFits gate b live

/-- The index after setting a non-blinding address: the old entries, then the new one. -/
theorem lastVal_index_set_some (store : Store (CanonicalCellRegistry.layout kind))
    {a : Address (CanonicalCellRegistry.layout kind)} (blind : ¬ some a = wire.blinding)
    (x : (CanonicalCellRegistry.layout kind).Value a.1) (k : Address (CanonicalCellRegistry.layout kind)) :
    lastVal (indexEntries wire (store.set a (some x))) k =
      lastVal (indexEntries wire store ++ [(a, valueBytes wire a x)]) k := by
  rw [lastVal_snoc, indexExact, indexExact]
  by_cases same : a = k
  · subst same
    simp [blind]
  · have ne : k ≠ a := fun h => same h.symm
    simp only [same, if_false, Store.set_ne store a (some x) k ne]

/-- The index after removing a non-blinding address: the key dropped. -/
theorem lastVal_index_set_none (store : Store (CanonicalCellRegistry.layout kind))
    {a : Address (CanonicalCellRegistry.layout kind)} (blind : ¬ some a = wire.blinding)
    (k : Address (CanonicalCellRegistry.layout kind)) :
    lastVal (indexEntries wire (store.set a none)) k =
      lastVal (Theory.AuthTrie.Trie.dropKey a (indexEntries wire store)) k := by
  rw [Theory.AuthTrie.lastVal_dropKey, indexExact, indexExact]
  by_cases same : k = a
  · subst same
    simp
  · simp only [same, if_false, Store.set_ne store a none k same]

theorem maskOf_set_blinding (B : StoreCodec.Blinding wire) (store : Store (CanonicalCellRegistry.layout kind))
    (m : (CanonicalCellRegistry.layout kind).Value B.space) :
    maskOf wire (store.set B.address (some m)) = (wire.valueStream B.space).encode m := by
  simp [maskOf, StoreCodec.Blinding.blindingKey_eq B, StoreCodec.Blinding.address]

theorem maskOf_set_other {store : Store (CanonicalCellRegistry.layout kind)} {a : Address (CanonicalCellRegistry.layout kind)}
    (blind : ¬ some a = wire.blinding) (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    maskOf wire (store.set a v) = maskOf wire store := by
  unfold maskOf StoreCodec.blindingKey
  cases h : wire.blinding with
  | none => rfl
  | some b =>
      have ne : b ≠ a := fun same => blind (by rw [h, same])
      simp [Store.set_ne store a v b ne]

/-- The mask address passes the gate (it is never a declared data key). -/
theorem storeFits_set_mask {store : Store (CanonicalCellRegistry.layout kind)} (gate : storeFits wire store = true)
    (B : StoreCodec.Blinding wire) (fitsB : addressFits 256 kind B.address = true)
    (m : (CanonicalCellRegistry.layout kind).Value B.space) :
    storeFits wire (store.set B.address (some m)) = true :=
  storeFits_set wire gate fitsB (some m)

namespace KeptCell

variable {wire}

/-- Set the mask: the index is untouched (it ignores the blinding). -/
def setMask (cell : KeptCell wire) (fitsB : addressFits 256 kind cell.params.blinding.address = true)
    (m : (CanonicalCellRegistry.layout kind).Value cell.params.blinding.space) (version : Nat) : KeptCell wire :=
  { params := cell.params, version := version,
    fit := ⟨cell.fit.store.set cell.params.blinding.address (some m), storeFits_set_mask wire cell.fit.fits _ fitsB m⟩,
    index := cell.index,
    holds := by
      have same := indexIgnoresBlinding wire cell.fit.store (cell.fit.store.set cell.params.blinding.address (some m))
        (fun b off => by
          have ne : b ≠ cell.params.blinding.address := fun h => off (by
            rw [h]; exact cell.params.blinding.isBlinding.symm)
          exact (Store.set_ne _ _ _ b ne).symm)
      show cell.index.Holds (indexEntries wire (cell.fit.store.set cell.params.blinding.address (some m)))
      rw [← same]; exact cell.holds,
    mask := (wire.valueStream cell.params.blinding.space).encode m,
    mask_eq := maskOf_set_blinding wire cell.params.blinding _ m }

end KeptCell

/-- **Birth (and import)**: the whole store through the gate, the first mask at
the blinding address, one bulk build of the index; version 0. -/
def birth (params : Params wire) (fitsB : addressFits 256 kind params.blinding.address = true)
    (store : Store (CanonicalCellRegistry.layout kind)) (m : (CanonicalCellRegistry.layout kind).Value params.blinding.space) :
    Option (KeptCell wire) :=
  (admit wire store).map fun fit =>
    KeptCell.setMask
      ⟨params, 0, fit, Theory.AuthTrie.Cache.build (bits_length wire) (indexEntries wire fit.store),
        Theory.AuthTrie.Cache.build_holds (bits_length wire) _, maskOf wire fit.store, rfl⟩ fitsB m 0

theorem birth_refuses (params : Params wire) (fitsB : addressFits 256 kind params.blinding.address = true)
    {store : Store (CanonicalCellRegistry.layout kind)} {a : Address (CanonicalCellRegistry.layout kind)}
    (live : store a ≠ none) (overflows : addressFits 256 kind a = false)
    (m : (CanonicalCellRegistry.layout kind).Value params.blinding.space) : birth wire params fitsB store m = none := by
  simp [birth, admit_refuses live overflows]

namespace KeptCell

variable {wire}

/-- **One data write.** The blinding address and a key failing the gate are
refused; a value is one insert walk; a removal is one erase walk. -/
def write (cell : KeptCell wire) (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) : Option (KeptCell wire) :=
  if fits : addressFits 256 kind a = true then
    if blind : some a = wire.blinding then none
    else
      match v with
      | some x =>
          some ⟨cell.params, cell.version,
            ⟨cell.fit.store.set a (some x), storeFits_set wire cell.fit.fits fits (some x)⟩,
            cell.index.insert (bits_length wire) a (valueBytes wire a x),
            (Theory.AuthTrie.Cache.insert_holds (bits_length wire) cell.holds a _).congr fun k =>
              (lastVal_index_set_some wire cell.fit.store blind x k).symm,
            cell.mask, (maskOf_set_other wire blind _).trans cell.mask_eq⟩
      | none =>
          some ⟨cell.params, cell.version,
            ⟨cell.fit.store.set a none, storeFits_set wire cell.fit.fits fits none⟩,
            cell.index.erase a,
            (Theory.AuthTrie.Cache.erase_holds cell.holds a).congr fun k =>
              (lastVal_index_set_none wire cell.fit.store blind k).symm,
            cell.mask, (maskOf_set_other wire blind _).trans cell.mask_eq⟩
  else none

/-- One write of a patch. -/
abbrev Write := Σ a : Address (CanonicalCellRegistry.layout kind), Option ((CanonicalCellRegistry.layout kind).Value a.1)

/-- The patch's writes in order; refused when any write is. -/
def writeAll : KeptCell wire → List (Write (kind := kind)) → Option (KeptCell wire)
  | cell, [] => some cell
  | cell, w :: rest => (cell.write w.1 w.2).bind fun next => writeAll next rest

/-- **One accepted version**, atomically: the supplied mask and the next
version, then the patch (which never writes the mask), for a no-op patch too. -/
def accept (cell : KeptCell wire) (fitsB : addressFits 256 kind cell.params.blinding.address = true)
    (patch : List (Write (kind := kind))) (m : (CanonicalCellRegistry.layout kind).Value cell.params.blinding.space) :
    Option (KeptCell wire) :=
  writeAll (cell.setMask fitsB m (cell.version + 1)) patch

/-- **A key failing the gate is refused**, never written outside the index. -/
theorem write_refuses (cell : KeptCell wire) {a : Address (CanonicalCellRegistry.layout kind)}
    (overflows : addressFits 256 kind a = false) (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    cell.write a v = none := by
  simp [write, overflows]

/-- An accepted write holds exactly the updated store, mask and version kept. -/
theorem write_store {cell cell' : KeptCell wire} {a : Address (CanonicalCellRegistry.layout kind)}
    {v : Option ((CanonicalCellRegistry.layout kind).Value a.1)} (accepted : cell.write a v = some cell') :
    cell'.fit.store = cell.fit.store.set a v ∧ cell'.mask = cell.mask ∧ cell'.version = cell.version ∧
      cell'.params = cell.params := by
  unfold write at accepted
  by_cases fits : addressFits 256 kind a = true
  · rw [dif_pos fits] at accepted
    by_cases blind : some a = wire.blinding
    · rw [dif_pos blind] at accepted; cases accepted
    · rw [dif_neg blind] at accepted
      cases v <;> (cases accepted; exact ⟨rfl, rfl, rfl, rfl⟩)
  · rw [dif_neg fits] at accepted; cases accepted

/-- A fitting data write is accepted. -/
theorem write_accepts (cell : KeptCell wire) {a : Address (CanonicalCellRegistry.layout kind)}
    (fits : addressFits 256 kind a = true) (blind : ¬ some a = wire.blinding)
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    (cell.write a v).isSome := by
  unfold write
  rw [dif_pos fits, dif_neg blind]
  cases v <;> rfl

/-- The mask is never written by a patch. -/
theorem write_refuses_blinding (cell : KeptCell wire) {a : Address (CanonicalCellRegistry.layout kind)}
    (blind : some a = wire.blinding) (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) :
    cell.write a v = none := by
  unfold write
  by_cases fits : addressFits 256 kind a = true
  · rw [dif_pos fits, dif_pos blind]
  · rw [dif_neg fits]

/-- A removal is one erase walk of the kept index. -/
theorem write_none_index (cell : KeptCell wire) {a : Address (CanonicalCellRegistry.layout kind)}
    (fits : addressFits 256 kind a = true) (blind : ¬ some a = wire.blinding) :
    ∃ cell', cell.write a none = some cell' ∧ cell'.index = cell.index.erase a := by
  unfold write
  rw [dif_pos fits, dif_neg blind]
  exact ⟨_, rfl, rfl⟩

theorem writeAll_params : ∀ {cell cell' : KeptCell wire} {patch : List (Write (kind := kind))},
    writeAll cell patch = some cell' →
      cell'.params = cell.params ∧ cell'.version = cell.version ∧ cell'.mask = cell.mask
  | _, _, [], accepted => by cases accepted; exact ⟨rfl, rfl, rfl⟩
  | cell, cell', w :: rest, accepted => by
      simp only [writeAll, Option.bind_eq_some_iff] at accepted
      obtain ⟨next, step, tail⟩ := accepted
      obtain ⟨_, hm, hv, hp⟩ := write_store step
      obtain ⟨hp', hv', hm'⟩ := writeAll_params tail
      exact ⟨hp'.trans hp, hv'.trans hv, hm'.trans hm⟩

/-- **An accepted version** carries the supplied mask, the next version, and a
root equal to the private root of its store under its own context. -/
theorem accept_spec {cell cell' : KeptCell wire} {fitsB : addressFits 256 kind cell.params.blinding.address = true}
    {patch : List (Write (kind := kind))} {m : (CanonicalCellRegistry.layout kind).Value cell.params.blinding.space}
    (accepted : cell.accept fitsB patch m = some cell') :
    cell'.version = cell.version + 1 ∧ cell'.params = cell.params ∧
      cell'.mask = (wire.valueStream cell.params.blinding.space).encode m ∧
      cell'.root = privateRoot wire (ctxBytes wire cell.params (cell.version + 1)) cell'.fit.store := by
  unfold accept at accepted
  obtain ⟨hp, hv, hm⟩ := writeAll_params accepted
  refine ⟨hv, hp, hm, ?_⟩
  rw [root_eq]
  simp only [ctx, hp, hv, setMask]

end KeptCell

#assert_axioms KeptCell.root_eq
#assert_axioms birth_refuses
#assert_axioms storeFits_set
#assert_axioms KeptCell.write_refuses
#assert_axioms KeptCell.write_refuses_blinding
#assert_axioms KeptCell.write_store
#assert_axioms KeptCell.write_accepts
#assert_axioms KeptCell.write_none_index
#assert_axioms KeptCell.accept_spec

end Minidregg.Kernel.PrivateCellReceiver
