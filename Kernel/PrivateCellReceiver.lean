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
* `birth`: the whole store through `admit`, refused if it already holds a mask
  (`birth_refuses_masked`: an import is never silently re-masked), then the mask
  of version 0 and one bulk build of the index (`birth_accepts`).
* `write`: one data address. The blinding address is refused (the mask moves
  only by `accept`); a key failing `addressFits` is refused, never left out of
  the index; a value is one `Cache.insert` walk, a removal one `Cache.erase`
  walk (metered at `7 L + 3` interpreter operations, `L = 516`, on injective
  live paths: a path collision is a cSHAKE256 collision among live addresses,
  `viewOpeningExact_deployed`).
* `accept`: one accepted version, atomically: the version advanced and its mask
  `prf (version + 1)` set at the blinding address, then the patch's writes in
  order, for a no-op patch too (`accept_spec`: the resulting store exactly;
  `accept_isSome_iff`: accepted exactly when every write fits and avoids the
  blinding). No caller supplies a mask. `History.custodyInputs_distinct`: across
  a cell's history the custody function is evaluated at pairwise distinct
  versions. Freshness is the named premise `Custody.CustodyPrf` (teeth:
  `Custody.constant_refuted`), composed with the distinct inputs in
  `receiver_prf_term`, the hybrid argument's PRF hop. Forks are the host's
  obligation `AtMostOneSuccessor` (a history meets it; `fork_shares_mask` is why).
* `root` / `root_eq`: the outer commitment from the kept digest and the held
  mask, under the context derived from the cell's state (`ctxOf`: protocol,
  cell, layout, accepted version, size bound), equals `privateRoot`, the
  specification over the whole store, which is
  `BlindedCellHidingDraft.maskedTrieCommitment` itself (one commitment
  definition).
* `blinding_fits`: the registry's blinding address passes the gate.

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
public import Kernel.BlindedCellHiding

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
bytes, public size bound, the registry's selection of the wire, the wire's
blinding address, and the custody mask function of this cell: the mask of
accepted version `v` is `prf v`. The host instantiates `prf` as a PRF under a
key independent of every disclosed value; the receiver only ever evaluates it
at strictly increasing versions (`History.custodyInputs_distinct`); its PRF
security is the named premise `CustodyPrf`. -/
structure Params where
  protocol : Nat
  cell : List UInt8
  layout : List UInt8
  sizeBound : Nat
  selected : CanonicalCellRegistry.wire? kind = some wire
  blinding : StoreCodec.Blinding wire
  prf : Nat → (CanonicalCellRegistry.layout kind).Value blinding.space

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
  BlindedCellHidingDraft.maskedTrieCommitment (deployedDig wire) (bits wire) 516 outerRoot ctx (maskOf wire store)
    (indexEntries wire store)

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
  rw [root, privateRoot, BlindedCellHidingDraft.maskedTrieCommitment, Theory.AuthTrie.Cache.digest_eq cell.holds,
    cell.mask_eq]

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

/-- **The registry's blinding address passes the gate**: for a declared kind it
is `StateKey.blinding`, which carries no digest; every other kind's addresses
always pass. -/
theorem blinding_fits {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    (selected : CanonicalCellRegistry.wire? kind = some wire) (B : StoreCodec.Blinding wire) :
    addressFits 256 kind B.address = true := by
  cases kind <;> simp only [CanonicalCellRegistry.wire?, Option.some.injEq, reduceCtorEq] at selected <;>
    first
    | (subst selected
       obtain ⟨space, key, isB, _⟩ := B
       cases space
       simp only [DeclaredEffectCell.wire, Minidregg.Theory.EffectDeclaration.StateKey.address, Option.some.injEq,
         Sigma.mk.injEq, heq_eq_eq, true_and] at isB
       subst isB
       rfl)
    | (simp [addressFits])

theorem storeFits_set_mask {store : Store (CanonicalCellRegistry.layout kind)} (gate : storeFits wire store = true)
    (selected : CanonicalCellRegistry.wire? kind = some wire) (B : StoreCodec.Blinding wire)
    (m : (CanonicalCellRegistry.layout kind).Value B.space) :
    storeFits wire (store.set B.address (some m)) = true :=
  storeFits_set wire gate (blinding_fits selected B) (some m)

namespace KeptCell

variable {wire}

/-- Set the mask: the index is untouched (it ignores the blinding). -/
def setMask (cell : KeptCell wire) (version : Nat) : KeptCell wire :=
  let m := cell.params.prf version
  { params := cell.params, version := version,
    fit := ⟨cell.fit.store.set cell.params.blinding.address (some m),
      storeFits_set_mask wire cell.fit.fits cell.params.selected _ m⟩,
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

/-- **Birth**: the whole store through the gate, refused when it already holds a
value at the blinding address (an imported cell is not silently re-masked: an
import of a masked cell is a re-genesis and states so by clearing the mask
first), then the mask of version 0 and one bulk build of the index. -/
def birth (params : Params wire) (store : Store (CanonicalCellRegistry.layout kind)) : Option (KeptCell wire) :=
  if store params.blinding.address = none then
    (admit wire store).map fun fit =>
      KeptCell.setMask
        ⟨params, 0, fit, Theory.AuthTrie.Cache.build (bits_length wire) (indexEntries wire fit.store),
          Theory.AuthTrie.Cache.build_holds (bits_length wire) _, maskOf wire fit.store, rfl⟩ 0
  else none

theorem birth_refuses (params : Params wire)
    {store : Store (CanonicalCellRegistry.layout kind)} {a : Address (CanonicalCellRegistry.layout kind)}
    (live : store a ≠ none) (overflows : addressFits 256 kind a = false) : birth wire params store = none := by
  unfold birth
  split
  · simp [admit_refuses live overflows]
  · rfl

theorem birth_refuses_masked (params : Params wire) {store : Store (CanonicalCellRegistry.layout kind)}
    (masked : store params.blinding.address ≠ none) : birth wire params store = none := by
  simp [birth, masked]

/-- **Birth accepts** a gated store with no mask: version 0, the store with the
mask of version 0 set, that mask held. -/
theorem birth_accepts (params : Params wire) {store : Store (CanonicalCellRegistry.layout kind)}
    (gate : storeFits wire store = true) (unmasked : store params.blinding.address = none) :
    ∃ cell, birth wire params store = some cell ∧ cell.version = 0 ∧ cell.params = params ∧
      cell.fit.store = store.set params.blinding.address (some (params.prf 0)) ∧
      cell.mask = (wire.valueStream params.blinding.space).encode (params.prf 0) := by
  unfold birth admit
  rw [if_pos unmasked, dif_pos gate]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

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

/-- **One accepted version**, atomically: the next version and its custody mask
`prf (version + 1)`, then the patch (which never writes the mask), for a no-op
patch too. No caller supplies a mask, so none can be reused. -/
def accept (cell : KeptCell wire) (patch : List (Write (kind := kind))) : Option (KeptCell wire) :=
  writeAll (cell.setMask (cell.version + 1)) patch

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

/-- A patch applied in order to a store. -/
def applyPatch (store : Store (CanonicalCellRegistry.layout kind)) (patch : List (Write (kind := kind))) :
    Store (CanonicalCellRegistry.layout kind) :=
  patch.foldl (fun s w => s.set w.1 w.2) store

theorem writeAll_store : ∀ {cell cell' : KeptCell wire} {patch : List (Write (kind := kind))},
    writeAll cell patch = some cell' → cell'.fit.store = applyPatch cell.fit.store patch
  | _, _, [], accepted => by cases accepted; rfl
  | cell, cell', w :: rest, accepted => by
      simp only [writeAll, Option.bind_eq_some_iff] at accepted
      obtain ⟨next, step, tail⟩ := accepted
      rw [writeAll_store tail, (write_store step).1]
      rfl

/-- **When a patch is accepted**: exactly when every write fits the gate and
avoids the blinding address. -/
theorem writeAll_isSome_iff : ∀ (cell : KeptCell wire) (patch : List (Write (kind := kind))),
    (writeAll cell patch).isSome ↔ ∀ w ∈ patch, addressFits 256 kind w.1 = true ∧ ¬ some w.1 = wire.blinding
  | _, [] => by simp [writeAll]
  | cell, w :: rest => by
      simp only [writeAll, List.mem_cons, forall_eq_or_imp]
      by_cases fits : addressFits 256 kind w.1 = true
      · by_cases blind : some w.1 = wire.blinding
        · rw [write_refuses_blinding cell blind]; simp [blind]
        · obtain ⟨next, step⟩ := Option.isSome_iff_exists.mp (write_accepts cell fits blind w.2)
          rw [step, Option.bind_some, writeAll_isSome_iff next rest]
          simp [fits, blind]
      · rw [write_refuses cell (by simpa using fits)]; simp [fits]

/-- **An accepted version**: the next version, its custody mask, the store the
old one with that mask set and the patch applied in order, and a root equal to
the private root of that store under the version's context. -/
theorem accept_spec {cell cell' : KeptCell wire} {patch : List (Write (kind := kind))}
    (accepted : cell.accept patch = some cell') :
    cell'.version = cell.version + 1 ∧ cell'.params = cell.params ∧
      cell'.mask = (wire.valueStream cell.params.blinding.space).encode (cell.params.prf (cell.version + 1)) ∧
      cell'.fit.store = applyPatch
        (cell.fit.store.set cell.params.blinding.address (some (cell.params.prf (cell.version + 1)))) patch ∧
      cell'.root = privateRoot wire (ctxBytes wire cell.params (cell.version + 1)) cell'.fit.store := by
  unfold accept at accepted
  obtain ⟨hp, hv, hm⟩ := writeAll_params accepted
  refine ⟨hv, hp, hm, writeAll_store accepted, ?_⟩
  rw [root_eq]
  simp only [ctx, hp, hv, setMask]

theorem accept_isSome_iff (cell : KeptCell wire) (patch : List (Write (kind := kind))) :
    (cell.accept patch).isSome ↔ ∀ w ∈ patch, addressFits 256 kind w.1 = true ∧ ¬ some w.1 = wire.blinding :=
  writeAll_isSome_iff _ patch

end KeptCell

/-! ## Mask freshness: one cell's accepted history -/

/-- An accepted history of one cell, newest first: a birth, then accepts. -/
inductive History : List (KeptCell wire) → Prop
  | birth {params : Params wire} {store : Store (CanonicalCellRegistry.layout kind)} {cell : KeptCell wire} :
      birth wire params store = some cell → History [cell]
  | accept {cell next : KeptCell wire} {older : List (KeptCell wire)} {patch : List (KeptCell.Write (kind := kind))} :
      History (cell :: older) → cell.accept patch = some next → History (next :: cell :: older)

/-- Every version of a history holds the custody mask of its own version, under
one set of parameters, and the versions strictly decrease from the newest. -/
theorem History.spec : ∀ {cells : List (KeptCell wire)}, History wire cells →
    (∀ c ∈ cells, c.mask = (wire.valueStream c.params.blinding.space).encode (c.params.prf c.version)) ∧
      cells.Pairwise (fun newer older => older.version < newer.version ∧ newer.params = older.params)
  | _, .birth (cell := cell) born => by
      unfold PrivateCellReceiver.birth at born
      split at born
      · obtain ⟨fit, _, rfl⟩ := Option.map_eq_some_iff.mp born
        exact ⟨by simp [KeptCell.setMask], List.pairwise_singleton _ _⟩
      · cases born
  | _, .accept (cell := cell) (next := next) (older := older) earlier accepted => by
      obtain ⟨masks, chain⟩ := History.spec earlier
      obtain ⟨hv, hp, hm, _, _⟩ := KeptCell.accept_spec accepted
      refine ⟨?_, List.pairwise_cons.mpr ⟨?_, chain⟩⟩
      · intro c member
        rcases List.mem_cons.mp member with same | member
        · have key : ∀ q : Params wire, q = cell.params →
              (wire.valueStream q.blinding.space).encode (q.prf (cell.version + 1)) =
                (wire.valueStream cell.params.blinding.space).encode (cell.params.prf (cell.version + 1)) := by
            rintro q rfl; rfl
          rw [same, hm, hv]; exact (key _ hp).symm
        · exact masks c member
      · intro c member
        rcases List.mem_cons.mp member with same | member
        · rw [same]; exact ⟨by omega, hp⟩
        · obtain ⟨lt, same⟩ := (List.pairwise_cons.mp chain).1 c member
          exact ⟨by omega, hp.trans same⟩

/-- **Distinct custody inputs**: across a history the custody function is
evaluated at pairwise distinct versions, each version's mask being its own
evaluation. This alone does not make masks fresh (a constant function passes
it); freshness is `CustodyPrf` of the function, composed in `receiver_prf_term`. -/
theorem History.custodyInputs_distinct {cells : List (KeptCell wire)} (history : History wire cells) :
    (cells.map KeptCell.version).Nodup ∧
      ∀ c ∈ cells, c.mask = (wire.valueStream c.params.blinding.space).encode (c.params.prf c.version) := by
  obtain ⟨masks, chain⟩ := history.spec
  exact ⟨List.pairwise_map.mpr (chain.imp fun h => Nat.ne_of_gt h.1), masks⟩


/-! ## The custody PRF and the receiver's PRF term -/

open Minidregg.Theory.FiniteTapeGap (GapAtMost)

namespace Custody

/-- **The custody PRF game**: over `tapes` equally likely draws of the custody
key (`keyed`) or of an ideal function (`ideal`), no budgeted test of the
function separates the two by more than `num/den`. The key is a tape, so it is
outside every reader's view; the test sees the function only through its
values. -/
def CustodyPrf {M : Type} (tapes num den : Nat) (keyed ideal : Fin tapes → Nat → M)
    (budgeted : ((Nat → M) → Bool) → Prop) : Prop :=
  ∀ test, budgeted test → GapAtMost tapes num den (fun t => test (keyed t)) (fun t => test (ideal t))

/-- Satisfiable: the ideal function against itself, at gap zero. -/
theorem identity_satisfies {M : Type} {tapes den : Nat} (positive : 0 < tapes) (denominator : 0 < den)
    (ideal : Fin tapes → Nat → M) (budgeted : ((Nat → M) → Bool) → Prop) :
    CustodyPrf tapes 0 den ideal ideal budgeted :=
  fun _ _ => ⟨positive, denominator, by simp, by simp⟩

/-- All four functions on `{1, 2}` into `Bool` (zero elsewhere). -/
def idealFour (t : Fin 4) (n : Nat) : Bool :=
  if n = 1 then t.val % 2 = 1 else if n = 2 then t.val / 2 = 1 else false

/-- The test "the masks of versions 1 and 2 agree". -/
def equalTest (f : Nat → Bool) : Bool := f 1 == f 2

/-- **Teeth**: a constant custody function fails the game at any gap below
one half against the test that compares two versions' masks. -/
theorem constant_refuted :
    ¬ CustodyPrf 4 1 4 (fun _ _ => false) idealFour (fun test => test = equalTest) := by
  intro prf
  obtain ⟨_, _, bound, _⟩ := prf equalTest rfl
  revert bound
  decide

end Custody

open Custody (CustodyPrf)

/-- **The receiver's PRF term.** A history's custody inputs are pairwise
distinct and each version holds its own evaluation; and for a game that reads
the masks only through the custody function, `CustodyPrf` of that function
gives the hybrid argument's first hop (`BlindedCellHidingDraft.HybridReduction`,
real masks against an ideal function, gap `fNum/den := num/den`). At the
distinct inputs the history supplies, the ideal function's values are what the
uniform hybrid samples. -/
theorem receiver_prf_term {M Strategy : Type} {cells : List (KeptCell wire)} (history : History wire cells)
    (tapes num den : Nat) (keyed ideal : Fin tapes → Nat → M) (budgetedPrf : ((Nat → M) → Bool) → Prop)
    (prf : CustodyPrf tapes num den keyed ideal budgetedPrf)
    (game : Strategy → Bool → (Nat → M) → Bool) (legal budgeted : Strategy → Prop)
    (reduces : ∀ a, legal a → budgeted a → ∀ b, budgetedPrf (game a b)) :
    (cells.map KeptCell.version).Nodup ∧
      (∀ c ∈ cells, c.mask = (wire.valueStream c.params.blinding.space).encode (c.params.prf c.version)) ∧
      ∀ a, legal a → budgeted a → ∀ b,
        GapAtMost tapes num den (fun t => game a b (keyed t)) (fun t => game a b (ideal t)) := by
  obtain ⟨distinct, masks⟩ := history.custodyInputs_distinct
  exact ⟨distinct, masks, fun a isLegal isBudgeted b => prf _ (reduces a isLegal isBudgeted b)⟩

/-! ## Forks: one accepted successor per version -/

/-- **At most one accepted successor per version**: among the host's accepted
cells, one parameter set and one version name one cell. A host that accepts
twice from one version publishes two stores under one mask; this is the host's
obligation (a persisted version counter, a retry returning the stored
successor), stated here so the hiding argument can take it as a premise. -/
def AtMostOneSuccessor (accepted : KeptCell wire → Prop) : Prop :=
  ∀ c c', accepted c → accepted c' → c.params = c'.params → c.version = c'.version → c = c'

/-- A single history meets it. -/
theorem History.atMostOneSuccessor {cells : List (KeptCell wire)} (history : History wire cells) :
    AtMostOneSuccessor wire (· ∈ cells) := by
  intro c c' hc hc' _ same
  obtain ⟨distinct, _⟩ := history.custodyInputs_distinct
  exact List.inj_on_of_nodup_map distinct hc hc' same

namespace KeptCell

variable {wire}

/-- **Why it is an obligation**: two accepts from one cell share the version and
the mask, whatever their patches. -/
theorem fork_shares_mask {cell left right : KeptCell wire} {patchL patchR : List (Write (kind := kind))}
    (acceptedL : cell.accept patchL = some left) (acceptedR : cell.accept patchR = some right) :
    left.version = right.version ∧ left.mask = right.mask := by
  obtain ⟨hvL, _, hmL, _, _⟩ := accept_spec acceptedL
  obtain ⟨hvR, _, hmR, _, _⟩ := accept_spec acceptedR
  exact ⟨hvL.trans hvR.symm, hmL.trans hmR.symm⟩

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
#assert_axioms KeptCell.accept_isSome_iff
#assert_axioms blinding_fits
#assert_axioms birth_accepts
#assert_axioms birth_refuses_masked
#assert_axioms History.custodyInputs_distinct
#assert_axioms Custody.constant_refuted
#assert_axioms Custody.identity_satisfies
#assert_axioms receiver_prf_term
#assert_axioms History.atMostOneSuccessor
#assert_axioms KeptCell.fork_shares_mask

end Minidregg.Kernel.PrivateCellReceiver
