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
  versions. Freshness is the named premise `Custody.CustodyPrf`: the ideal fixed as
  the uniform function on the version window, the budget admitting every
  two-query evaluation test (satisfiable `enumeration_satisfies`, teeth
  `constant_refuted`). Forks are the host's obligation `AtMostOneSuccessor` (a
  history meets it; `fork_shares_mask` is why; `PublishesRun` is the premise
  that carries it to the deployed host).
* What is published: a `Serve` (a function of a version's context, mask and
  kept index: roots, openings). The host's obligations: `ViewThroughServe`
  (every reader's view is a function of the served items) and `ServesWithin`
  (the mask reaches a view only inside the outer commitment and the index only
  through the leakage; teeth
  `recoverable_refuted`: an archive of store bytes, which carry the blinding
  value, is refused).
* `arun`, the adaptive run (each patch chosen from the items served so far), is
  `srun`, the same run with the masks substituted, at the custody function's
  masks on versions `0 … rounds` (`arun_srun`). `receiver_prf_hop` /
  `receiver_prf_hop_view`: `HybridReduction`'s first antecedent against an
  adaptive strategy (refusals included), on the whole published transcript or
  any view through it, under the reduction's efficiency obligation.
* `root` / `root_eq`: the outer commitment from the kept digest and the held
  mask, under the kind-level context `kindCtx` (protocol version and the
  wire's frame, a function of the wire alone), equals `privateRoot`, the
  specification over the whole store, which is
  `BlindedCellHiding.maskedTrieCommitment` itself (one commitment
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.List

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

/-- The private-cell protocol version, bound into every kind's context. -/
def protocolVersion : Nat := 1

/-- **The kind-level context**: the protocol version and the wire's frame (magic, store version
and layout digest). A function of the wire alone, so every cell of a kind has it by
construction: no parameter set can carry another (round 18, context uniformity). The cell's
identity and accepted version are not here: they are in the blinding value, which the receiver
writes per accepted version (`CustodyCodec`), so the root is a function of the store
(`Kernel.PrivateCellMaterializer`), and the separation of outer-hash inputs across versions and
cells comes from the custody value's kind-level decode (`History.custodyBytes_nodup`,
`CustodyCodec.cross_cell`), not from a context. -/
def kindCtx : List UInt8 :=
  (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.byte)).encode
    (protocolVersion, StoreCodec.frame wire)

/-- The cell's fixed parameters: its identity, the registry's selection of the wire, the wire's
blinding address, and the custody function of this cell: the custody value of accepted version
`v` is `prf v`. The host instantiates `prf` from a PRF under a key independent of every
disclosed value; the receiver only ever evaluates it at strictly increasing versions
(`History.custodyInputs_distinct`); its PRF security is the named premise `CustodyPrf`. -/
structure Params where
  cell : List UInt8
  selected : CanonicalCellRegistry.wire? kind = some wire
  blinding : StoreCodec.Blinding wire
  prf : Nat → (CanonicalCellRegistry.layout kind).Value blinding.space

/-- **A kind-level custody decode**: fixed by the wire, never by a cell's parameters, so the
cell identity it returns is read from the bytes (round 18: a per-parameters decode could return
the constant `params.cell` without the bytes carrying it). -/
abbrev CustodyDecode := List UInt8 → Option (List UInt8 × Nat × List UInt8)

/-- **The custody encoding** of a cell's parameters under the kind's decode: the blinding value
of version `v` (`params.prf v`) decodes exactly to the cell's identity, the version and the
secret mask bytes. Only `secret` bears entropy: the identity and version are public, so the
hiding argument's `λ` is the entropy of `secret v` alone. -/
structure CustodyCodec (decode : CustodyDecode) (params : Params wire) where
  secret : Nat → List UInt8
  exact : ∀ v, decode ((wire.valueStream params.blinding.space).encode (params.prf v)) =
    some (params.cell, v, secret v)

/-- The cell's mask: its blinding value's bytes (none: the empty mask). -/
def maskOf (store : Store (CanonicalCellRegistry.layout kind)) : List UInt8 :=
  (StoreCodec.blindingKey wire store).getD []

/-- **The private root (specification)**: the outer commitment over the mask and
the canonical root of the store's index, computed from the whole store. -/
def privateRoot (ctx : List UInt8) (store : Store (CanonicalCellRegistry.layout kind)) : Digest :=
  BlindedCellHiding.maskedTrieCommitment (deployedDig wire) (bits wire) 516 outerRoot ctx (maskOf wire store)
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
def ctx (_cell : KeptCell wire) : List UInt8 := kindCtx wire

/-- The root from the kept digest and the held mask: no rebuild, no store lookup. -/
def root (cell : KeptCell wire) : Digest := outerRoot cell.ctx cell.mask cell.index.digest

/-- **The kept root is the private root** under the cell's own context. -/
theorem root_eq (cell : KeptCell wire) : cell.root = privateRoot wire cell.ctx cell.fit.store := by
  rw [root, privateRoot, BlindedCellHiding.maskedTrieCommitment, Theory.AuthTrie.Cache.digest_eq cell.holds,
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
      cell'.root = privateRoot wire (kindCtx wire) cell'.fit.store := by
  unfold accept at accepted
  obtain ⟨hp, hv, hm⟩ := writeAll_params accepted
  refine ⟨hv, hp, hm, writeAll_store accepted, ?_⟩
  rw [root_eq]
  simp only [ctx, hp, hv, setMask]

/-- **Acceptance as one composite patch**: the store an accepted version holds is the old store
under the custody write of version `version + 1` followed by the caller's patch. The custody
write is the receiver's (from `prf`), never the caller's: every caller write at the blinding
address is refused (`accept_isSome_iff`). -/
theorem accept_composite {cell cell' : KeptCell wire} {patch : List (Write (kind := kind))}
    (accepted : cell.accept patch = some cell') :
    cell'.fit.store = applyPatch cell.fit.store
      (⟨cell.params.blinding.address, some (cell.params.prf (cell.version + 1))⟩ :: patch) :=
  (accept_spec accepted).2.2.2.1

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
it); freshness is `CustodyPrf` of the function, composed in `receiver_prf_hop`. -/
theorem History.custodyInputs_distinct {cells : List (KeptCell wire)} (history : History wire cells) :
    (cells.map KeptCell.version).Nodup ∧
      ∀ c ∈ cells, c.mask = (wire.valueStream c.params.blinding.space).encode (c.params.prf c.version) := by
  obtain ⟨masks, chain⟩ := history.spec
  exact ⟨List.pairwise_map.mpr (chain.imp fun h => Nat.ne_of_gt h.1), masks⟩


/-- **Custody bytes never repeat under one codec**: two versions' blinding bytes differ, by the
exact decode, whatever the secret masks are (a repeated mask does not repeat an outer-hash
input). -/
theorem CustodyCodec.bytes_ne {decode : CustodyDecode} {params : Params wire}
    (codec : CustodyCodec wire decode params) {v w : Nat}
    (ne : v ≠ w) : (wire.valueStream params.blinding.space).encode (params.prf v) ≠
      (wire.valueStream params.blinding.space).encode (params.prf w) := fun same => by
  have := (codec.exact v).symm.trans (same ▸ codec.exact w)
  exact ne (Prod.mk.inj (Prod.mk.inj (Option.some.inj this)).2).1

/-- Teeth: a constant custody value has no custody codec once two versions exist. -/
theorem CustodyCodec.constant_refuted {decode : CustodyDecode} {params : Params wire}
    (constant : ∀ v, params.prf v = params.prf 0) : CustodyCodec wire decode params → False :=
  fun codec => CustodyCodec.bytes_ne wire codec (v := 0) (w := 1) (by decide) (by rw [constant 1])

/-- **The outer-hash inputs of a history are pairwise distinct** under a custody codec of its
parameters: every version's blinding bytes (the mask argument of the outer hash) differ. This is
what replaces a per-version context; no birthday term enters. -/
theorem History.custodyBytes_nodup {cells : List (KeptCell wire)} (history : History wire cells)
    {decode : CustodyDecode} {params : Params wire} (codec : CustodyCodec wire decode params)
    (same : ∀ c ∈ cells, c.params = params) :
    (cells.map KeptCell.mask).Nodup := by
  obtain ⟨versions, masks⟩ := history.custodyInputs_distinct
  rw [List.nodup_map_iff_inj_on (List.Nodup.of_map _ versions)]
  intro c hc d hd equal
  by_contra differ
  have hv : c.version ≠ d.version := fun hv => differ (List.inj_on_of_nodup_map versions hc hd hv)
  rw [masks c hc, masks d hd] at equal
  have key : ∀ q₁ q₂ : Params wire, q₁ = params → q₂ = params → ∀ v w,
      (wire.valueStream q₁.blinding.space).encode (q₁.prf v) =
        (wire.valueStream q₂.blinding.space).encode (q₂.prf w) → v = w := by
    rintro q₁ q₂ rfl rfl v w eq; by_contra ne; exact CustodyCodec.bytes_ne wire codec ne eq
  exact hv (key _ _ (same c hc) (same d hd) _ _ equal)

/-- **Cross-cell separation** (round 18): under one kind-level decode, the custody bytes of two
cells with different identities never coincide, at any versions, whatever their secrets: the
decode reads the identity back from the bytes. So two cells of one kind at one version with one
secret do not share an outer-hash input, and no birthday term over cells enters `rom`. -/
theorem CustodyCodec.cross_cell {decode : CustodyDecode} {p q : Params wire}
    (cp : CustodyCodec wire decode p) (cq : CustodyCodec wire decode q) (differ : p.cell ≠ q.cell)
    (v w : Nat) : (wire.valueStream p.blinding.space).encode (p.prf v) ≠
      (wire.valueStream q.blinding.space).encode (q.prf w) := fun same => by
  have := (cp.exact v).symm.trans (same ▸ cq.exact w)
  exact differ (Prod.mk.inj (Option.some.inj this)).1

/-- Across two cells' histories under one kind-level decode, no mask (outer-hash mask argument)
of one equals a mask of the other. -/
theorem History.custodyBytes_disjoint {cs ds : List (KeptCell wire)} (hc : History wire cs) (hd : History wire ds)
    {decode : CustodyDecode} {p q : Params wire} (cp : CustodyCodec wire decode p)
    (cq : CustodyCodec wire decode q) (onP : ∀ c ∈ cs, c.params = p) (onQ : ∀ d ∈ ds, d.params = q)
    (differ : p.cell ≠ q.cell) : ∀ c ∈ cs, ∀ d ∈ ds, c.mask ≠ d.mask := by
  intro c mc d md equal
  rw [(hc.custodyInputs_distinct).2 c mc, (hd.custodyInputs_distinct).2 d md] at equal
  have key : ∀ q₁ q₂ : Params wire, q₁ = p → q₂ = q →
      (wire.valueStream q₁.blinding.space).encode (q₁.prf c.version) ≠
        (wire.valueStream q₂.blinding.space).encode (q₂.prf d.version) := by
    rintro q₁ q₂ rfl rfl; exact CustodyCodec.cross_cell wire cp cq differ _ _
  exact key _ _ (onP c mc) (onQ d md) equal

/-- Teeth: two cells with different identities whose custody bytes coincide (a custody value
that omits the cell) have no custody codecs under one kind-level decode. -/
theorem CustodyCodec.shared_bytes_refuted {decode : CustodyDecode} {p q : Params wire}
    (differ : p.cell ≠ q.cell)
    (shared : (wire.valueStream p.blinding.space).encode (p.prf 0) = (wire.valueStream q.blinding.space).encode (q.prf 0)) :
    CustodyCodec wire decode p → CustodyCodec wire decode q → False :=
  fun cp cq => CustodyCodec.cross_cell wire cp cq differ 0 0 shared

/-! ### A kind-level custody decode over custody naturals -/

/-- An injective code of a cell identity. -/
def cellCode (cell : List UInt8) : Nat := Encodable.encode (cell.map UInt8.toNat)

/-- Its inverse on codes. -/
def cellOfCode (code : Nat) : Option (List UInt8) :=
  (Encodable.decode (α := List Nat) code).map (List.map UInt8.ofNat)

theorem cellOfCode_cellCode (cell : List UInt8) : cellOfCode (cellCode cell) = some cell := by
  simp only [cellOfCode, cellCode, Encodable.encodek, Option.map_some, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id cell]
  exact List.map_congr_left fun b _ => UInt8.ofNat_toNat

/-- **The custody natural** of cell `cell`, version `v` and secret `x`: the cell code, the
version and the secret, paired. -/
def custodyNat (cell : List UInt8) (v x : Nat) : Nat := Nat.pair (cellCode cell) (Nat.pair v x)

/-- **The decode of custody naturals**, fixed by the wire's reader `readNat` (the blinding
space's value bytes back to a natural) and the secret's byte form: the cell identity, version
and secret are read from the natural the bytes carry. -/
def natDecode (readNat : List UInt8 → Option Nat) (secretBytes : Nat → List UInt8) : CustodyDecode :=
  fun bytes => (readNat bytes).bind fun n =>
    (cellOfCode n.unpair.1).map fun cell => (cell, n.unpair.2.unpair.1, secretBytes n.unpair.2.unpair.2)

theorem natDecode_custodyNat {readNat : List UInt8 → Option Nat} (secretBytes : Nat → List UInt8)
    {bytes : List UInt8} {cell : List UInt8} {v x : Nat} (read : readNat bytes = some (custodyNat cell v x)) :
    natDecode readNat secretBytes bytes = some (cell, v, secretBytes x) := by
  simp [natDecode, read, custodyNat, Nat.unpair_pair, cellOfCode_cellCode]

/-! ## The custody PRF and the receiver's PRF term -/

open Minidregg.Theory.FiniteTapeGap (GapAtMost)

namespace Custody

variable (m : Nat)

/-- The number of functions from a version window into masks `Fin (m + 1)`. -/
abbrev funs (window : List Nat) : Nat := (m + 1) ^ window.length

/-- **The ideal function** on a version window: tape `t` is one of all
`(m + 1) ^ |window|` functions window → `Fin (m + 1)`, each equally likely
(`finFunctionFinEquiv`); outside the window it is `0`. -/
def idealFn (window : List Nat) (t : Fin (funs m window)) (v : Nat) : Fin (m + 1) :=
  if h : v ∈ window then finFunctionFinEquiv.symm t ⟨window.idxOf v, List.idxOf_lt_length_iff.mpr h⟩ else 0

/-- On a window of distinct versions, the ideal function's values at the window
are exactly the tape's tuple: independent uniform masks. -/
theorem idealFn_window {window : List Nat} (distinct : window.Nodup) (t : Fin (funs m window)) (i : Fin window.length) :
    idealFn m window t window[i] = finFunctionFinEquiv.symm t i := by
  have mem : window[i] ∈ window := List.getElem_mem _
  simp only [idealFn, mem, dif_pos]
  exact congrArg _ (Fin.ext (distinct.idxOf_getElem i i.isLt))

/-- The test "the masks of versions `v` and `w` agree". -/
def equalityTest (v w : Nat) (f : Nat → Fin (m + 1)) : Bool := f v == f w

/-- The successor on masks, `x ↦ x + 1` mod `m + 1`. -/
def succMask (x : Fin (m + 1)) : Fin (m + 1) := x + 1

/-- The test "the mask of `w` is the successor of the mask of `v`": two queries,
one efficient relation. -/
def succTest (v w : Nat) (f : Nat → Fin (m + 1)) : Bool := f w == succMask m (f v)

/-- The test "the mask of version `v` is `c`": one query, efficient. -/
def pointTest (v : Nat) (c : Fin (m + 1)) (f : Nat → Fin (m + 1)) : Bool := f v == c

/-- **The named distinguishers a meaningful budget admits**: equality of two
distinct window versions' masks (a function repeating a mask fails against
them), the successor relation between two of them (a keyed shift, one disclosed
mask revealing every other, fails against it) and the one-query point tests on
the window (a function predictable at one version, such as a public counter,
fails against them). The budget is
meant as the efficiency class of the PRF assumption, and Lean does not tie it
to efficiency: at a use it is the composed reduction tests plus these named
distinguishers, nothing more. Admitting every evaluation test would admit
exhaustive key search and make the premise statistical, which no short-key
PRF meets. -/
def BudgetAdmitsNamed (window : List Nat) (budgeted : ((Nat → Fin (m + 1)) → Bool) → Prop) : Prop :=
  (∀ v ∈ window, ∀ w ∈ window, v ≠ w → budgeted (equalityTest m v w) ∧ budgeted (succTest m v w)) ∧
    ∀ v ∈ window, ∀ c, budgeted (pointTest m v c)

/-- The budget of exactly the named distinguishers. -/
def namedBudget (window : List Nat) (test : (Nat → Fin (m + 1)) → Bool) : Prop :=
  (∃ v ∈ window, ∃ w ∈ window, v ≠ w ∧ (test = equalityTest m v w ∨ test = succTest m v w)) ∨
    ∃ v ∈ window, ∃ c, test = pointTest m v c

theorem namedBudget_admits (window : List Nat) : BudgetAdmitsNamed m window (namedBudget m window) :=
  ⟨fun v hv w hw ne => ⟨Or.inl ⟨v, hv, w, hw, ne, Or.inl rfl⟩, Or.inl ⟨v, hv, w, hw, ne, Or.inr rfl⟩⟩,
    fun v hv c => Or.inr ⟨v, hv, c, rfl⟩⟩

/-- The two halves of a joint tape: the key draw and the ideal function draw. -/
abbrev split {keys window : Nat} (t : Fin (keys * window)) : Fin keys × Fin window := finProdFinEquiv.symm t

/-- **The custody PRF game.** With the ideal fixed as the uniform function on the
version window and a budget admitting the named distinguishers
(`BudgetAdmitsNamed`), no budgeted test separates the keyed custody function (key drawn
uniformly from `keys`, outside every view) from the ideal by more than
`num/den`. -/
def CustodyPrf (keys num den : Nat) (window : List Nat) (keyed : Fin keys → Nat → Fin (m + 1))
    (budgeted : ((Nat → Fin (m + 1)) → Bool) → Prop) : Prop :=
  BudgetAdmitsNamed m window budgeted ∧
    ∀ test, budgeted test →
      GapAtMost (keys * funs m window) num den
        (fun t => test (keyed (split t).1)) (fun t => test (idealFn m window (split t).2))

/-- **Satisfiable, honestly**: the custody function that IS the enumeration of
all functions on the window (its key is the function) meets the game at gap 0,
against every budget. -/
theorem enumeration_satisfies {den : Nat} (window : List Nat) (denominator : 0 < den)
    (budgeted : ((Nat → Fin (m + 1)) → Bool) → Prop) (admits : BudgetAdmitsNamed m window budgeted) :
    CustodyPrf m (funs m window) 0 den window (idealFn m window) budgeted := by
  refine ⟨admits, fun test _ => ?_⟩
  have positive : 0 < funs m window * funs m window := Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _))
    (Nat.pow_pos (Nat.succ_pos _))
  let swap : Equiv.Perm (Fin (funs m window * funs m window)) :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)
  have := GapAtMost.zero_of_perm positive denominator (fun t => test (idealFn m window (split t).2)) swap
  refine this.cast rfl rfl |> fun h => ?_
  have same : ((fun t => test (idealFn m window (split t).2)) ∘ swap) = fun t => test (idealFn m window (split t).1) := by
    funext t
    simp only [Function.comp, swap, Equiv.trans_apply, split, Equiv.symm_apply_apply, Equiv.prodComm_apply,
      Prod.snd_swap]
  rw [same] at h
  exact h

/-- All four functions on `{1, 2}` into `Fin 2`, as tape order gives them. -/
abbrev window12 : List Nat := [1, 2]

/-- **Teeth**: an equality test separates a constant custody function from the
ideal at gap `1/2`, so the `1/4` bound fails, against the budget of exactly the
named distinguishers. -/
theorem constant_refuted :
    ¬ CustodyPrf 1 2 1 4 window12 (fun _ _ => 0) (namedBudget 1 window12) := by
  rintro ⟨_, game⟩
  obtain ⟨_, _, bound, _⟩ := game (equalityTest 1 1 2) (Or.inl ⟨1, by simp, 2, by simp, by decide, Or.inl rfl⟩)
  revert bound
  decide

/-- A public counter: the mask of version `v` is `v mod (m + 1)`, whatever the key. -/
def counter (keys : Nat) (_k : Fin keys) (v : Nat) : Fin (m + 1) := ⟨v % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- **Teeth**: a public counter repeats no mask on `{1, 2}`, so it passes every
equality test; the point test "version 1's mask is 1" separates it from the
ideal at gap `m/(m+1) = 1/2`, so the `1/4` bound fails. -/
theorem counter_refuted :
    ¬ CustodyPrf 1 2 1 4 window12 (counter 1 2) (namedBudget 1 window12) := by
  rintro ⟨_, game⟩
  obtain ⟨_, _, bound, _⟩ := game (pointTest 1 1 1) (Or.inr ⟨1, by simp, 1, rfl⟩)
  revert bound
  decide

/-- A keyed shift: the mask of version `v` is `k + v`, the key uniform. Every
point marginal is uniform and no mask repeats, yet one disclosed mask reveals
all the others. -/
def shift (k : Fin (m + 1)) (v : Nat) : Fin (m + 1) := k + ⟨v % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- **Teeth**: at `m = 2` a keyed shift passes the `1/2` bound against every
equality test (gap `1/3`, `shift_passes_equality`) and every point test (gap
`0`, `shift_passes_points`), and fails it against the successor test (gap
`2/3`), which alone refutes it. -/
theorem shift_refuted :
    ¬ CustodyPrf 2 3 1 2 window12 (shift 2) (namedBudget 2 window12) := by
  rintro ⟨_, game⟩
  obtain ⟨_, _, bound, _⟩ := game (succTest 2 1 2) (Or.inl ⟨1, by simp, 2, by simp, by decide, Or.inr rfl⟩)
  revert bound
  decide

theorem shift_passes_equality :
    ∀ v ∈ window12, ∀ w ∈ window12, v ≠ w →
      GapAtMost (3 * funs 2 window12) 1 2 (fun t => equalityTest 2 v w (shift 2 (split t).1))
        (fun t => equalityTest 2 v w (idealFn 2 window12 (split t).2)) := by
  intro v hv w hw ne
  simp only [window12, List.mem_cons, List.not_mem_nil, or_false] at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> first | exact absurd rfl ne | (unfold GapAtMost; decide)

theorem shift_passes_points :
    ∀ v ∈ window12, ∀ c : Fin 3,
      GapAtMost (3 * funs 2 window12) 0 1 (fun t => pointTest 2 v c (shift 2 (split t).1))
        (fun t => pointTest 2 v c (idealFn 2 window12 (split t).2)) := by
  intro v hv c
  simp only [window12, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> revert c <;> unfold GapAtMost <;> decide

end Custody

open Custody (CustodyPrf funs idealFn split)

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

/-! ## Twins: one store and one patch list, only the key varying -/

namespace KeptCell

variable {wire}

/-- Two cells with the same public parameters, version and kept index: they
differ at most in the custody function and the mask. -/
def Twin (c₁ c₂ : KeptCell wire) : Prop :=
  c₁.params.cell = c₂.params.cell ∧ c₁.version = c₂.version ∧ c₁.index = c₂.index

theorem Twin.ctx {c₁ c₂ : KeptCell wire} (_twin : Twin c₁ c₂) : c₁.ctx = c₂.ctx := rfl

theorem Twin.symm {c₁ c₂ : KeptCell wire} (twin : Twin c₁ c₂) : Twin c₂ c₁ := by
  obtain ⟨tc, tv, ti⟩ := twin
  exact ⟨tc.symm, tv.symm, ti.symm⟩

theorem twins_symm : ∀ {cs₁ cs₂ : List (KeptCell wire)}, List.Forall₂ Twin cs₁ cs₂ → List.Forall₂ Twin cs₂ cs₁
  | _, _, .nil => .nil
  | _, _, .cons twin rest => .cons twin.symm (twins_symm rest)

theorem twins_versions : ∀ {cs₁ cs₂ : List (KeptCell wire)}, List.Forall₂ Twin cs₁ cs₂ →
    cs₁.map KeptCell.version = cs₂.map KeptCell.version
  | _, _, .nil => rfl
  | _, _, .cons twin rest => by simp only [List.map_cons, twin.2.1, twins_versions rest]

/-- **A twin's root is a function of its mask**: the context and index digest are shared. -/
theorem Twin.root {c₁ c₂ : KeptCell wire} (twin : Twin c₁ c₂) :
    c₁.root = outerRoot c₂.ctx c₁.mask c₂.index.digest := by
  rw [KeptCell.root, twin.ctx, twin.2.2]

/-- The index after one data write: a function of the old index. -/
def indexStep (index : Index wire) (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) : Index wire :=
  match v with
  | some x => index.insert (bits_length wire) a (valueBytes wire a x)
  | none => index.erase a

theorem write_index {cell cell' : KeptCell wire} {a : Address (CanonicalCellRegistry.layout kind)}
    {v : Option ((CanonicalCellRegistry.layout kind).Value a.1)} (accepted : cell.write a v = some cell') :
    cell'.index = indexStep cell.index a v := by
  unfold write at accepted
  by_cases fits : addressFits 256 kind a = true
  · rw [dif_pos fits] at accepted
    by_cases blind : some a = wire.blinding
    · rw [dif_pos blind] at accepted; cases accepted
    · rw [dif_neg blind] at accepted
      cases v <;> (cases accepted; rfl)
  · rw [dif_neg fits] at accepted; cases accepted

theorem write_twin {c₁ c₂ d₁ : KeptCell wire} (twin : Twin c₁ c₂) {a : Address (CanonicalCellRegistry.layout kind)}
    {v : Option ((CanonicalCellRegistry.layout kind).Value a.1)} (accepted : c₁.write a v = some d₁) :
    ∃ d₂, c₂.write a v = some d₂ ∧ Twin d₁ d₂ := by
  have ok := (writeAll_isSome_iff c₁ [⟨a, v⟩]).mp (by simp [writeAll, accepted])
  obtain ⟨fits, blind⟩ := ok ⟨a, v⟩ (List.mem_singleton_self _)
  obtain ⟨d₂, step⟩ := Option.isSome_iff_exists.mp (write_accepts c₂ fits blind v)
  obtain ⟨_, _, hv₁, hp₁⟩ := write_store accepted
  obtain ⟨_, _, hv₂, hp₂⟩ := write_store step
  obtain ⟨tc, tv, ti⟩ := twin
  refine ⟨d₂, step, ?_, ?_, ?_⟩
  · rw [hp₁, hp₂]; exact tc
  · rw [hv₁, hv₂]; exact tv
  · rw [write_index accepted, write_index step, ti]

theorem writeAll_twin : ∀ {c₁ c₂ d₁ : KeptCell wire} {patch : List (Write (kind := kind))},
    Twin c₁ c₂ → writeAll c₁ patch = some d₁ → ∃ d₂, writeAll c₂ patch = some d₂ ∧ Twin d₁ d₂
  | _, c₂, _, [], twin, accepted => by cases accepted; exact ⟨c₂, rfl, twin⟩
  | c₁, c₂, d₁, w :: rest, twin, accepted => by
      simp only [writeAll, Option.bind_eq_some_iff] at accepted ⊢
      obtain ⟨next₁, step₁, tail₁⟩ := accepted
      obtain ⟨next₂, step₂, twinNext⟩ := write_twin twin step₁
      obtain ⟨d₂, tail₂, twinD⟩ := writeAll_twin twinNext tail₁
      exact ⟨d₂, ⟨next₂, step₂, tail₂⟩, twinD⟩

theorem setMask_twin {c₁ c₂ : KeptCell wire} (twin : Twin c₁ c₂) (version : Nat) :
    Twin (c₁.setMask version) (c₂.setMask version) := by
  obtain ⟨tc, _, ti⟩ := twin
  exact ⟨tc, rfl, ti⟩

theorem accept_twin {c₁ c₂ d₁ : KeptCell wire} {patch : List (Write (kind := kind))} (twin : Twin c₁ c₂)
    (accepted : c₁.accept patch = some d₁) : ∃ d₂, c₂.accept patch = some d₂ ∧ Twin d₁ d₂ := by
  unfold accept at accepted ⊢
  have tv : c₁.version = c₂.version := twin.2.1
  rw [tv] at accepted
  exact writeAll_twin (setMask_twin twin _) accepted

end KeptCell

/-- Birth's twin: the same store under another custody function. -/
theorem birth_twin {p₁ p₂ : Params wire} (same : p₁.cell = p₂.cell ∧ p₁.blinding = p₂.blinding)
    {store : Store (CanonicalCellRegistry.layout kind)} {c₁ : KeptCell wire} (born : birth wire p₁ store = some c₁) :
    ∃ c₂, birth wire p₂ store = some c₂ ∧ KeptCell.Twin c₁ c₂ := by
  obtain ⟨sc, sb⟩ := same
  unfold birth at born ⊢
  split at born
  · rename_i unmasked
    rw [if_pos (sb ▸ unmasked)]
    obtain ⟨fit, admitted, rfl⟩ := Option.map_eq_some_iff.mp born
    exact ⟨KeptCell.setMask ⟨p₂, 0, fit, Theory.AuthTrie.Cache.build (bits_length wire) (indexEntries wire fit.store),
        Theory.AuthTrie.Cache.build_holds (bits_length wire) _, maskOf wire fit.store, rfl⟩ 0,
      by rw [admitted]; rfl, sc, rfl, rfl⟩
  · cases born

theorem birth_version {params : Params wire} {store : Store (CanonicalCellRegistry.layout kind)}
    {cell : KeptCell wire} (born : birth wire params store = some cell) : cell.version = 0 ∧ cell.params = params := by
  unfold birth at born
  split at born
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp born; exact ⟨rfl, rfl⟩
  · cases born

/-- A history under one parameter set holds that set's custody masks. -/
theorem History.masks_of_params {cells : List (KeptCell wire)} (history : History wire cells) {p : Params wire}
    (params : ∀ c ∈ cells, c.params = p) :
    ∀ c ∈ cells, c.mask = (wire.valueStream p.blinding.space).encode (p.prf c.version) := by
  intro c member
  rw [history.spec.1 c member]
  have key : ∀ q : Params wire, q = p →
      (wire.valueStream q.blinding.space).encode (q.prf c.version) =
        (wire.valueStream p.blinding.space).encode (p.prf c.version) := by
    rintro q rfl; rfl
  exact key _ (params c member)

/-! ## What the host serves, and what reaches a view -/

/-- **What the host serves for one accepted version**: a function of the
version's context, its mask and its kept index. Roots are one service
(`rootServe`); a deterministic opening of the index is another. A randomized
opening (the zero-knowledge opening, whose witness is the mask) is a `Serve` at
each fixed assignment of its proving coins, and the hop below holds at every
such assignment; averaging over an independent coin tape is owed. The second
argument is the version's public metadata (the cell's identity and the accepted
version, `Meta`), which any real host publishes; it is public by construction and
adds no leakage. -/
abbrev PublicMeta := List UInt8 × Nat

abbrev Serve (Item : Type) := List UInt8 → PublicMeta → List UInt8 → Index wire → Item

/-- The roots, as a service. -/
def rootServe : Serve wire Digest := fun ctx _ mask index => outerRoot ctx mask index.digest

namespace KeptCell

variable {wire}

/-- The item a cell's version is served as. -/
def served {Item : Type} (serve : Serve wire Item) (cell : KeptCell wire) : Item :=
  serve cell.ctx (cell.params.cell, cell.version) cell.mask cell.index

theorem served_root (cell : KeptCell wire) : cell.served (rootServe wire) = cell.root := rfl

end KeptCell

/-- **The host's view obligation**: everything any reader sees of the cell is a
function of the served items, newest first. Posting or archiving durable record
bytes (the store, its blinding value included) is outside it. -/
def ViewThroughServe {Item View : Type} (serve : Serve wire Item) (view : List (KeptCell wire) → View) : Prop :=
  ∃ g : List Item → View, ∀ cells, view cells = g (cells.map (KeptCell.served serve))

/-- **A deterministic service within the leakage**: its items are a function of
the context, the public metadata, the outer root and the authorized leakage `leak` of the index (the
design's `L`: for a reader, its `narrowPacked` view, `PrivateCellView`). The
mask reaches a view only inside the root, and the index only through `leak`.
This is the pointwise, deterministic case of the hybrids after the PRF hop
(ordered PRF, then zero-knowledge simulation of openings, then root replacement
under a uniform mask); a zero-knowledge opening meets it only after simulation,
distributionally. -/
def ServesWithin {Item Leak : Type} (leak : Index wire → Leak) (serve : Serve wire Item) : Prop :=
  ∃ S : List UInt8 → PublicMeta → Digest → Leak → Item,
    ∀ ctx pub mask index, serve ctx pub mask index = S ctx pub (outerRoot ctx mask index.digest) (leak index)

/-- Satisfiable: the roots, under any leakage. -/
theorem rootServe_servesWithin {Leak : Type} (leak : Index wire → Leak) : ServesWithin wire leak (rootServe wire) :=
  ⟨fun _ _ r _ => r, fun _ _ _ _ => rfl⟩

/-- Satisfiable: a view of the roots alone. -/
theorem roots_viewThroughServe : ViewThroughServe wire (rootServe wire) (fun cells => cells.map KeptCell.root) :=
  ⟨id, fun _ => rfl⟩

/-- **Teeth**: a service from which the mask can be read back (an archive of the
store bytes, which carry the blinding value; or the mask itself) is outside
every leakage. Masks of 33 bytes outnumber 256-bit roots, so two masks share a
root at one context and index, and the service would have to tell them apart
from that root and the index's leakage. (Exposure of the index is excluded only
distributionally: two indexes with one root are a cSHAKE256 collision, so no
pointwise refutation is claimed for it.) -/
theorem recoverable_refuted {Item Leak : Type} (leak : Index wire → Leak) (serve : Serve wire Item)
    (recover : Item → List UInt8) (recovers : ∀ ctx pub mask index, recover (serve ctx pub mask index) = mask) :
    ¬ ServesWithin wire leak serve := by
  rintro ⟨S, factors⟩
  let index : Index wire := Theory.AuthTrie.Cache.build (bits_length wire) []
  let maskOfFn : (Fin 33 → Fin 256) → List UInt8 := fun x => List.ofFn fun i => UInt8.ofNat (x i)
  let f : (Fin 33 → Fin 256) → Fin (2 ^ 256) := fun x =>
    ⟨(outerRoot [] (maskOfFn x) index.digest).value, Sp800185Cshake256.hash_digest_lt_two_pow_256 _ _⟩
  obtain ⟨x, y, ne, eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  apply ne
  have roots : outerRoot [] (maskOfFn x) index.digest = outerRoot [] (maskOfFn y) index.digest := by
    have hv := congrArg Fin.val eq
    simp only [f] at hv
    revert hv
    generalize outerRoot [] (maskOfFn x) index.digest = r₁
    generalize outerRoot [] (maskOfFn y) index.digest = r₂
    rintro hv; cases r₁; cases r₂; simp_all
  have masks : maskOfFn x = maskOfFn y := by
    rw [← recovers [] ([], 0) (maskOfFn x) index, ← recovers [] ([], 0) (maskOfFn y) index, factors, factors, roots]
  funext i
  have := congrArg (fun l => (l[i.val]?).map UInt8.toNat) masks
  simp only [maskOfFn, List.getElem?_ofFn, i.isLt, Option.map_some, UInt8.toNat_ofNat] at this
  simp at this
  exact Fin.ext this

/-- The mask itself, as a service, is refused. -/
theorem maskServe_refuted {Leak : Type} (leak : Index wire → Leak) :
    ¬ ServesWithin wire leak (fun _ _ mask _ => mask) :=
  recoverable_refuted wire leak _ id fun _ _ _ _ => rfl

/-! ## The adaptive run -/

/-- **The adaptive run** (newest first): birth from `store`, then `rounds`
rounds, each patch chosen by `next` from the items served so far. A refused
patch leaves the cell as it was and serves nothing new; refusal is a function of
the patch and the public wire alone (`KeptCell.accept_isSome_iff`), so a
strategy computes it itself. -/
def arun {Item : Type} (serve : Serve wire Item) (params : Params wire) (store : Store (CanonicalCellRegistry.layout kind))
    (next : List Item → List (KeptCell.Write (kind := kind))) : Nat → Option (List (KeptCell wire))
  | 0 => (birth wire params store).map fun cell => [cell]
  | rounds + 1 => (arun serve params store next rounds).bind fun cells =>
      match cells with
      | cell :: _ => some ((cell.accept (next (cells.map (KeptCell.served serve)))).elim cells fun n => n :: cells)
      | [] => none

/-- The item of a version served with the substituted mask `masks.getD version []`. -/
def substServed {Item : Type} (serve : Serve wire Item) (masks : List (List UInt8)) (cell : KeptCell wire) : Item :=
  serve cell.ctx (cell.params.cell, cell.version) (masks.getD cell.version []) cell.index

/-- **The run with masks substituted**: the same adaptive run, each version's
item served with `masks.getD version []` in place of the cell's own mask. -/
def srun {Item : Type} (serve : Serve wire Item) (params : Params wire) (store : Store (CanonicalCellRegistry.layout kind))
    (next : List Item → List (KeptCell.Write (kind := kind))) (masks : List (List UInt8)) :
    Nat → Option (List (KeptCell wire))
  | 0 => (birth wire params store).map fun cell => [cell]
  | rounds + 1 => (srun serve params store next masks rounds).bind fun cells =>
      match cells with
      | cell :: _ => some ((cell.accept (next (cells.map (substServed wire serve masks)))).elim cells
          fun n => n :: cells)
      | [] => none

/-- The transcript of the substituted run: a function of the mask list. -/
def transcript {Item : Type} (serve : Serve wire Item) (params : Params wire)
    (store : Store (CanonicalCellRegistry.layout kind)) (next : List Item → List (KeptCell.Write (kind := kind)))
    (masks : List (List UInt8)) (rounds : Nat) : Option (List Item) :=
  (srun wire serve params store next masks rounds).map (·.map (substServed wire serve masks))

/-- **The real run is the substituted run** at the masks the custody function
gives versions `0 … rounds`: the two are twins cell by cell (one public
parameter set, versions and kept index), they serve the same items, every
version is at most `rounds`, and every strategy runs to the end (a refusal on
one side is a refusal on the other: it depends on the patch alone). The masks
influence the patches only through the items, and the items only through
`masks`. -/
theorem arun_srun {Item : Type} (serve : Serve wire Item) {p base : Params wire}
    (same : p.cell = base.cell ∧ p.blinding = base.blinding)
    {store : Store (CanonicalCellRegistry.layout kind)} {next : List Item → List (KeptCell.Write (kind := kind))}
    (masks : List (List UInt8)) (born : (birth wire p store).isSome) :
    ∀ rounds, (∀ v ≤ rounds, masks.getD v [] = (wire.valueStream p.blinding.space).encode (p.prf v)) →
      ∃ cells cells₀, arun wire serve p store next rounds = some cells ∧
        srun wire serve base store next masks rounds = some cells₀ ∧
        List.Forall₂ KeptCell.Twin cells cells₀ ∧
        cells.map (KeptCell.served serve) = cells₀.map (substServed wire serve masks) ∧
        cells ≠ [] ∧ (∀ c ∈ cells, c.version ≤ rounds) ∧ History wire cells ∧ ∀ c ∈ cells, c.params = p
  | 0, hm => by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp born
      obtain ⟨c₀, hc₀, twin⟩ := birth_twin wire same hc
      obtain ⟨v0, pc⟩ := birth_version wire hc
      have hist := History.birth hc
      have mask := History.masks_of_params wire hist (p := p) (by simp [pc]) c (List.mem_singleton_self _)
      refine ⟨[c], [c₀], by simp [arun, hc], by simp [srun, hc₀], .cons twin .nil, ?_, by simp, by simp [v0], hist,
        by simp [pc]⟩
      simp only [List.map_cons, List.map_nil, KeptCell.served, substServed, List.cons.injEq, and_true]
      rw [twin.ctx, twin.1, twin.2.2, ← twin.2.1, mask, v0, hm 0 le_rfl]
  | rounds + 1, hm => by
      obtain ⟨cells, cells₀, ha, hs, twins, items, nonempty, versions, hist, hp⟩ :=
        arun_srun serve same (next := next) masks born rounds (fun v hv => hm v (by omega))
      match cells, cells₀, twins with
      | c :: rest, c₀ :: rest₀, .cons twin restTwins =>
        have hv : c.version ≤ rounds := versions c (List.mem_cons_self ..)
        have patch : (c₀ :: rest₀).map (substServed wire serve masks) = (c :: rest).map (KeptCell.served serve) :=
          items.symm
        have refusal : (c₀.accept (next ((c :: rest).map (KeptCell.served serve)))).isSome =
            (c.accept (next ((c :: rest).map (KeptCell.served serve)))).isSome := by
          rw [Bool.eq_iff_iff, KeptCell.accept_isSome_iff, KeptCell.accept_isSome_iff]
        cases hn : c.accept (next ((c :: rest).map (KeptCell.served serve))) with
        | none =>
          have hn₀ : c₀.accept (next ((c :: rest).map (KeptCell.served serve))) = none := by
            rw [hn, Option.isSome_none] at refusal; exact Option.not_isSome_iff_eq_none.mp (by rw [refusal]; decide)
          refine ⟨c :: rest, c₀ :: rest₀, ?_, ?_, .cons twin restTwins, items, nonempty,
            fun x member => by have := versions x member; omega, hist, hp⟩
          · simp only [arun, ha, Option.bind_some, hn, Option.elim]
          · simp only [srun, hs, Option.bind_some]
            rw [patch, hn₀]; rfl
        | some n =>
          obtain ⟨n₀, hn₀, twinN⟩ := KeptCell.accept_twin twin hn
          obtain ⟨nv, np, _, _, _⟩ := KeptCell.accept_spec hn
          have hist' := History.accept hist hn
          have params' : ∀ x ∈ n :: c :: rest, x.params = p := by
            intro x member
            rcases List.mem_cons.mp member with same | member
            · rw [same, np]; exact hp c (List.mem_cons_self ..)
            · exact hp x member
          refine ⟨n :: c :: rest, n₀ :: c₀ :: rest₀, ?_, ?_, .cons twinN (.cons twin restTwins), ?_, by simp,
            ?_, hist', params'⟩
          · simp only [arun, ha, Option.bind_some, hn, Option.elim]
          · simp only [srun, hs, Option.bind_some]
            rw [patch, hn₀]; rfl
          · show n.served serve :: (c :: rest).map (KeptCell.served serve) =
              substServed wire serve masks n₀ :: (c₀ :: rest₀).map (substServed wire serve masks)
            rw [items]
            congr 1
            have mask := History.masks_of_params wire hist' params' n (List.mem_cons_self ..)
            simp only [KeptCell.served, substServed]
            rw [twinN.ctx, twinN.1, twinN.2.2, ← twinN.2.1, mask, nv, hm (c.version + 1) (by omega)]
          · intro x member
            rcases List.mem_cons.mp member with same | member
            · rw [same, nv]; omega
            · have := versions x member; omega

/-- A run publishes one chain: at most one accepted successor per version.
When the hop is linked to the deployed host, "the host's accepted set is
exactly this run" (`PublishesRun`) becomes its premise. -/
def PublishesRun (accepted : KeptCell wire → Prop) (cells : List (KeptCell wire)) : Prop :=
  ∀ c, accepted c ↔ c ∈ cells

theorem PublishesRun.atMostOneSuccessor {accepted : KeptCell wire → Prop} {cells : List (KeptCell wire)}
    (publishes : PublishesRun wire accepted cells) (history : History wire cells) : AtMostOneSuccessor wire accepted := by
  intro c c' hc hc' sameParams sameVersion
  exact History.atMostOneSuccessor wire history c c' ((publishes c).mp hc) ((publishes c').mp hc') sameParams
    sameVersion

/-- The cell parameters under key `k`: the base with `prf := sample ∘ keyed k`. -/
def keyedParams {m keys : Nat} (base : Params wire)
    (sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space)
    (keyed : Fin keys → Nat → Fin (m + 1)) (k : Fin keys) : Params wire :=
  { base with prf := fun v => sample v (keyed k v) }

/-- **The keyed parameters admit a custody codec** under a kind-level decode whenever the custody
encoding is exact for it: the custody value of version `v` and secret `x` decodes to the cell,
`v` and `secretOf x`. Then under every key the blinding value of version `v` decodes to
`(cell, v, secretOf (keyed k v))`, whether or not the keyed function repeats a value, and the
hiding argument's `λ` is the entropy of `secretOf` alone. -/
def keyedCodec {m keys : Nat} (base : Params wire)
    (sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space)
    (keyed : Fin keys → Nat → Fin (m + 1)) (k : Fin keys)
    (decode : CustodyDecode) (secretOf : Fin (m + 1) → List UInt8)
    (exact : ∀ v x, decode ((wire.valueStream base.blinding.space).encode (sample v x)) = some (base.cell, v, secretOf x)) :
    CustodyCodec wire decode (keyedParams wire base sample keyed k) where
  secret v := secretOf (keyed k v)
  exact v := exact v (keyed k v)

/-- The masks of versions `0 … rounds` under a mask function. -/
def maskList {m : Nat} (encodeMask : Nat → Fin (m + 1) → List UInt8) (rounds : Nat) (f : Nat → Fin (m + 1)) :
    List (List UInt8) :=
  (List.range (rounds + 1)).map fun v => encodeMask v (f v)

/-- **A key's real transcript is the substituted transcript of its masks.** -/
theorem arun_transcript {m keys : Nat} {Item : Type} (keyed : Fin keys → Nat → Fin (m + 1)) (base : Params wire)
    (sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space)
    (encodeMask : Nat → Fin (m + 1) → List UInt8)
    (encodes : ∀ v x, (wire.valueStream base.blinding.space).encode (sample v x) = encodeMask v x)
    (serve : Serve wire Item) (rounds : Nat) (store : Store (CanonicalCellRegistry.layout kind))
    (next : List Item → List (KeptCell.Write (kind := kind))) (born : (birth wire base store).isSome) (k : Fin keys) :
    (arun wire serve (keyedParams wire base sample keyed k) store next rounds).map (·.map (KeptCell.served serve)) =
      transcript wire serve base store next (maskList encodeMask rounds (keyed k)) rounds := by
  have bornK : (birth wire (keyedParams wire base sample keyed k) store).isSome := by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp born
    obtain ⟨c₂, hc₂, _⟩ := birth_twin wire (p₁ := base) (p₂ := keyedParams wire base sample keyed k)
      ⟨rfl, rfl⟩ hc
    simp [hc₂]
  obtain ⟨cells, cells₀, ha, hs, _, items, _⟩ :=
    arun_srun wire serve (p := keyedParams wire base sample keyed k) (base := base) (next := next)
      ⟨rfl, rfl⟩ (maskList encodeMask rounds (keyed k)) bornK rounds (fun v hv => by
        simp only [maskList, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (by omega : v < rounds + 1), Option.map_some, Option.getD_some]
        exact (encodes _ _).symm)
  rw [ha, transcript, hs]
  simp only [Option.map_some, items]

/-- **The receiver's PRF hop** (`BlindedCellHiding.HybridReduction`'s first
antecedent at `fNum/den := num/den`), against an adaptive strategy. Each
strategy and world bit choose the birth store and, round by round, the next
patch from the items served so far; the custody function alone varies with the
key tape (`keyedParams`). For `rounds` rounds every version is in `0 … rounds`
whatever is chosen, so the window does not depend on the world bit. `reduction`
is the reduction's efficiency obligation: the composed distinguisher (the
strategy, the simulated host on given masks, the game) is in the PRF's
efficiency class whenever the strategy is budgeted. (i) Every
key's real transcript is `transcript` of its masks on the window. (ii) The game
on the real transcript and on `transcript` of the ideal function's masks are at
most `num/den` apart. (iii) The ideal's masks on the window are the tape's own
independent tuple. -/
theorem receiver_prf_hop {m keys num den : Nat} {Strategy Item : Type}
    (keyed : Fin keys → Nat → Fin (m + 1)) (budgetedPrf : ((Nat → Fin (m + 1)) → Bool) → Prop)
    (base : Params wire) (sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space)
    (encodeMask : Nat → Fin (m + 1) → List UInt8)
    (encodes : ∀ v x, (wire.valueStream base.blinding.space).encode (sample v x) = encodeMask v x)
    (serve : Serve wire Item) (rounds : Nat)
    (store : Strategy → Bool → Store (CanonicalCellRegistry.layout kind))
    (next : Strategy → Bool → List Item → List (KeptCell.Write (kind := kind)))
    (born : ∀ a b, (birth wire base (store a b)).isSome)
    (prf : CustodyPrf m keys num den (List.range (rounds + 1)) keyed budgetedPrf)
    (game : Strategy → Bool → Option (List Item) → Bool) (legal budgeted : Strategy → Prop)
    (reduction : ∀ a, legal a → budgeted a → ∀ b,
      budgetedPrf fun f => game a b (transcript wire serve base (store a b) (next a b) (maskList encodeMask rounds f)
        rounds)) :
    (∀ a b k, (arun wire serve (keyedParams wire base sample keyed k) (store a b) (next a b) rounds).map
        (·.map (KeptCell.served serve)) =
      transcript wire serve base (store a b) (next a b) (maskList encodeMask rounds (keyed k)) rounds) ∧
    (∀ a, legal a → budgeted a → ∀ b,
      GapAtMost (keys * funs m (List.range (rounds + 1))) num den
        (fun t => game a b ((arun wire serve (keyedParams wire base sample keyed (split t).1) (store a b) (next a b)
          rounds).map (·.map (KeptCell.served serve))))
        (fun t => game a b (transcript wire serve base (store a b) (next a b)
          (maskList encodeMask rounds (idealFn m (List.range (rounds + 1)) (split t).2)) rounds))) ∧
    ∀ (t : Fin (funs m (List.range (rounds + 1)))) (i : Fin (List.range (rounds + 1)).length),
      idealFn m (List.range (rounds + 1)) t (List.range (rounds + 1))[i] = finFunctionFinEquiv.symm t i := by
  have real : ∀ a b k, (arun wire serve (keyedParams wire base sample keyed k) (store a b) (next a b) rounds).map
      (·.map (KeptCell.served serve)) =
      transcript wire serve base (store a b) (next a b) (maskList encodeMask rounds (keyed k)) rounds :=
    fun a b k => arun_transcript wire keyed base sample encodeMask encodes serve rounds (store a b) (next a b)
      (born a b) k
  refine ⟨real, fun a la ba b => ?_, fun t i => Custody.idealFn_window m List.nodup_range t i⟩
  have gap := prf.2 _ (reduction a la ba b)
  simp only [real]
  exact gap

/-- **The hop through the host's view**: given the view's factorization `g`
through the served items (the witness of `ViewThroughServe`), a game on
whatever readers see of the run is a game on its transcript; `reduction` is
required for that `g` only (asking it for every `g` would put inefficient
compositions in the budget). -/
theorem receiver_prf_hop_view {m keys num den : Nat} {Strategy Item View : Type}
    (keyed : Fin keys → Nat → Fin (m + 1)) (budgetedPrf : ((Nat → Fin (m + 1)) → Bool) → Prop)
    (base : Params wire) (sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space)
    (encodeMask : Nat → Fin (m + 1) → List UInt8)
    (encodes : ∀ v x, (wire.valueStream base.blinding.space).encode (sample v x) = encodeMask v x)
    (serve : Serve wire Item) (view : List (KeptCell wire) → View) (g : List Item → View)
    (factors : ∀ cells, view cells = g (cells.map (KeptCell.served serve)))
    (rounds : Nat)
    (store : Strategy → Bool → Store (CanonicalCellRegistry.layout kind))
    (next : Strategy → Bool → List Item → List (KeptCell.Write (kind := kind)))
    (born : ∀ a b, (birth wire base (store a b)).isSome)
    (prf : CustodyPrf m keys num den (List.range (rounds + 1)) keyed budgetedPrf)
    (game : Strategy → Bool → Option View → Bool) (legal budgeted : Strategy → Prop)
    (reduction : ∀ a, legal a → budgeted a → ∀ b,
      budgetedPrf fun f => game a b ((transcript wire serve base (store a b) (next a b)
        (maskList encodeMask rounds f) rounds).map g)) :
    ∀ a, legal a → budgeted a → ∀ b,
      GapAtMost (keys * funs m (List.range (rounds + 1))) num den
        (fun t => game a b ((arun wire serve (keyedParams wire base sample keyed (split t).1) (store a b) (next a b)
          rounds).map view))
        (fun t => game a b ((transcript wire serve base (store a b) (next a b)
          (maskList encodeMask rounds (idealFn m (List.range (rounds + 1)) (split t).2)) rounds).map g)) := by
  intro a la ba b
  have hop := (receiver_prf_hop wire keyed budgetedPrf base sample encodeMask encodes serve rounds store next born
    prf (fun a b o => game a b (o.map g)) legal budgeted reduction).2.1 a la ba b
  have viewed : ∀ o : Option (List (KeptCell wire)), o.map view = (o.map (·.map (KeptCell.served serve))).map g := by
    intro o; cases o <;> simp [factors]
  simp only [viewed]
  exact hop

/-! ## The hiding goal at the receiver -/

open Minidregg.Kernel.ResourceObservationAdmission (Visible)

/-- **An attack**: the two candidate worlds' birth store and adaptive patch
choices (a world is `false` or `true`), and the attacker's own decision on the
view. The decision never sees the world bit; it is all the attacker outputs. -/
structure Attack (base : Params wire) (Item View : Type) where
  store : Bool → Store (CanonicalCellRegistry.layout kind)
  next : Bool → List Item → List (KeptCell.Write (kind := kind))
  decide : Option View → Bool
  born : ∀ b, (birth wire base (store b)).isSome

/-- **One deployment of the receiver's hiding game**: the custody function and
its mask encoding, what is served and the reader's view through it (`g`,
`factors`: the `ViewThroughServe` witness), the number of rounds, and the
reader's authorized scope `fields`, from which the same-leakage rule is
defined. The attacks are `Attack base Item View`. -/
structure HidingSetting (m keys : Nat) (Item View : Type) where
  keyed : Fin keys → Nat → Fin (m + 1)
  base : Params wire
  sample : Nat → Fin (m + 1) → (CanonicalCellRegistry.layout kind).Value base.blinding.space
  encodeMask : Nat → Fin (m + 1) → List UInt8
  encodes : ∀ v x, (wire.valueStream base.blinding.space).encode (sample v x) = encodeMask v x
  serve : Serve wire Item
  view : List (KeptCell wire) → View
  g : List Item → View
  factors : ∀ cells, view cells = g (cells.map (KeptCell.served serve))
  rounds : Nat
  fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField)

/-! ### Stores under writes no reader sees -/

/-- A write at an address the scope does not see leaves the reader's view. -/
theorem filter_set_invisible {fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField)}
    (S : Store (CanonicalCellRegistry.layout kind)) (a : Address (CanonicalCellRegistry.layout kind))
    (v : Option ((CanonicalCellRegistry.layout kind).Value a.1)) (hidden : ¬ Visible fields kind a) :
    DFinsupp.filter (Visible fields kind) (S.set a v) = DFinsupp.filter (Visible fields kind) S := by
  refine DFinsupp.ext fun b => ?_
  simp only [DFinsupp.filter_apply]
  split
  · rename_i seen
    have ne : b ≠ a := fun h => hidden (h ▸ seen)
    exact Store.set_ne S a v b ne
  · rfl

theorem applyPatch_invisible {fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField)} :
    ∀ (S : Store (CanonicalCellRegistry.layout kind)) (patch : List (KeptCell.Write (kind := kind))),
      (∀ w ∈ patch, ¬ Visible fields kind w.1) →
        DFinsupp.filter (Visible fields kind) (KeptCell.applyPatch S patch) = DFinsupp.filter (Visible fields kind) S
  | _, [], _ => rfl
  | S, w :: rest, hidden => by
      show DFinsupp.filter _ (KeptCell.applyPatch (S.set w.1 w.2) rest) = _
      rw [applyPatch_invisible _ rest (fun x hx => hidden x (List.mem_cons_of_mem _ hx)),
        filter_set_invisible S w.1 w.2 (hidden w (List.mem_cons_self ..))]

/-- No scope sees the blinding address. -/
theorem blinding_invisible (fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField)) (p : Params wire) :
    ¬ Visible fields kind p.blinding.address := by
  rintro ⟨_, visible⟩
  have : CanonicalCellRegistry.isBlinding kind p.blinding.address = true :=
    (isBlinding_iff p.selected _).mpr p.blinding.isBlinding.symm
  rw [this] at visible; cases visible

theorem birth_store {p : Params wire} {S : Store (CanonicalCellRegistry.layout kind)} {c : KeptCell wire}
    (born : birth wire p S = some c) : c.fit.store = S.set p.blinding.address (some (p.prf 0)) := by
  unfold birth at born
  split at born
  · rename_i unmasked
    obtain ⟨fit, admitted, rfl⟩ := Option.map_eq_some_iff.mp born
    unfold admit at admitted
    split at admitted
    · cases admitted; rfl
    · cases admitted
  · cases born

/-- **A hidden patch**: every write is at an address the reader's scope does not
see, fits the gate and avoids the blinding address (so it is accepted). -/
def HiddenPatch (fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField))
    (patch : List (KeptCell.Write (kind := kind))) : Prop :=
  ∀ w ∈ patch, ¬ Visible fields kind w.1 ∧ addressFits 256 kind w.1 = true ∧ ¬ some w.1 = wire.blinding

/-- A run repeating one hidden patch: every round is accepted, and every
version's reader view is the birth store's. -/
theorem hidden_run {Item : Type} (serve : Serve wire Item) (fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField))
    {p : Params wire} {S : Store (CanonicalCellRegistry.layout kind)} (born : (birth wire p S).isSome)
    {patch : List (KeptCell.Write (kind := kind))} (hidden : HiddenPatch wire fields patch) :
    ∀ r, ∃ cells, arun wire serve p S (fun _ => patch) r = some cells ∧ cells.length = r + 1 ∧
      ∀ c ∈ cells, DFinsupp.filter (Visible fields kind) c.fit.store = DFinsupp.filter (Visible fields kind) S
  | 0 => by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp born
      refine ⟨[c], by simp [arun, hc], rfl, ?_⟩
      intro x member
      rw [List.mem_singleton.mp member, birth_store wire hc]
      exact filter_set_invisible S _ _ (blinding_invisible wire fields p)
  | r + 1 => by
      obtain ⟨cells, ha, len, views⟩ := hidden_run serve fields born hidden r
      match cells, len with
      | c :: rest, len =>
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
          ((KeptCell.accept_isSome_iff c patch).mpr fun w hw => ⟨(hidden w hw).2.1, (hidden w hw).2.2⟩)
        obtain ⟨_, _, _, hs, _⟩ := KeptCell.accept_spec hn
        refine ⟨n :: c :: rest, by simp only [arun, ha, Option.bind_some, hn, Option.elim], by simp [len], ?_⟩
        intro x member
        rcases List.mem_cons.mp member with same | member
        · rw [same, hs, applyPatch_invisible _ patch (fun w hw => (hidden w hw).1),
            filter_set_invisible _ _ _ (blinding_invisible wire fields c.params)]
          exact views c (List.mem_cons_self ..)
        · exact views x member

/-- Two different values at one address give different stores. -/
theorem single_differ (S : Store (CanonicalCellRegistry.layout kind)) (a : Address (CanonicalCellRegistry.layout kind))
    {v₀ v₁ : (CanonicalCellRegistry.layout kind).Value a.1} (ne : v₀ ≠ v₁) :
    KeptCell.applyPatch S [⟨a, some v₀⟩] ≠ KeptCell.applyPatch S [⟨a, some v₁⟩] := by
  intro same
  have := DFunLike.congr_fun same a
  simp only [KeptCell.applyPatch, List.foldl_cons, List.foldl_nil, Store.set_eq, Option.some.injEq] at this
  exact ne this

/-- One write at a hidden, fitting, non-blinding address is a hidden patch. -/
theorem single_hidden (fields : Option (Finset Minidregg.Theory.TypedAuthorization.CellField))
    {a : Address (CanonicalCellRegistry.layout kind)} (v : (CanonicalCellRegistry.layout kind).Value a.1)
    (hidden : ¬ Visible fields kind a) (fits : addressFits 256 kind a = true) (off : ¬ some a = wire.blinding) :
    HiddenPatch wire fields [⟨a, some v⟩] := by
  intro w member
  rw [List.mem_singleton.mp member]
  exact ⟨hidden, fits, off⟩

/-- **Concretely**: in `PrivateCellView.Witness`'s declared cell, the slot-2
field is hidden from the slot-1 reader, fits the gate and is not the blinding
address, so `[⟨a2, some 5⟩]` and `[⟨a2, some 7⟩]` are hidden patches with
different effects. -/
theorem witness_hidden_write :
    ¬ Visible Witness.slot1 .declaredObject Witness.a2 ∧ addressFits 256 .declaredObject Witness.a2 = true ∧
      ¬ some Witness.a2 = Witness.wire.blinding ∧ (5 : Int) ≠ 7 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

namespace HidingSetting

variable {wire} {m keys : Nat} {Item View : Type} (setting : HidingSetting wire m keys Item View)

/-- The attacks of this deployment. -/
abbrev Strategy := Attack wire setting.base Item View

/-- The window of versions a run of `rounds` rounds uses. -/
abbrev window : List Nat := List.range (setting.rounds + 1)

/-- The joint tape: the custody key and the ideal function. -/
abbrev tapes : Nat := keys * funs m setting.window

/-- **The real experiment**: the attacker's decision on the reader's view of the
adaptive run in world `b`, under the tape's custody key. This is the `run` of
the hiding goal. -/
def real (a : setting.Strategy) (b : Bool) (t : Fin setting.tapes) : Bool :=
  a.decide ((arun wire setting.serve (keyedParams wire setting.base setting.sample setting.keyed (split t).1)
    (a.store b) (a.next b) setting.rounds).map setting.view)

/-- **The uniform experiment**: the same decision over the ideal function's masks. -/
def uniform (a : setting.Strategy) (b : Bool) (t : Fin setting.tapes) : Bool :=
  a.decide ((transcript wire setting.serve setting.base (a.store b) (a.next b)
    (maskList setting.encodeMask setting.rounds (idealFn m setting.window (split t).2)) setting.rounds).map setting.g)

/-- The composed distinguisher of the PRF reduction for one attack and world. -/
def composed (a : setting.Strategy) (b : Bool) (f : Nat → Fin (m + 1)) : Bool :=
  a.decide ((transcript wire setting.serve setting.base (a.store b) (a.next b)
    (maskList setting.encodeMask setting.rounds f) setting.rounds).map setting.g)

/-- The view world `b` publishes when the masks are the list `masks`. -/
def worldView (a : setting.Strategy) (b : Bool) (masks : List (List UInt8)) : Option View :=
  (transcript wire setting.serve setting.base (a.store b) (a.next b) masks setting.rounds).map setting.g

/-- The reader-authorized view of one version: `narrowPacked`'s store. -/
def readerView (c : KeptCell wire) : Store (CanonicalCellRegistry.layout kind) :=
  DFinsupp.filter (Visible setting.fields kind) c.fit.store

/-- **The same-leakage rule** (`BlindedCellHiding.OnlineSameLeakage` at the
receiver: the prefix is the round, the paired state the two worlds' runs, the
release the reader's authorized view of every published version): under every
custody key and at every round, the two worlds publish versions whose
reader-authorized views agree, version by version. What an opening reveals
beyond `Visible` (an honest reveal that stops early exposes nodes of other
classes) is not in `readerView`: it is pushed into the `zk` hybrid, whose
simulator sees only this leakage. -/
def Legal (a : setting.Strategy) : Prop :=
  ∀ (k : Fin keys) r, r ≤ setting.rounds →
    (arun wire setting.serve (keyedParams wire setting.base setting.sample setting.keyed k) (a.store false)
      (a.next false) r).map (·.map setting.readerView) =
    (arun wire setting.serve (keyedParams wire setting.base setting.sample setting.keyed k) (a.store true)
      (a.next true) r).map (·.map setting.readerView)

/-- The store world `b`'s first accepted version holds after the patch chosen
on `items`. -/
def effect (a : setting.Strategy) (b : Bool) (items : List Item) : Option (Store (CanonicalCellRegistry.layout kind)) :=
  (birth wire setting.base (a.store b)).bind fun c => (c.accept (a.next b items)).map (·.fit.store)

/-- **The goal's hidden difference**: on some items both worlds' patches are
accepted and their effects on the store differ (operation histories, not patch
syntax). -/
def HiddenDiff (a : setting.Strategy) : Prop :=
  ∃ items, (setting.effect a false items).isSome ∧ (setting.effect a true items).isSome ∧
    setting.effect a false items ≠ setting.effect a true items

/-- **The decoy-membership test**: is the view one of the candidate views? -/
def decoyTest [DecidableEq View] (decoys : List (Option View)) (v : Option View) : Bool := decoys.contains v

/-- **The goal's distinguishers**: attacks deciding whether the view is world
`true`'s view under some fixed exposed mask list (the attack a reader mounts
when the masks are known or absent). -/
def Distinguisher [DecidableEq View] (a : setting.Strategy) : Prop :=
  ∃ masks₀ : List (List UInt8), a.decide = decoyTest [setting.worldView a true masks₀]

/-- **The concrete challenge**: one birth store, patch `p₀` in world `false` and
`p₁` in world `true` at every round, decided by membership in world `true`'s
view under `masks₀`. -/
def pairAttack [DecidableEq View] (S : Store (CanonicalCellRegistry.layout kind)) (bornS : (birth wire setting.base S).isSome)
    (p₀ p₁ : List (KeptCell.Write (kind := kind))) (masks₀ : List (List UInt8)) : setting.Strategy :=
  ⟨fun _ => S, fun b _ => cond b p₁ p₀,
    decoyTest [(transcript wire setting.serve setting.base S (fun _ => p₁) masks₀ setting.rounds).map setting.g],
    fun _ => bornS⟩

theorem pairAttack_distinguisher [DecidableEq View] (S : Store (CanonicalCellRegistry.layout kind))
    (bornS : (birth wire setting.base S).isSome) (p₀ p₁ : List (KeptCell.Write (kind := kind)))
    (masks₀ : List (List UInt8)) : setting.Distinguisher (setting.pairAttack S bornS p₀ p₁ masks₀) :=
  ⟨masks₀, rfl⟩

/-- **The pair is legal** when both patches are hidden: every version of either
world shows the reader the birth store's view. -/
theorem pairAttack_legal [DecidableEq View] (S : Store (CanonicalCellRegistry.layout kind))
    (bornS : (birth wire setting.base S).isSome) {p₀ p₁ : List (KeptCell.Write (kind := kind))}
    (hidden₀ : HiddenPatch wire setting.fields p₀) (hidden₁ : HiddenPatch wire setting.fields p₁)
    (masks₀ : List (List UInt8)) : setting.Legal (setting.pairAttack S bornS p₀ p₁ masks₀) := by
  intro k r _
  have born : (birth wire (keyedParams wire setting.base setting.sample setting.keyed k) S).isSome := by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp bornS
    obtain ⟨c₂, hc₂, _⟩ := birth_twin wire (p₁ := setting.base)
      (p₂ := keyedParams wire setting.base setting.sample setting.keyed k) ⟨rfl, rfl⟩ hc
    simp [hc₂]
  have flat : ∀ {patch : List (KeptCell.Write (kind := kind))}, HiddenPatch wire setting.fields patch →
      (arun wire setting.serve (keyedParams wire setting.base setting.sample setting.keyed k) S (fun _ => patch) r).map
        (·.map setting.readerView) = some (List.replicate (r + 1) (DFinsupp.filter (Visible setting.fields kind) S)) := by
    intro patch hidden
    obtain ⟨cells, ha, len, views⟩ := hidden_run wire setting.serve setting.fields born hidden r
    rw [ha, Option.map_some, Option.some.injEq, List.eq_replicate_iff]
    refine ⟨by simp [len], fun x member => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp member
    exact views c hc
  exact (flat hidden₀).trans (flat hidden₁).symm

/-- **The pair has a hidden difference** when both patches are hidden and their
effects on the post-birth store differ. -/
theorem pairAttack_hiddenDiff [DecidableEq View] (S : Store (CanonicalCellRegistry.layout kind))
    (bornS : (birth wire setting.base S).isSome) {p₀ p₁ : List (KeptCell.Write (kind := kind))}
    (hidden₀ : HiddenPatch wire setting.fields p₀) (hidden₁ : HiddenPatch wire setting.fields p₁)
    (differ : ∀ c : KeptCell wire, birth wire setting.base S = some c →
      KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₀ ≠
        KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₁)
    (masks₀ : List (List UInt8)) : setting.HiddenDiff (setting.pairAttack S bornS p₀ p₁ masks₀) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp bornS
  have accepts : ∀ {patch : List (KeptCell.Write (kind := kind))}, HiddenPatch wire setting.fields patch →
      ∃ n, c.accept patch = some n ∧ n.fit.store =
        KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) patch := by
    intro patch hidden
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
      ((KeptCell.accept_isSome_iff c patch).mpr fun w hw => ⟨(hidden w hw).2.1, (hidden w hw).2.2⟩)
    exact ⟨n, hn, (KeptCell.accept_spec hn).2.2.2.1⟩
  obtain ⟨n₀, hn₀, hs₀⟩ := accepts hidden₀
  obtain ⟨n₁, hn₁, hs₁⟩ := accepts hidden₁
  refine ⟨[], ?_, ?_, ?_⟩ <;> simp only [effect, pairAttack, hc, Option.bind_some, cond, hn₀, hn₁, Option.map_some,
    Option.isSome_some]
  rw [Ne, Option.some.injEq, hs₀, hs₁]
  exact differ c hc

/-- The real experiment's view is the substituted transcript of the tape key's masks. -/
theorem real_eq (a : setting.Strategy) (b : Bool) (t : Fin setting.tapes) :
    setting.real a b t = a.decide ((transcript wire setting.serve setting.base (a.store b) (a.next b)
      (maskList setting.encodeMask setting.rounds (setting.keyed (split t).1)) setting.rounds).map setting.g) := by
  rw [← arun_transcript wire setting.keyed setting.base setting.sample setting.encodeMask setting.encodes setting.serve
    setting.rounds (a.store b) (a.next b) (a.born b) (split t).1, real]
  congr 1
  cases arun wire setting.serve (keyedParams wire setting.base setting.sample setting.keyed (split t).1) (a.store b)
    (a.next b) setting.rounds <;> simp [setting.factors]

/-- A service that does not read the mask gives a transcript that does not either. -/
theorem transcript_maskFree (maskFree : ∀ ctx pub mask mask' index, setting.serve ctx pub mask index = setting.serve ctx pub mask' index)
    (S : Store (CanonicalCellRegistry.layout kind)) (next : List Item → List (KeptCell.Write (kind := kind)))
    (masks masks' : List (List UInt8)) :
    transcript wire setting.serve setting.base S next masks setting.rounds =
      transcript wire setting.serve setting.base S next masks' setting.rounds := by
  have same : substServed wire setting.serve masks = substServed wire setting.serve masks' := by
    funext c; exact maskFree _ _ _ _ _
  have runs : ∀ r, srun wire setting.serve setting.base S next masks r = srun wire setting.serve setting.base S next masks' r := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => simp only [srun, ih, same]
  simp only [transcript, runs, same]

/-- **Teeth**: an unmasked service (one that does not read the mask: the legacy
fingerprint) refutes hiding at every bound below one against a legal budgeted
distinguisher whose two worlds' views separate. The decoy is world `true`'s
view under `masks₀`; with the mask unread, that is world `true`'s view under
every key, and world `false`'s view is never it. -/
theorem unmasked_refuted [DecidableEq View] {num den : Nat} (small : num < den)
    (maskFree : ∀ ctx pub mask mask' index, setting.serve ctx pub mask index = setting.serve ctx pub mask' index)
    (legal budgeted : setting.Strategy → Prop) (a : setting.Strategy) (la : legal a) (ba : budgeted a)
    (masks₀ : List (List UInt8)) (decides : a.decide = decoyTest [setting.worldView a true masks₀])
    (separated : setting.worldView a false masks₀ ≠ setting.worldView a true masks₀) :
    ¬ BlindedCellHiding.TranscriptHiding setting.tapes num den setting.real legal budgeted := by
  intro hides
  have view : ∀ b t, setting.real a b t = decoyTest [setting.worldView a true masks₀] (setting.worldView a b masks₀) := by
    intro b t
    rw [real_eq, decides]
    congr 1
    unfold worldView
    rw [transcript_maskFree setting maskFree _ _ _ masks₀]
  apply Minidregg.Theory.FiniteTapeGap.not_gapAtMost_of_separating small (left := setting.real a true) (right := setting.real a false)
  · intro t; rw [view]; simp [decoyTest]
  · intro t; rw [view]; simpa [decoyTest] using separated
  · exact (hides a la ba).symm

/-- **The receiver's hiding from the hybrids** (`BlindedCellHiding.TranscriptHiding`
of `real` at the hybrid composition's bound). The PRF hop is discharged here
(`receiver_prf_hop_view`) from `CustodyPrf` and the reduction's efficiency
obligation. The rest of the declared order stays as named open premises, which
jointly say "hiding with uniform masks": `zk`, the uniform-mask experiment
against one with simulated openings (`ServesWithin` is the deterministic case
after simulation); `rom`, that experiment against the ideal one with
independent uniform roots (the mask-guessing coupling, which needs
`ServesWithin`; `lambda` is the mask encoding's entropy in bits, and at the
use `versions = rounds + 1`); `identical`, that the ideal experiment does not
depend on the world. Forks are excluded by the run itself (one chain;
`PublishesRun` at the host). -/
theorem hiding_of_hybrids {num den lambda versions queries zNum : Nat}
    (budgetedPrf : ((Nat → Fin (m + 1)) → Bool) → Prop) (legal budgeted : setting.Strategy → Prop)
    (prf : CustodyPrf m keys num den setting.window setting.keyed budgetedPrf)
    (reduction : ∀ a, legal a → budgeted a → ∀ b, budgetedPrf (setting.composed a b))
    (someKey : 0 < keys) (denominator : 0 < den) (below : queries < 2 ^ lambda)
    (simulated ideal : setting.Strategy → Bool → Fin setting.tapes → Bool)
    (zk : ∀ a, legal a → budgeted a → ∀ b, GapAtMost setting.tapes zNum den (setting.uniform a b) (simulated a b))
    (rom : ∀ a, legal a → budgeted a → ∀ b,
      GapAtMost setting.tapes (versions * queries) (2 ^ lambda - queries) (simulated a b) (ideal a b))
    (identical : ∀ a, legal a → budgeted a → GapAtMost setting.tapes 0 1 (ideal a false) (ideal a true)) :
    BlindedCellHiding.TranscriptHiding setting.tapes
      (2 * (num + zNum) * (2 ^ lambda - queries) + 2 * versions * queries * den)
      (den * (2 ^ lambda - queries)) setting.real legal budgeted := by
  have positive : 0 < setting.tapes := Nat.mul_pos someKey (Nat.pow_pos (Nat.succ_pos _))
  have hop := receiver_prf_hop_view wire setting.keyed budgetedPrf setting.base setting.sample setting.encodeMask
    setting.encodes setting.serve setting.view setting.g setting.factors setting.rounds
    (fun (a : setting.Strategy) b => a.store b) (fun a b => a.next b) (fun a b => a.born b) prf
    (fun a _ v => a.decide v) legal budgeted reduction
  exact BlindedCellHiding.hybridReduction_holds setting.tapes lambda versions queries num zNum den setting.real
    setting.uniform simulated ideal legal budgeted positive denominator below
    (fun a la ba b => ⟨hop a la ba b, zk a la ba b, rom a la ba b⟩) identical

/-- **The receiver's hiding goal from the hybrids** (`BlindedCellHiding.RatchetHidingGoal`
of `real`), with every non-vacuity witness concrete: `legal` is the setting's
same-leakage rule `Legal`; the distinguishers are the decoy attacks on the other
world's view; the hidden difference compares the two worlds' accepted effects;
the hidden-choice witness is `pairAttack` with two hidden patches whose effects
differ, and it is proved legal (`pairAttack_legal`), not assumed. The budget
must admit every distinguisher. The hybrids `zk`, `rom`, `identical` stay open,
as in `hiding_of_hybrids`. -/
theorem hidingGoal_of_hybrids [DecidableEq View] {num den lambda versions queries zNum : Nat}
    (budgetedPrf : ((Nat → Fin (m + 1)) → Bool) → Prop) (budgeted : setting.Strategy → Prop)
    (prf : CustodyPrf m keys num den setting.window setting.keyed budgetedPrf)
    (reduction : ∀ a, setting.Legal a → budgeted a → ∀ b, budgetedPrf (setting.composed a b))
    (someKey : 0 < keys) (denominator : 0 < den) (below : queries < 2 ^ lambda)
    (small : 2 * (num + zNum) * (2 ^ lambda - queries) + 2 * versions * queries * den < den * (2 ^ lambda - queries))
    (meaningful : BlindedCellHiding.BudgetMeaningful budgeted setting.Distinguisher)
    (S : Store (CanonicalCellRegistry.layout kind)) (bornS : (birth wire setting.base S).isSome)
    (p₀ p₁ : List (KeptCell.Write (kind := kind)))
    (hidden₀ : HiddenPatch wire setting.fields p₀) (hidden₁ : HiddenPatch wire setting.fields p₁)
    (differ : ∀ c : KeptCell wire, birth wire setting.base S = some c →
      KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₀ ≠
        KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₁)
    (masks₀ : List (List UInt8))
    (simulated ideal : setting.Strategy → Bool → Fin setting.tapes → Bool)
    (zk : ∀ a, setting.Legal a → budgeted a → ∀ b,
      GapAtMost setting.tapes zNum den (setting.uniform a b) (simulated a b))
    (rom : ∀ a, setting.Legal a → budgeted a → ∀ b,
      GapAtMost setting.tapes (versions * queries) (2 ^ lambda - queries) (simulated a b) (ideal a b))
    (identical : ∀ a, setting.Legal a → budgeted a → GapAtMost setting.tapes 0 1 (ideal a false) (ideal a true)) :
    BlindedCellHiding.RatchetHidingGoal setting.tapes lambda versions queries num zNum den setting.real setting.Legal
      budgeted setting.HiddenDiff setting.Distinguisher :=
  ⟨denominator, below, small, meaningful,
    ⟨setting.pairAttack S bornS p₀ p₁ masks₀, setting.pairAttack_legal S bornS hidden₀ hidden₁ masks₀,
      setting.pairAttack_distinguisher S bornS p₀ p₁ masks₀,
      setting.pairAttack_hiddenDiff S bornS hidden₀ hidden₁ differ masks₀⟩,
    setting.hiding_of_hybrids budgetedPrf setting.Legal budgeted prf reduction someKey denominator below simulated
      ideal zk rom identical⟩

end HidingSetting

/-! ## A concrete deployment: premise inhabitation and teeth

The declared cell of `PrivateCellView.Witness` (wire `DeclaredEffectCell.wire`,
blinding `DeclaredEffectCell.blinding`), a store holding slot 1 and no mask, a
slot-1 reader, and worlds writing `5` or `7` at slot 2. -/

namespace Concrete

open Minidregg.Theory.AuthTrie (Entry lookup)

/-- Lookup agrees on permuted key-distinct entry lists. -/
theorem lookup_perm {K V : Type} [DecidableEq K] {l₁ l₂ : List (Entry K V)} (perm : l₁.Perm l₂)
    (nd : (l₁.map (·.1)).Nodup) (k : K) : lookup l₁ k = lookup l₂ k := by
  have char : ∀ {l : List (Entry K V)}, (l.map (·.1)).Nodup → ∀ v, lookup l k = some v ↔ ∃ b, (k, b, v) ∈ l := by
    intro l nd v
    unfold lookup
    constructor
    · intro h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      have mem := List.mem_of_find?_eq_some he
      have key : e.1 = k := by simpa using List.find?_some he
      exact ⟨e.2.1, by rw [← key]; exact mem⟩
    · rintro ⟨b, mem⟩
      obtain ⟨e, he⟩ : ∃ e, l.find? (fun e => e.1 = k) = some e := by
        cases h : l.find? (fun e => e.1 = k) with
        | none => exact absurd (List.find?_eq_none.mp h _ mem) (by simp)
        | some e => exact ⟨e, rfl⟩
      have emem := List.mem_of_find?_eq_some he
      have key : e.1 = k := by simpa using List.find?_some he
      have same : e = (k, b, v) := List.inj_on_of_nodup_map nd emem mem key
      rw [he, same]; rfl
  have nd₂ : (l₂.map (·.1)).Nodup := (perm.map _).nodup_iff.mp nd
  apply Option.ext
  intro v
  rw [char nd, char nd₂]
  exact exists_congr fun b => perm.mem_iff

abbrev W := Witness.wire

/-- The base parameters: the declared cell's own blinding, masks `prf v = v`. -/
def base : Params W where
  cell := []
  selected := Witness.selected
  blinding := DeclaredEffectCell.blinding
  prf := fun v => Int.ofNat v

/-- Slot 1 holds `5`; no mask. -/
def S : Store (CanonicalCellRegistry.layout .declaredObject) := (0 : Store _).set Witness.a1 (some (5 : Int))

def p₀ : List (KeptCell.Write (kind := .declaredObject)) := [⟨Witness.a2, some (5 : Int)⟩]
def p₁ : List (KeptCell.Write (kind := .declaredObject)) := [⟨Witness.a2, some (7 : Int)⟩]

theorem bornS : (birth W base S).isSome := by
  have gate : storeFits W S = true := storeFits_of_forall W fun a live => by
    by_cases h : a = Witness.a1
    · subst h; decide
    · exact absurd (by rw [S, Store.set_ne _ _ _ _ h]; rfl) live
  have unmasked : S base.blinding.address = none := by
    rw [S, Store.set_ne _ _ _ _ (by decide)]; rfl
  obtain ⟨c, born, _⟩ := birth_accepts W base gate unmasked
  simp [born]

theorem hidden₀ : HiddenPatch W Witness.slot1 p₀ :=
  single_hidden W Witness.slot1 (5 : Int) witness_hidden_write.1 witness_hidden_write.2.1 witness_hidden_write.2.2.1

theorem hidden₁ : HiddenPatch W Witness.slot1 p₁ :=
  single_hidden W Witness.slot1 (7 : Int) witness_hidden_write.1 witness_hidden_write.2.1 witness_hidden_write.2.2.1

theorem differ : ∀ c : KeptCell W, birth W base S = some c →
    KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₀ ≠
      KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₁ :=
  fun _ _ => single_differ _ _ (by decide : (5 : Int) ≠ 7)

/-- A deployment over `base` at one round, a slot-1 reader, one key, and any service. -/
def setting {Item : Type} (serve : Serve W Item) : HidingSetting W 0 1 Item (List Item) where
  keyed := fun _ _ => 0
  base := base
  sample := fun _ _ => (0 : Int)
  encodeMask := fun _ _ => (W.valueStream base.blinding.space).encode (0 : Int)
  encodes := fun _ _ => rfl
  serve := serve
  view := fun cells => cells.map (KeptCell.served serve)
  g := id
  factors := fun _ => rfl
  rounds := 1
  fields := Witness.slot1

/-- **Premise inhabitation of `hidingGoal_of_hybrids`** at the root service: the
store is born, both patches are hidden, their effects differ, and so the pair
attack is legal with a hidden difference. -/
theorem goalPremises_inhabited :
    (birth W (setting (rootServe W)).base S).isSome ∧ HiddenPatch W (setting (rootServe W)).fields p₀ ∧
      HiddenPatch W (setting (rootServe W)).fields p₁ ∧
      (∀ c : KeptCell W, birth W (setting (rootServe W)).base S = some c →
        KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₀ ≠
          KeptCell.applyPatch (c.fit.store.set c.params.blinding.address (some (c.params.prf (c.version + 1)))) p₁) ∧
      ∀ masks₀, (setting (rootServe W)).Legal ((setting (rootServe W)).pairAttack S bornS p₀ p₁ masks₀) ∧
        (setting (rootServe W)).HiddenDiff ((setting (rootServe W)).pairAttack S bornS p₀ p₁ masks₀) :=
  ⟨bornS, hidden₀, hidden₁, differ, fun masks₀ =>
    ⟨(setting (rootServe W)).pairAttack_legal S bornS hidden₀ hidden₁ masks₀,
      (setting (rootServe W)).pairAttack_hiddenDiff S bornS hidden₀ hidden₁ differ masks₀⟩⟩

/-- **The plaintext service**: the value bytes the kept index holds at slot 2,
read off the trie's entries; it does not read the mask (the archive of a
blinded cell's plaintext). -/
def plainServe : Serve W (Option (List UInt8)) := fun _ _ _ index => lookup index.trie.entries Witness.a2

theorem plain_of_holds {index : Index W} {store : Store (CanonicalCellRegistry.layout .declaredObject)}
    (holds : index.Holds (indexEntries W store)) :
    plainServe [] ([], 0) [] index = (store Witness.a2).map (valueBytes W Witness.a2) := by
  show lookup index.trie.entries Witness.a2 = _
  rw [lookup_perm holds index.nodup, Theory.AuthTrie.Cache.lookup_canon, indexExact W store Witness.a2,
    if_neg witness_hidden_write.2.2.1]

/-- The newest version's item in world `b` of the pair attack: slot 2's value bytes. -/
theorem plain_view (v : Int) (masks : List (List UInt8)) :
    ∃ rest, ((setting plainServe).worldView ⟨fun _ => S, fun _ _ => [⟨Witness.a2, some v⟩], fun _ => true, fun _ => bornS⟩
      true masks) = some (some (valueBytes W Witness.a2 v) :: rest) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp bornS
  have hidden : HiddenPatch W Witness.slot1 [⟨Witness.a2, some v⟩] :=
    single_hidden W Witness.slot1 v witness_hidden_write.1 witness_hidden_write.2.1 witness_hidden_write.2.2.1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
    ((KeptCell.accept_isSome_iff c _).mpr fun w hw => ⟨(hidden w hw).2.1, (hidden w hw).2.2⟩)
  have hs := (KeptCell.accept_spec hn).2.2.2.1
  refine ⟨[substServed W plainServe masks c], ?_⟩
  simp only [HidingSetting.worldView, transcript, setting, srun, hc, Option.map_some, Option.bind_some, hn,
    Option.elim, id, List.map_cons, List.map_nil]
  congr 2
  show plainServe [] ([], 0) [] n.index = _
  rw [plain_of_holds n.holds, hs]
  simp [KeptCell.applyPatch]

/-- **Teeth at the goal's own statement**: at the concrete deployment with the
plaintext service, `TranscriptHiding` of `real` fails at every bound below one,
with `legal := Legal` and any budget admitting the goal's distinguishers: the
pair attack is legal, a distinguisher, and separates. -/
theorem plain_refuted {num den : Nat} (small : num < den) (budgeted : (setting plainServe).Strategy → Prop)
    (meaningful : BlindedCellHiding.BudgetMeaningful budgeted (setting plainServe).Distinguisher)
    (masks₀ : List (List UInt8)) :
    ¬ BlindedCellHiding.TranscriptHiding (setting plainServe).tapes num den (setting plainServe).real
      (setting plainServe).Legal budgeted := by
  let a := (setting plainServe).pairAttack S bornS p₀ p₁ masks₀
  refine (setting plainServe).unmasked_refuted small (fun _ _ _ _ _ => rfl) _ budgeted a
    ((setting plainServe).pairAttack_legal S bornS hidden₀ hidden₁ masks₀)
    (meaningful a ((setting plainServe).pairAttack_distinguisher S bornS p₀ p₁ masks₀)) masks₀ rfl ?_
  obtain ⟨r₀, h₀⟩ := plain_view 5 masks₀
  obtain ⟨r₁, h₁⟩ := plain_view 7 masks₀
  have v₀ : (setting plainServe).worldView a false masks₀ = some (some (valueBytes W Witness.a2 (5 : Int)) :: r₀) := h₀
  have v₁ : (setting plainServe).worldView a true masks₀ = some (some (valueBytes W Witness.a2 (7 : Int)) :: r₁) := h₁
  rw [v₀, v₁]
  intro same
  simp only [Option.some.injEq, List.cons.injEq] at same
  exact absurd same.1 (by decide)

/-- The same deployment with the custody function the ideal one on the window
(one key per function `{0, 1} → Fin 2`, masks `0` or `1`): `CustodyPrf` holds at
gap `0` (`enumeration_satisfies`), so the PRF premise is inhabited jointly with
every other non-cryptographic one. -/
def idealSetting {Item : Type} (serve : Serve W Item) : HidingSetting W 1 (funs 1 (List.range 2)) Item (List Item) where
  keyed := idealFn 1 (List.range 2)
  base := base
  sample := fun v x => (custodyNat base.cell v x.val : Int)
  encodeMask := fun v x => (W.valueStream base.blinding.space).encode (custodyNat base.cell v x.val : Int)
  encodes := fun _ _ => rfl
  serve := serve
  view := fun cells => cells.map (KeptCell.served serve)
  g := id
  factors := fun _ => rfl
  rounds := 1
  fields := Witness.slot1

/-- The declared wire's natural reader: the blinding space's value bytes back to an integer, then
its natural part. Fixed by the wire. -/
def readNat (bytes : List UInt8) : Option Nat :=
  ((W.valueStream DeclaredEffectCell.blinding.space).toLawful.decode bytes).map Int.toNat

theorem readNat_custody (c : List UInt8) (u z : Nat) :
    readNat ((W.valueStream DeclaredEffectCell.blinding.space).encode (custodyNat c u z : Int)) =
      some (custodyNat c u z) :=
  congrArg (Option.map Int.toNat) ((W.valueStream DeclaredEffectCell.blinding.space).toLawful.decode_encode _)

/-- The ideal setting's secret bytes. -/
def secretBytes (x : Nat) : List UInt8 := [UInt8.ofNat x]

/-- The declared wire's kind-level custody decode. -/
def declaredDecode : CustodyDecode := natDecode readNat secretBytes

/-- **The ideal setting's custody is exact under the kind-level decode**: its custody value of
version `v` is the custody natural of the cell, `v` and the secret `x`, so under every key the
parameters admit a custody codec whose decode reads the cell from the bytes. -/
def idealSetting_codec {Item : Type} (serve : Serve W Item) (k : Fin (funs 1 (List.range 2))) :
    CustodyCodec W declaredDecode
      (keyedParams W (idealSetting serve).base (idealSetting serve).sample (idealSetting serve).keyed k) :=
  keyedCodec W _ _ _ k declaredDecode (fun x => secretBytes x.val) fun v x =>
    natDecode_custodyNat secretBytes (readNat_custody base.cell v x.val)

/-- **The declared custody bytes carry the cell**: two different cell identities never give the
same custody bytes, at any versions and secrets. -/
theorem declared_cross_cell {cell cell' : List UInt8} (differ : cell ≠ cell') (v w x y : Nat) :
    (W.valueStream DeclaredEffectCell.blinding.space).encode (custodyNat cell v x : Int) ≠
      (W.valueStream DeclaredEffectCell.blinding.space).encode (custodyNat cell' w y : Int) := fun same => by
  have read : ∀ c u z, declaredDecode ((W.valueStream DeclaredEffectCell.blinding.space).encode
      (custodyNat c u z : Int)) = some (c, u, secretBytes z) := fun c u z =>
    natDecode_custodyNat secretBytes (readNat_custody c u z)
  have := (read cell v x).symm.trans (same ▸ read cell' w y)
  exact differ (Prod.mk.inj (Option.some.inj this)).1

/-- **Joint premise inhabitation** at one setting, the random-function pole
(not the deployed custody PRF): the custody function is the ideal one, so
`CustodyPrf` holds at gap 0 against every test and the hop is exact. At a real
PRF the budget is the efficiency class and `reduction` is the open
concrete-security premise. Also a key, the bound's side conditions at `λ = 1`,
`queries = 0`, `versions = rounds + 1 = 2`, a budget admitting every
distinguisher, and the pair attack's birth, hidden patches, differing effects,
legality and hidden difference. -/
theorem jointPremises_inhabited {den : Nat} (denominator : 0 < den) :
    CustodyPrf 1 (funs 1 (List.range 2)) 0 den (idealSetting (rootServe W)).window (idealSetting (rootServe W)).keyed
        (fun _ => True) ∧
      0 < funs 1 (List.range 2) ∧ (0 : Nat) < 2 ^ 1 ∧
      2 * (0 + 0) * (2 ^ 1 - 0) + 2 * 2 * 0 * den < den * (2 ^ 1 - 0) ∧
      BlindedCellHiding.BudgetMeaningful (fun _ => True) (idealSetting (rootServe W)).Distinguisher ∧
      (birth W (idealSetting (rootServe W)).base S).isSome ∧
      HiddenPatch W (idealSetting (rootServe W)).fields p₀ ∧ HiddenPatch W (idealSetting (rootServe W)).fields p₁ ∧
      ∀ masks₀, (idealSetting (rootServe W)).Legal ((idealSetting (rootServe W)).pairAttack S bornS p₀ p₁ masks₀) ∧
        (idealSetting (rootServe W)).HiddenDiff ((idealSetting (rootServe W)).pairAttack S bornS p₀ p₁ masks₀) :=
  ⟨Custody.enumeration_satisfies 1 (List.range 2) denominator _ ⟨fun _ _ _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial⟩,
    Nat.pow_pos (Nat.succ_pos _), by decide, by simp; omega, fun _ _ => trivial, bornS, hidden₀, hidden₁,
    fun masks₀ => ⟨(idealSetting (rootServe W)).pairAttack_legal S bornS hidden₀ hidden₁ masks₀,
      (idealSetting (rootServe W)).pairAttack_hiddenDiff S bornS hidden₀ hidden₁ differ masks₀⟩⟩

/-- **What stays open** at the random-function pole: the three hybrids. Given
them, `RatchetHidingGoal` of `real` follows, every other premise supplied by
`jointPremises_inhabited` (the reduction obligation is trivial only because the
budget is every test, which the ideal custody function allows; at a real PRF
`reduction` stays open as the concrete-security premise). -/
theorem idealGoal_of_open {den : Nat} (denominator : 0 < den)
    (simulated ideal : (idealSetting (rootServe W)).Strategy → Bool → Fin (idealSetting (rootServe W)).tapes → Bool)
    (zk : ∀ a, (idealSetting (rootServe W)).Legal a → True → ∀ b,
      GapAtMost (idealSetting (rootServe W)).tapes 0 den ((idealSetting (rootServe W)).uniform a b) (simulated a b))
    (rom : ∀ a, (idealSetting (rootServe W)).Legal a → True → ∀ b,
      GapAtMost (idealSetting (rootServe W)).tapes (2 * 0) (2 ^ 1 - 0) (simulated a b) (ideal a b))
    (identical : ∀ a, (idealSetting (rootServe W)).Legal a → True →
      GapAtMost (idealSetting (rootServe W)).tapes 0 1 (ideal a false) (ideal a true)) (masks₀ : List (List UInt8)) :
    BlindedCellHiding.RatchetHidingGoal (idealSetting (rootServe W)).tapes 1 2 0 0 0 den (idealSetting (rootServe W)).real
      (idealSetting (rootServe W)).Legal (fun _ => True) (idealSetting (rootServe W)).HiddenDiff
      (idealSetting (rootServe W)).Distinguisher := by
  obtain ⟨prf, someKey, below, small, meaningful, _⟩ := jointPremises_inhabited denominator
  exact (idealSetting (rootServe W)).hidingGoal_of_hybrids (num := 0) (zNum := 0) (lambda := 1) (versions := 2)
    (queries := 0) _ (fun _ => True) prf (fun _ _ _ _ => trivial) someKey denominator below small meaningful S bornS p₀ p₁ hidden₀
    hidden₁ differ masks₀ simulated ideal zk rom identical

end Concrete

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
#assert_axioms Custody.enumeration_satisfies
#assert_axioms Custody.idealFn_window
#assert_axioms receiver_prf_hop
#assert_axioms receiver_prf_hop_view
#assert_axioms HidingSetting.hiding_of_hybrids
#assert_axioms HidingSetting.hidingGoal_of_hybrids
#assert_axioms HidingSetting.pairAttack_hiddenDiff
#assert_axioms HidingSetting.pairAttack_legal
#assert_axioms HidingSetting.unmasked_refuted
#assert_axioms HidingSetting.real_eq
#assert_axioms arun_transcript
#assert_axioms witness_hidden_write
#assert_axioms single_differ
#assert_axioms single_hidden
#assert_axioms Concrete.goalPremises_inhabited
#assert_axioms Concrete.plain_refuted
#assert_axioms Concrete.jointPremises_inhabited
#assert_axioms Concrete.idealGoal_of_open
#assert_axioms Custody.shift_passes_equality
#assert_axioms Custody.shift_passes_points
#assert_axioms arun_srun
#assert_axioms recoverable_refuted
#assert_axioms maskServe_refuted
#assert_axioms rootServe_servesWithin
#assert_axioms Custody.namedBudget_admits
#assert_axioms Custody.counter_refuted
#assert_axioms Custody.shift_refuted
#assert_axioms roots_viewThroughServe
#assert_axioms PublishesRun.atMostOneSuccessor
#assert_axioms History.atMostOneSuccessor
#assert_axioms KeptCell.fork_shares_mask
#assert_axioms CustodyCodec.bytes_ne
#assert_axioms CustodyCodec.constant_refuted
#assert_axioms History.custodyBytes_nodup
#assert_axioms CustodyCodec.cross_cell
#assert_axioms CustodyCodec.shared_bytes_refuted
#assert_axioms History.custodyBytes_disjoint
#assert_axioms cellOfCode_cellCode
#assert_axioms natDecode_custodyNat
#assert_axioms Concrete.declared_cross_cell
#assert_axioms KeptCell.accept_composite

end Minidregg.Kernel.PrivateCellReceiver
