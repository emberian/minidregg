/-
# Kernel.WorldRootCache — the world root, kept: one walk per write

The specification is `WorldRoot.deployedRoot es`: the compressed trie
(`Theory.AuthTrie`) over each key's LAST value in `es`. This module keeps the
evaluated trie (`RootCache`, an `AuthTrie.Cache` at the deployed node hash and
index) and states when it holds a list (`RootsExact`, a `Prop`: no runtime
entry list is kept beside the trie):

* `RootsExact.root_eq`: a cache exact for `es` has root `deployedRoot es`;
* `RootCache.build` builds once, one digest per leaf and branch;
* `RootsExact.advance`: writing slots in order keeps exactness for any list
  that gives every key the new last value — one walk per slot, one digest per
  branch on it (about `log₂ n`), never a rebuild;
* `RootsExact.opening_complete`: the opening read off the cache (no hashing)
  verifies against the root, answering the key's last value.

There is no injectivity flag and no fallback rebuild: an index collision is a
`clash` node whose digest is what the specification gives there, so the cache
equals the specification at every list.

Poles (a byte-mixing toy hash, `decide`): `cached_write_root` (the kept trie
tracks a write), `stale_cache_refuted` (a cache that skipped the write keeps a
digest that is no longer the root), `order_free_on_collision` (two keys at one
index path, written in either order: one root).
-/
import Kernel.WorldRoot

namespace Minidregg.Kernel.WorldRootCache

open Minidregg.Theory
open Minidregg.Kernel.WorldRoot
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

export Minidregg.Theory.AuthTrie (lastVal lastVal_append lastVal_cons lastVal_isSome lastVal_snoc lastVal_map)

/-- **The kept world root**: the compressed trie at the deployed node hash and index. -/
abbrev RootCache := AuthTrie.Cache worldDig deployedIx 256

/-- The cache holds `es`: its entries are `es`'s last values. -/
def RootsExact (cache : RootCache) (es : List (Key × Digest)) : Prop := cache.Holds es

namespace RootCache

/-- Bulk build: one digest per leaf and per branch. -/
def ofEntries (es : List (Key × Digest)) : RootCache := AuthTrie.Cache.build deployedIx_length es

/-- Write one slot: one walk, one digest per branch on it. -/
def write (cache : RootCache) (key : Key) (value : Digest) : RootCache :=
  cache.insert deployedIx_length key value

/-- Write slots in order. -/
def writeAll (cache : RootCache) (slots : List (Key × Digest)) : RootCache :=
  cache.insertAll deployedIx_length slots

def root (cache : RootCache) : Digest := cache.digest

/-- The opening of a key, read off the kept trie (no hashing). -/
def opening (cache : RootCache) (k : Key) : AuthTrie.Opening Key Digest Digest :=
  AuthTrie.Cache.opening cache k

end RootCache

theorem RootsExact.ofEntries (es : List (Key × Digest)) : RootsExact (RootCache.ofEntries es) es :=
  AuthTrie.Cache.build_holds deployedIx_length es

/-- **The kept root is the specification root.** -/
theorem RootsExact.root_eq {cache : RootCache} {es : List (Key × Digest)} (exact : RootsExact cache es) :
    cache.root = deployedRoot es :=
  AuthTrie.Cache.digest_eq exact

theorem RootCache.ofEntries_root (es : List (Key × Digest)) : (RootCache.ofEntries es).root = deployedRoot es :=
  (RootsExact.ofEntries es).root_eq

theorem RootsExact.congr {cache : RootCache} {es es' : List (Key × Digest)} (exact : RootsExact cache es)
    (same : ∀ k, lastVal es k = lastVal es' k) : RootsExact cache es' :=
  AuthTrie.Cache.Holds.congr exact same

/-- The cache of `es` with its exactness, built once. -/
def RootCache.build (es : List (Key × Digest)) : (cache : RootCache) ×' RootsExact cache es :=
  ⟨RootCache.ofEntries es, RootsExact.ofEntries es⟩

/-- **Advance**: write `slots` in order; the result is exact for any `es'` whose
last values are the slots' over `es`'s. One walk per slot. -/
def RootsExact.advance {cache : RootCache} {es es' : List (Key × Digest)}
    (exact : RootsExact cache es) (slots : List (Key × Digest))
    (step : ∀ k, lastVal es' k = (lastVal slots k).or (lastVal es k)) :
    (next : RootCache) ×' RootsExact next es' :=
  ⟨cache.writeAll slots, (AuthTrie.Cache.insertAll_holds deployedIx_length slots exact).congr
    fun k => by rw [lastVal_append, step]⟩

theorem RootsExact.advance_root {cache : RootCache} {es es' : List (Key × Digest)}
    (exact : RootsExact cache es) (slots : List (Key × Digest))
    (step : ∀ k, lastVal es' k = (lastVal slots k).or (lastVal es k)) :
    (exact.advance slots step).1.root = deployedRoot es' :=
  (exact.advance slots step).2.root_eq

/-- **Completeness**: the opening read off an exact cache verifies against its
root, answering the key's last value (under distinct paths; a path collision
is a deployed-hash collision, `deployed_paths`). -/
theorem RootsExact.opening_complete {cache : RootCache} {es : List (Key × Digest)}
    (exact : RootsExact cache es) (inj : AuthTrie.Cache.PathsInjective deployedIx es) (k : Key) :
    AuthTrie.verify worldDig deployedIx cache.root k (lastVal es k) (cache.opening k) = true :=
  AuthTrie.Cache.opening_complete deployedIx_length exact inj k

/-! ## Poles (a byte-mixing toy hash, so equalities are computed) -/

namespace Toy

/-- A toy node hash: weak, but a write moves it. -/
def dig : AuthTrie.NodeIn UInt8 UInt8 UInt8 → UInt8
  | .empty => 0
  | .leaf k v => k * 31 + v + 1
  | .branch l r => l * 7 + r * 13 + 3

/-- The index: a byte's eight bits. -/
def ix (k : UInt8) : List Bool := byteBits k

theorem ix_length (k : UInt8) : (ix k).length = 8 := byteBits_length k

/-- An index that collides: keys equal mod 4 share a path. -/
def ixMod (k : UInt8) : List Bool := byteBits (k % 4)

theorem ixMod_length (k : UInt8) : (ixMod k).length = 8 := byteBits_length _

def es0 : List (UInt8 × UInt8) := [(5, 7), (2, 1)]

def c0 : AuthTrie.Cache dig ix 8 := AuthTrie.Cache.build ix_length es0

/-- **Satisfiable pole.** The kept trie tracks a write. -/
theorem cached_write_root :
    (c0.insert ix_length 6 200).digest = AuthTrie.root dig ix 8 (es0 ++ [(6, 200)]) := by decide +kernel

/-- The write moves the root. -/
theorem write_moves_root : AuthTrie.root dig ix 8 (es0 ++ [(6, 200)]) ≠ AuthTrie.root dig ix 8 es0 := by
  decide +kernel

/-- **Refuting pole.** A cache that skipped the write is no longer the root. -/
theorem stale_cache_refuted : c0.digest ≠ AuthTrie.root dig ix 8 (es0 ++ [(6, 200)]) := by decide +kernel

/-- Keys 1 and 5 share a path under `ixMod`: written in either order, one root. -/
theorem order_free_on_collision :
    ((AuthTrie.Cache.build (dig := dig) ixMod_length []).insertAll ixMod_length [(1, 7), (5, 9)]).digest =
      ((AuthTrie.Cache.build (dig := dig) ixMod_length []).insertAll ixMod_length [(5, 9), (1, 7)]).digest := by
  decide +kernel

end Toy

end Minidregg.Kernel.WorldRootCache

#assert_axioms Minidregg.Kernel.WorldRootCache.RootsExact.root_eq
#assert_axioms Minidregg.Kernel.WorldRootCache.RootsExact.advance_root
#assert_axioms Minidregg.Kernel.WorldRootCache.RootsExact.opening_complete
#assert_axioms Minidregg.Kernel.WorldRootCache.Toy.cached_write_root
#assert_axioms Minidregg.Kernel.WorldRootCache.Toy.stale_cache_refuted
#assert_axioms Minidregg.Kernel.WorldRootCache.Toy.order_free_on_collision
