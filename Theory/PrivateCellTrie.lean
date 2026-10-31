/-
# Theory.PrivateCellTrie — what the compressed trie owes before it carries a blinded cell

Statements only (statement-first, docs/RATCHET-LOG-DESIGN.md §3 as instantiated in
docs/PRIVATE-CELLS-STATE.md). The cell's private index is `Theory.AuthTrie`; a
cell's store needs two things the trie does not yet have:

* **Erase.** A store write can remove a key. `EraseCorrect` is the target for a
  `Cache` operation that removes one key along one walk, collapsing branches, so
  the kept trie still `Holds` the logical list with the key dropped. Teeth: the
  identity operation fails it whenever the key is live (`Holds` compares
  entries, not roots). Satisfiable: a rebuild from the cache's retained entries
  satisfies it, which is exactly the O(n) path the real operation must not take:
  `EraseCost` bounds the interpreter's count of an erase written as a heap
  program (`HeapErase`), uniform constants times `L`, on caches with injective
  live paths (a `.clash` list has no uniform bound).
* **Complete class openings.** Keys are a fixed-width class tag followed by the
  address path (`ClassKeys`), so one visibility class is one subtree. A
  verifying reveal at a class tag must answer exactly that class's live entries,
  or exhibit a collision within this comparison's finite scope
  (`ClassRevealComplete`). The ANSWER is exact; the reveal's `members` are not
  bounded: an honest early stop at another class's leaf verifies with that leaf
  among the members and an empty answer, and depth zero reveals the whole store.
  Bounded disclosure and witness privacy are the ZK opening's obligations, not
  this one's. Witnesses (`Witness`): three-bit keys in two classes over the free
  (injective) digest, where the theorem's premises hold and its collision escape
  is impossible (`class_opening_exact`); the honest class opening verifying with
  the exact answer, and a cross-class member, a withheld member and the other
  class's opening refused. The kept trie serves the opening in general
  (`Cache.reveal_verifies`).

The scoped collision set matters: a fixed-width digest always has SOME global
collision, so a disjunct naming any collision is vacuous (`AuthTrie` §101,
astra round 2). `AuthTrie.reveal_sound` now concludes with the scoped `CollisionAmong
(revealNodes …)`, which discharges `ClassRevealComplete` (`classRevealComplete`);
`erase_correct` and `erase_cost` discharge the erase targets with
`AuthTrie.Cache.erase` (`Theory.AuthTrieErase`).
-/
module

public import Theory.AuthTrieRange
public import Theory.AuthTrieCache
public import Theory.AuthTrieErase
public import Theory.AuthTrieReveal
public import Theory.AssertAxioms

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

namespace Minidregg.Theory.PrivateCellTrie

set_option autoImplicit false

open Minidregg.Theory.AuthTrie (NodeIn root lastVal canon entries tree climb mem_canon
  CollisionAmong TreeNode Reveal revealVerify reveal_sound)
open Minidregg.Theory.AuthTrie.Trie (dropKey)
open Minidregg.Theory.AuthTrie.Cache (Holds PathsInjective)

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]

/-- **Erase target.** `erase cache k` keeps a trie holding the list with `k`
dropped, whatever list the cache held. -/
def EraseCorrect {bitsOf : K → List Bool} {L : Nat} (dig : NodeIn K V D → D)
    (erase : AuthTrie.Cache dig bitsOf L → K → AuthTrie.Cache dig bitsOf L) : Prop :=
  ∀ (cache : AuthTrie.Cache dig bitsOf L) (es : List (K × V)) (k : K),
    cache.Holds es → (erase cache k).Holds (dropKey k es)

/-- A trie erase as a heap program (`AuthTrie.Prog`), uniform in the key,
value and digest types: from the key, the public length, the key's path and
the root's handle, a program whose node reads, node writes and digests are
interpreter operations. A handle is a heap index, so the program reaches a
node's contents only by loading it. -/
abbrev HeapErase :=
  ∀ {K V D : Type} [DecidableEq K], K → Nat → List Bool → Nat → AuthTrie.Prog K V D Nat

/-- **Erase cost target.** With the constants chosen BEFORE the key, value and
digest types, the digest function, the public length and the key paths: on
every heap holding a cache's trie, the program's result handle holds a cache
that is the erase (`EraseCorrect`'s postcondition), and on caches with injective
live paths the interpreter (`AuthTrie.run`: one per hash, load and store, a
clash load charged its size) counts at most `perBit * L + fixed` operations.

What the count is: abstract operations of a heap with constant-time access (the
list heap `run` uses is a model, not a runtime). The program is chosen before
the digest function, so a digest it uses comes from `hash` or a loaded node;
it holds for every representing heap, so the layout is learnt only by loading;
constants before the types exclude absorbing a finite key space. Pure
computation between operations is not metered. -/
def EraseCost (erase : HeapErase) : Prop :=
  ∃ perBit fixed : Nat, ∀ {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
    (dig : NodeIn K V D → D) (bitsOf : K → List Bool) (L : Nat) (cache : AuthTrie.Cache dig bitsOf L)
    (es : List (K × V)) (k : K) (heap : AuthTrie.Heap K V D) (x : Nat),
    cache.Holds es → AuthTrie.Repr heap x cache.trie →
      (∃ after : AuthTrie.Cache dig bitsOf L,
        AuthTrie.Repr (AuthTrie.run dig heap (erase k L (bitsOf k) x)).2.1
          (AuthTrie.run dig heap (erase k L (bitsOf k) x)).1 after.trie ∧ after.Holds (dropKey k es)) ∧
      (PathsInjective bitsOf es → (AuthTrie.run dig heap (erase k L (bitsOf k) x)).2.2 ≤ perBit * L + fixed)

/-- Class-hierarchical keys: a fixed-width, injective class tag, then the
address path. Leaves authenticate the full key, but two live keys with one path
reach a `.clash`, whose digest is the empty node's: admission must preserve
`PathsInjective` on live keys or count index collisions. -/
structure ClassKeys (K Class : Type) where
  classOf : K → Class
  tag : Class → List Bool
  address : K → List Bool
  tagWidth : Nat
  tag_width : ∀ c, (tag c).length = tagWidth
  tag_injective : Function.Injective tag

def ClassKeys.bitsOf {Class : Type} (keys : ClassKeys K Class) (k : K) : List Bool :=
  keys.tag (keys.classOf k) ++ keys.address k

/-- The finite comparison scope of one class reveal: the canonical tree of the
store, the reveal's climb from the revealed subtree to the root, and the
canonical tree of the revealed members below the stop depth
(`AuthTrie.revealNodes` over the store's canonical entries). -/
def revealNodes (dig : NodeIn K V D → D) (bitsOf : K → List Bool) (L : Nat)
    (es : List (K × V)) (p : List Bool) (reveal : Reveal K V D) : NodeIn K V D → Prop :=
  AuthTrie.revealNodes dig bitsOf L (entries bitsOf (canon es)) p reveal

/-- **Complete class opening target.** Over the canonical root of a store with
injective live paths of public length `L`, a verifying reveal at class `c`'s tag
answers exactly the live entries of class `c` (last value per key), or two
distinct nodes of the scope `revealNodes` share a digest: the store's whole
canonical tree, the reveal's climb and the revealed members' tree. The scope
includes the whole store tree, so an unrelated collision in the store discharges
every reveal; locality to the path and the selected subtree is owed. -/
def ClassRevealComplete {Class : Type} (dig : NodeIn K V D → D) (keys : ClassKeys K Class)
    (L : Nat) : Prop :=
  (∀ k, (keys.bitsOf k).length = L) →
  ∀ (es : List (K × V)) (c : Class) (reveal : Reveal K V D),
    PathsInjective keys.bitsOf es →
    revealVerify dig keys.bitsOf L (root dig keys.bitsOf L es) (keys.tag c) reveal = true →
    (∀ k v, (k, v) ∈ reveal.answer keys.bitsOf (keys.tag c) ↔
        lastVal es k = some v ∧ keys.classOf k = c) ∨
      CollisionAmong dig (revealNodes dig keys.bitsOf L es (keys.tag c) reveal)

/-! ## Discharged: the kept trie's erase -/

omit [DecidableEq V] [DecidableEq D] in
/-- **`EraseCorrect` holds** for the one-walk erase (`AuthTrie.Cache.erase`). -/
theorem erase_correct {bitsOf : K → List Bool} {L : Nat} (dig : NodeIn K V D → D) :
    EraseCorrect (V := V) (bitsOf := bitsOf) (L := L) dig AuthTrie.Cache.erase :=
  fun _ _ k h => AuthTrie.Cache.erase_holds h k

/-- **`EraseCost` holds** for the program erase (`AuthTrie.eraseM` over
`AuthTrie.Prog.ops`), at seven operations per key bit plus three: per level one
load, the re-join's two loads, at most two empty-node digests, one branch hash
and one store. -/
theorem erase_cost : EraseCost (fun k n bits x => AuthTrie.eraseM AuthTrie.Prog.ops k n bits x) :=
  ⟨7, 3, fun _ _ _ cache _ k _ _ h rx =>
    ⟨⟨cache.erase k, (AuthTrie.Cache.eraseM_cache h k rx).1, AuthTrie.Cache.erase_holds h k⟩,
      (AuthTrie.Cache.eraseM_cache h k rx).2⟩⟩

/-! ## Discharged: complete class openings -/

omit [DecidableEq K] [DecidableEq V] [DecidableEq D] in
theorem ClassKeys.take_bitsOf {Class : Type} (keys : ClassKeys K Class) (k : K) :
    (keys.bitsOf k).take keys.tagWidth = keys.tag (keys.classOf k) := by
  simp [ClassKeys.bitsOf, ← keys.tag_width (keys.classOf k)]

/-- **`ClassRevealComplete` holds**: scoped reveal soundness (`AuthTrie.reveal_sound`)
over the store's canonical entries, with the class read off the fixed-width tag. -/
theorem classRevealComplete {Class : Type} (dig : NodeIn K V D → D) (keys : ClassKeys K Class)
    (L : Nat) : ClassRevealComplete dig keys L := by
  intro lengths es c reveal inj accepted
  rcases reveal_sound dig keys.bitsOf L lengths (canon es) (AuthTrie.Cache.wf_canon lengths inj) (keys.tag c) reveal
      accepted with exact | collision
  · left
    intro k v
    rw [exact k v, mem_canon, keys.tag_width c, ClassKeys.take_bitsOf]
    exact and_congr Iff.rfl ⟨fun h => keys.tag_injective h, fun h => h ▸ rfl⟩
  · exact Or.inr collision

/-! ## Witnesses: an erase that collapses, deletion and overwrite teeth -/

namespace Witness

open Minidregg.Theory.AuthTrie.Poles (bitsOf toy kvs)
open Minidregg.Theory.AuthTrie (eraseM run storeTrie Heap)

/-- The kept trie of the three-key example. -/
def kept : AuthTrie.Trie (List Bool) Nat String := AuthTrie.Trie.build toy 3 (entries bitsOf kvs)

/-- The digest held at a handle. -/
def heapDigest (heap : Heap (List Bool) Nat String) (h : Nat) : String :=
  match heap.get h with
  | .leaf d .. => d
  | .branch d .. => d
  | _ => toy .empty

/-- The program erase run on `kept` stored in an empty heap: the result handle,
the heap, and the interpreter's count. -/
def counted (k : List Bool) : Nat × Heap (List Bool) Nat String × Nat :=
  run toy (storeTrie kept []).2 (eraseM AuthTrie.Prog.ops k 3 k (storeTrie kept []).1)

/-- Erasing `110` (alone under `1`) collapses the right spine: the digest is the
canonical root of the two remaining keys, within the handler's bound `7L + 3`. -/
theorem erase_collapses :
    heapDigest (counted [true, true, false]).2.1 (counted [true, true, false]).1 =
        tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [true, true, false] kvs)) ∧
      (counted [true, true, false]).2.2 ≤ 7 * 3 + 3 := by
  decide

/-- Erasing `011` leaves `001` alone under `0`: the leaf rises to depth one. -/
theorem erase_rises :
    heapDigest (counted [false, true, true]).2.1 (counted [false, true, true]).1 =
        tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [false, true, true] kvs)) := by
  decide

/-- Deletion teeth: the identity operation does not hold the dropped list, since
the root of the dropped list differs from the kept root. -/
theorem identity_not_erase :
    kept.digest toy ≠ tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [true, true, false] kvs)) := by
  decide

/-- Erasing an absent key changes nothing. -/
theorem erase_absent :
    heapDigest (counted [true, false, false]).2.1 (counted [true, false, false]).1 = kept.digest toy := by
  decide


/-! ### Two classes: a complete class opening and cross-class refusal

Keys are three bits (`Bool × Bool × Bool`, so every key path has length 3 and
the theorem's length premise holds), the first bit the class. The digest is the
free one (`FreeDigest`, the node itself), injective, so no collision exists and
`classRevealComplete` gives the exact class answer unconditionally. -/

abbrev Key3 := Bool × Bool × Bool

/-- The free digest: a node is its own digest. -/
inductive FreeDigest where
  | e
  | l (k : Key3) (v : Nat)
  | b (x y : FreeDigest)
  deriving DecidableEq

def free : NodeIn Key3 Nat FreeDigest → FreeDigest
  | .empty => .e
  | .leaf k v => .l k v
  | .branch x y => .b x y

theorem free_injective : Function.Injective free := by
  intro a b same
  cases a <;> cases b <;> simp_all [free]

theorem no_collision (S : NodeIn Key3 Nat FreeDigest → Prop) : ¬ CollisionAmong free S :=
  fun ⟨_, _, _, _, ne, same⟩ => ne (free_injective same)

def keys3 : ClassKeys Key3 Bool :=
  ⟨fun k => k.1, fun c => [c], fun k => [k.2.1, k.2.2], 1, fun _ => rfl, fun _ _ h => by simpa using h⟩

theorem keys3_length (k : Key3) : (keys3.bitsOf k).length = 3 := rfl

def store3 : List (Key3 × Nat) := [((false, false, true), 7), ((false, true, true), 9), ((true, true, false), 3)]

theorem store3_paths : PathsInjective keys3.bitsOf store3 := by
  intro a b _ _ same
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [ClassKeys.bitsOf, keys3, List.cons_append, List.nil_append, List.cons.injEq] at same
  obtain ⟨rfl, rfl, rfl, -⟩ := same
  rfl

/-- **Every verifying class opening answers exactly its class**, at this
instance: the theorem's premises hold and its collision escape is impossible. -/
theorem class_opening_exact (c : Bool) (reveal : Reveal Key3 Nat FreeDigest)
    (accepted : revealVerify free keys3.bitsOf 3 (root free keys3.bitsOf 3 store3) (keys3.tag c) reveal = true)
    (k : Key3) (v : Nat) :
    (k, v) ∈ reveal.answer keys3.bitsOf (keys3.tag c) ↔ lastVal store3 k = some v ∧ k.1 = c :=
  ((classRevealComplete free keys3 3 keys3_length store3 c reveal store3_paths accepted).resolve_right
    (no_collision _)) k v

/-- Class `false`'s honest opening. -/
def classHonest : Reveal Key3 Nat FreeDigest :=
  AuthTrie.revealFor free keys3.bitsOf 3 (canon store3) (keys3.tag false)

/-- The premise is inhabited: the honest class opening verifies, answering the
class's two keys. -/
theorem class_honest_verified :
    revealVerify free keys3.bitsOf 3 (root free keys3.bitsOf 3 store3) (keys3.tag false) classHonest = true ∧
      classHonest.answer keys3.bitsOf (keys3.tag false) =
        [((false, false, true), 7), ((false, true, true), 9)] := by
  decide

/-- Cross-class refusal: class `false`'s siblings with class `true`'s key claimed. -/
theorem cross_class_refused :
    revealVerify free keys3.bitsOf 3 (root free keys3.bitsOf 3 store3) (keys3.tag false)
      ⟨classHonest.siblings, classHonest.members ++ [((true, true, false), 3)]⟩ = false := by
  decide

/-- Withholding a member of the class is refused. -/
theorem class_member_withheld_refused :
    revealVerify free keys3.bitsOf 3 (root free keys3.bitsOf 3 store3) (keys3.tag false)
      ⟨classHonest.siblings, [((false, false, true), 7)]⟩ = false := by
  decide

/-- The other class's honest opening does not pass as this class's. -/
theorem other_class_refused :
    revealVerify free keys3.bitsOf 3 (root free keys3.bitsOf 3 store3) (keys3.tag false)
      (AuthTrie.revealFor free keys3.bitsOf 3 (canon store3) (keys3.tag true)) = false := by
  decide

end Witness

#assert_axioms erase_correct
#assert_axioms erase_cost
#assert_axioms classRevealComplete
#assert_axioms Witness.erase_collapses
#assert_axioms Witness.class_honest_verified
#assert_axioms Witness.cross_class_refused
#assert_axioms Witness.class_member_withheld_refused
#assert_axioms Witness.other_class_refused
#assert_axioms Witness.class_opening_exact

end Minidregg.Theory.PrivateCellTrie
