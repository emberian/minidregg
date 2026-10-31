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
  `EraseCost` is the counted bound, uniform constants times `L`, on caches with
  injective live paths (a `.clash` list has no uniform bound).
* **Complete class openings.** Keys are a fixed-width class tag followed by the
  address path (`ClassKeys`), so one visibility class is one subtree. A
  verifying reveal at a class tag must answer exactly that class's live entries,
  or exhibit a collision within this comparison's finite scope
  (`ClassRevealComplete`). The ANSWER is exact; the reveal's `members` are not
  bounded: an honest early stop at another class's leaf verifies with that leaf
  among the members and an empty answer, and depth zero reveals the whole store.
  Bounded disclosure and witness privacy are the ZK opening's obligations, not
  this one's. Owed witnesses: a nonempty multi-class instance with an injective
  `dig` (`AuthTrie.spelled` is `Unit`-keyed and cannot show cross-class
  refusal), overwrite and deletion teeth, and honest cached-reveal acceptance.

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

/-- **Erase cost shape.** A family of counted erases, one per key-path function
and public length. This predicate constrains only the returned count, so it is
meaningful only for an operation whose count is defined by its own execution:
it is claimed here for `AuthTrie.Cache.eraseCounted` (`erase_cost`), whose count
is node visits, digest evaluations (the empty-node digests a fresh branch reads
included) and clash entries filtered; allocations are O(1) per visit and not
counted separately. A self-reported counter passes it trivially. On every cache with injective live paths the count is at
most `perBit * L + fixed`, with constants chosen BEFORE `L` and the key paths
(a constant chosen after `L` could hide a rebuild, the live store being at most
`2^L` entries), and each member is `EraseCorrect`. -/
def EraseCost (dig : NodeIn K V D → D)
    (eraseCounted : ∀ {bitsOf : K → List Bool} {L : Nat},
      AuthTrie.Cache dig bitsOf L → K → AuthTrie.Cache dig bitsOf L × Nat) : Prop :=
  (∀ (bitsOf : K → List Bool) (L : Nat),
    EraseCorrect (V := V) (bitsOf := bitsOf) (L := L) dig (fun cache k => (eraseCounted cache k).1)) ∧
  ∃ perBit fixed : Nat, ∀ (bitsOf : K → List Bool) (L : Nat) (cache : AuthTrie.Cache dig bitsOf L)
    (es : List (K × V)) (k : K),
    cache.Holds es → PathsInjective bitsOf es → (eraseCounted cache k).2 ≤ perBit * L + fixed

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
distinct nodes among this comparison's nodes share a digest. -/
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

/-- **`EraseCost` holds** for the counted erase, at four per key bit plus one:
per level one visit and at most three digest evaluations (a re-joined branch and
the empty children it reads). -/
theorem erase_cost (dig : NodeIn K V D → D) :
    EraseCost (V := V) dig AuthTrie.Cache.eraseCounted :=
  ⟨fun _ _ => erase_correct dig, 4, 1, fun _ _ _ _ k h inj => AuthTrie.Cache.eraseCounted_count h inj k⟩

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
open Minidregg.Theory.AuthTrie.Trie (eraseCounted)

/-- The kept trie of the three-key example. -/
def kept : AuthTrie.Trie (List Bool) Nat String := AuthTrie.Trie.build toy 3 (entries bitsOf kvs)

/-- Erasing `110` (alone under `1`) collapses the right spine: the digest is the
canonical root of the two remaining keys, within the counted bound `4L + 1`. -/
theorem erase_collapses :
    (eraseCounted toy [true, true, false] 3 [true, true, false] kept).1.digest toy =
        tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [true, true, false] kvs)) ∧
      (eraseCounted toy [true, true, false] 3 [true, true, false] kept).2 ≤ 4 * 3 + 1 := by
  decide

/-- Erasing `011` leaves `001` alone under `0`: the leaf rises to depth one. -/
theorem erase_rises :
    (eraseCounted toy [false, true, true] 3 [false, true, true] kept).1.digest toy =
        tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [false, true, true] kvs)) := by
  decide

/-- Deletion teeth: the identity operation does not hold the dropped list, since
the root of the dropped list differs from the kept root. -/
theorem identity_not_erase :
    kept.digest toy ≠ tree toy 3 (entries bitsOf (AuthTrie.Trie.dropKey [true, true, false] kvs)) := by
  decide

/-- Erasing an absent key changes nothing. -/
theorem erase_absent :
    (eraseCounted toy [true, false, false] 3 [true, false, false] kept).1.digest toy = kept.digest toy := by
  decide

end Witness

end Minidregg.Theory.PrivateCellTrie
