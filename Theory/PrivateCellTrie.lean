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
  or exhibit a collision AMONG the nodes this comparison hashes
  (`ClassRevealComplete`). The ANSWER is exact; the reveal's `members` are not
  bounded: an honest early stop at another class's leaf verifies with that leaf
  among the members and an empty answer, and depth zero reveals the whole store.
  Bounded disclosure and witness privacy are the ZK opening's obligations, not
  this one's. Owed witnesses: a nonempty multi-class instance with an injective
  `dig` (`AuthTrie.spelled` is `Unit`-keyed and cannot show cross-class
  refusal), overwrite and deletion teeth, and honest cached-reveal acceptance.

The scoped collision set matters: a fixed-width digest always has SOME global
collision, so a disjunct naming any collision is vacuous (`AuthTrie` §101,
astra round 2). `AuthTrie.reveal_sound` concludes with the global `Collision`;
discharging `ClassRevealComplete` needs its scoped strengthening.
-/
module

public import Theory.AuthTrieRange
public import Theory.AuthTrieCache

@[expose] public section

namespace Minidregg.Theory.PrivateCellTrie

set_option autoImplicit false

open Minidregg.Theory.AuthTrie (NodeIn root lastVal canon entries tree climb
  CollisionAmong TreeNode Reveal revealVerify)
open Minidregg.Theory.AuthTrie.Trie (dropKey)
open Minidregg.Theory.AuthTrie.Cache (Holds PathsInjective)

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]

/-- **Erase target.** `erase cache k` keeps a trie holding the list with `k`
dropped, whatever list the cache held. -/
def EraseCorrect {bitsOf : K → List Bool} {L : Nat} (dig : NodeIn K V D → D)
    (erase : AuthTrie.Cache dig bitsOf L → K → AuthTrie.Cache dig bitsOf L) : Prop :=
  ∀ (cache : AuthTrie.Cache dig bitsOf L) (es : List (K × V)) (k : K),
    cache.Holds es → (erase cache k).Holds (dropKey k es)

/-- **Erase cost target.** The counted erase (its count instrumented in the
operation itself: node inspections, hashes and allocations) touches at most
`perBit * L + fixed` nodes on every cache with injective live paths, with
constants independent of the store, and its cache is `EraseCorrect`'s. -/
def EraseCost {bitsOf : K → List Bool} {L : Nat} (dig : NodeIn K V D → D)
    (eraseCounted : AuthTrie.Cache dig bitsOf L → K → AuthTrie.Cache dig bitsOf L × Nat) : Prop :=
  EraseCorrect dig (fun cache k => (eraseCounted cache k).1) ∧
  ∃ perBit fixed : Nat, ∀ (cache : AuthTrie.Cache dig bitsOf L) (es : List (K × V)) (k : K),
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

/-- The branch nodes a climb from digest `below` hashes. -/
inductive ClimbDigestNode (dig : NodeIn K V D → D) (below : D) :
    List Bool → List D → NodeIn K V D → Prop
  | left (bits : List Bool) (s : D) (siblings : List D) :
      ClimbDigestNode dig below (false :: bits) (s :: siblings)
        (.branch (climb dig bits siblings below) s)
  | right (bits : List Bool) (s : D) (siblings : List D) :
      ClimbDigestNode dig below (true :: bits) (s :: siblings)
        (.branch s (climb dig bits siblings below))
  | deeper (b : Bool) (bits : List Bool) (s : D) (siblings : List D) (x : NodeIn K V D) :
      ClimbDigestNode dig below bits siblings x → ClimbDigestNode dig below (b :: bits) (s :: siblings) x

/-- The nodes one class-reveal comparison hashes: the canonical tree of the
store, the reveal's climb from the revealed subtree to the root, and the
canonical tree of the revealed members below the stop depth. -/
def revealNodes (dig : NodeIn K V D → D) (bitsOf : K → List Bool) (L : Nat)
    (es : List (K × V)) (p : List Bool) (reveal : Reveal K V D) : NodeIn K V D → Prop := fun x =>
  let depth := reveal.siblings.length
  let below := tree dig (L - depth) (Reveal.entriesBelow bitsOf depth reveal.members)
  TreeNode dig L (entries bitsOf (canon es)) x ∨
    ClimbDigestNode dig below (p.take depth) reveal.siblings x ∨
    TreeNode dig (L - depth) (Reveal.entriesBelow bitsOf depth reveal.members) x

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

end Minidregg.Theory.PrivateCellTrie
