/-
# Compiler.DurableIndexProbe — the incremental trie against the canonical root, executed

The executed probe of `Compiler.DurableIndex`, in its own module: the two closed
`native_decide` runs interpret cSHAKE256 over every node of the probe's tries, about
a minute each, and no module imports them, so they build beside the Host, not ahead
of it.
-/
module

public import Compiler.DurableIndex
public import Theory.AssertCompiled
meta import Compiler.DurableIndex
meta import Theory.AssertCompiled

@[expose] public section

namespace Minidregg.Compiler.DurableIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.AuthTrie (NodeIn Collision CollisionAmong TreeNode ClimbNode WF entries tree)

set_option autoImplicit false

/-! ## The incremental set against the canonical root (executed probe)

`set` is not yet proved to compute `rootOf` of the updated map (cv
01a11741-1af8; `store audit` rebuilds every row version from the records). This
probe runs a sequence of inserts, updates and deletes — including keys that share
their family and primary (a 264-bit common prefix), deletes that collapse a leaf
upward, and a delete of the last member — through `setAll` over in-memory rows,
and checks after EVERY step that the incremental root is `rootOf` of the logical
map, that every key's row lookup verifies and answers the map's value, and that
each family's reveal answers exactly the family's members. -/

namespace Probe

def probeKey (family : UInt8) (n : Nat) (secondary : Nat) : IndexKey :=
  ⟨family, primaryOf family [UInt8.ofNat n], ⟨secondary % 256 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

def keys : List IndexKey :=
  [probeKey 4 1 0, probeKey 4 1 1, probeKey 4 1 2, probeKey 4 1 3, probeKey 4 1 7,
   probeKey 4 2 0, probeKey 0 1 0, probeKey 0 2 0, probeKey 0 3 0, probeKey 1 1 0, probeKey 1 9 0]

def ops : List (Nat × Option (List UInt8)) :=
  (List.range 11).map (fun i => (i, some [UInt8.ofNat i])) ++
  [(2, some [9, 9]), (6, some [1]), (0, none), (1, none), (2, none), (6, some [2]), (9, none),
   (0, some [5]), (3, none), (4, none), (5, none), (7, none), (8, none), (10, none), (6, none),
   (0, none), (1, none), (9, none)]

def familyPrefix (family : UInt8) : List Bool := (bitsOf ⟨family, 0, 0⟩).take 8

def sameSet (a b : List (IndexKey × List UInt8)) : Bool :=
  a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)

/-- One step checked: the root, every key's verified lookup, every family's reveal. -/
def stepOk (rows : List Bool → Option Row) (root : Digest) (model : List (IndexKey × List UInt8)) : Bool :=
  root == rootOf model &&
  keys.all (fun k => match lookupRows rows root k with
    | .ok answer => answer.value == (model.find? (·.1 = k)).map (·.2)
    | .error _ => false) &&
  [0, 1, 4].all (fun family : UInt8 => match revealRows rows root (familyPrefix family) with
    | .ok revealed => sameSet revealed.members (model.filter (·.1.family = family))
    | .error _ => false)

def run : List (Nat × Option (List UInt8)) → List (List Bool × Row) → Digest →
    List (IndexKey × List UInt8) → Bool
  | [], _, root, model => model.isEmpty == (root == emptyDigest)
  | (i, value) :: rest, written, root, model =>
      let k := keys.getD i (probeKey 0 0 0)
      match setAll (overlay (fun _ => none) written) root [(k, value)] with
      | .error _ => false
      | .ok (root', rows) =>
          let written' := rows ++ written
          let model' := modelSet model k value
          stepOk (overlay (fun _ => none) written') root' model' && run rest written' root' model'

theorem incremental_matches_canonical : run ops [] emptyDigest [] = true := by native_decide

/-- Rows read against a root they do not reach (here a forged one-leaf root
naming another value) are refused, both by the lookup and by the reveal — never
answered as the rows say. -/
theorem wrong_root_refused :
    (match setAll (overlay (fun _ => none) []) emptyDigest [(probeKey 4 1 0, some [1])] with
      | .ok (_, rows) => (lookupRows (overlay (fun _ => none) rows) (dig (.leaf (probeKey 4 1 0) [2])) (probeKey 4 1 0)).toOption.isNone &&
          (revealRows (overlay (fun _ => none) rows) (dig (.leaf (probeKey 4 1 0) [2])) (familyPrefix 4)).toOption.isNone
      | .error _ => false) = true := by native_decide

end Probe

#assert_compiled Probe.incremental_matches_canonical
#assert_compiled Probe.wrong_root_refused

end Minidregg.Compiler.DurableIndex
