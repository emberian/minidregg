/-
# Compiler.DurableSpent — the spent set and transaction index, authenticated and incremental

KN2-STORE-OPEN. The checkpoint used to carry every consumed nullifier (605 of
the 2104 ms of a 3000-record open) and the journal was the whole decoded log.
Both questions — "has this history already consumed nullifier n?" and "at
which height was transaction t accepted?" — are now answered by ONE
authenticated map, keyed by domain-separated 256-bit keys
(`nullifierKey`, `transactionKey`), whose value is the height that inserted the
key. Its root (`spentRoot`) is bound into every log tag MAC and the
checkpoint; the map's nodes are versioned rows of the Store's `durable_node`
table (space `spentSpace`), written with the entry that changed them.

Shape: a compressed binary trie on the key bits. Empty subtrees hash to
`emptyDigest`; a subtree holding exactly one key is that key's leaf
(`leafDigest key height`), at the highest level where it is alone; any other
subtree is a branch `branchDigest left right`. The root is therefore a
function of the logical map. An opening is the sibling digests from the root
down to the terminal (empty, or a leaf) on the key's path: O(log n) digests,
not 256.

This module pins the VERIFIER (what an at-use read checks). The insert, its
completeness and the collision-exhibiting soundness theorem (mirroring
`Theory.LogAccumulator.verify_sound` and `Theory.AuthMap.forgery_exhibits_collision`)
are KN2 stage (2).
-/
import Compiler.DurableCheckpointCodec
import Kernel.WorldRoot

namespace Minidregg.Compiler.DurableSpent

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec (nullifierStream)
open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier)

set_option autoImplicit false

/-- The Store node space of this map (`durable_node.space`). Space 1 is the log accumulator. -/
def spentSpace : Nat := 2
/-- The log accumulator's node space. -/
def accumulatorSpace : Nat := 1

def keyCustomization : List UInt8 := "DREGG/NATIVE-HOST/SPENT-KEY/v1".toUTF8.toList
def nodeCustomization : List UInt8 := "DREGG/NATIVE-HOST/SPENT-NODE/v1".toUTF8.toList

/-- A key: a cSHAKE256 digest over a domain tag and the canonical bytes. -/
def key (domain : UInt8) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash keyCustomization (domain :: bytes)).digest

/-- The key of a consumed nullifier (domain 1). -/
def nullifierKey (nullifier : StableNullifier) : Digest :=
  key 1 (nullifierStream.encode nullifier)

/-- The key of an accepted transaction id (domain 2). -/
def transactionKey (transactionId : TransactionId) : Digest :=
  key 2 (digestStream.encode transactionId)

/-- The 256 path bits of a key, most significant first. -/
def keyBits (k : Digest) : List Bool := Kernel.WorldRoot.bytesBits (digestStream.encode k)

def hashNode (tag : UInt8) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash nodeCustomization (tag :: bytes)).digest

def emptyDigest : Digest := hashNode 2 []
def leafDigest (k : Digest) (height : Nat) : Digest :=
  hashNode 0 (digestStream.encode k ++ StreamCodec.nat.encode height)
def branchDigest (left right : Digest) : Digest :=
  hashNode 1 (digestStream.encode left ++ digestStream.encode right)

/-- Where a key's walk ends. -/
inductive Terminal where
  | empty
  | leaf (k : Digest) (height : Nat)
  deriving DecidableEq, Repr

/-- An opening: the siblings from the root down (one per branch walked), and
the terminal at depth `siblings.length`. -/
structure Opening where
  siblings : List Digest
  terminal : Terminal
  deriving Repr

def Terminal.digest : Terminal → Digest
  | .empty => emptyDigest
  | .leaf k height => leafDigest k height

/-- Climb from the terminal: the sibling at depth `i` combines on the side the
key's bit `i` does not take. -/
def climb (bits : List Bool) (siblings : List Digest) (below : Digest) : Digest :=
  (bits.zip siblings).foldr (fun (bit, sibling) acc =>
    if bit then branchDigest sibling acc else branchDigest acc sibling) below

/-- **The verifier.** The opening proves `lookup k = answer` under `root`:
the terminal must be consistent with the answer (an empty subtree or another
key's leaf on the same prefix for absence; this key's leaf for presence), and
the climb must reach `root`. -/
def verify (root k : Digest) (answer : Option Nat) (opening : Opening) : Bool :=
  let bits := keyBits k
  let depth := opening.siblings.length
  decide (depth ≤ 256) &&
  (match opening.terminal, answer with
    | .empty, none => true
    | .leaf other height, some value => decide (other = k ∧ height = value)
    | .leaf other _, none => decide (other ≠ k ∧ (keyBits other).take depth = bits.take depth)
    | .empty, some _ => false) &&
  decide (climb (bits.take depth) opening.siblings opening.terminal.digest = root)

/-- The proposition a verified spent answer carries. -/
def Opens (root k : Digest) (answer : Option Nat) : Prop :=
  ∃ opening : Opening, verify root k answer opening = true

/-- A spent-map answer that passed `verify` against the authenticated root. -/
structure Answer (root k : Digest) where
  value : Option Nat
  opens : Opens root k value

/-- The empty map's root, and its absence opening (satisfying pole). -/
theorem empty_absent (k : Digest) : verify emptyDigest k none ⟨[], .empty⟩ = true := by
  simp [verify, climb, Terminal.digest]

/-- Presence cannot be claimed from an empty terminal (refuting pole). -/
theorem empty_present_refused (root k : Digest) (siblings : List Digest) (height : Nat) :
    verify root k (some height) ⟨siblings, .empty⟩ = false := by
  simp [verify]

/-! ## Store rows: reading an opening, inserting a key

The map's nodes are rows of `durable_node` in `spentSpace`: the row at a bit
prefix `p` is the subtree there — a leaf (the one key under `p`) or a branch
(the digests of its two children). An empty subtree has no row. Rows are
versioned by height; a reader asks for every prefix of its key at once and
gets each prefix's latest version at or below its height. Rows are UNTRUSTED:
the opening they produce is checked by `verify` against the authenticated root.
-/

inductive Row where
  | leaf (k : Digest) (height : Nat)
  | branch (left right : Digest)
  deriving DecidableEq, Repr

def rowStream : StreamCodec Row :=
  StreamCodec.xmap (StreamCodec.sum (StreamCodec.product digestStream StreamCodec.nat)
      (StreamCodec.product digestStream digestStream))
    (fun | .leaf k h => .inl (k, h) | .branch l r => .inr (l, r))
    (fun | .inl (k, h) => .leaf k h | .inr (l, r) => .branch l r)
    (by intro value; cases value <;> rfl)

def Row.digest : Row → Digest
  | .leaf k h => leafDigest k h
  | .branch l r => branchDigest l r

/-- The Store key of the row at a bit prefix. -/
def rowKey (prefixBits : List Bool) : List UInt8 := (StreamCodec.list StreamCodec.bool).encode prefixBits

/-- Every prefix of a key's path, root first (257 of them). -/
def prefixes (k : Digest) : List (List Bool) :=
  (List.range 257).map fun i => (keyBits k).take i

/-- Walk rows down a key's path: the opening they claim. -/
def walk (rows : List Bool → Option Row) (bits : List Bool) : Nat → List Bool → List Digest → Opening
  | 0, _, siblings => ⟨siblings.reverse, .empty⟩
  | fuel + 1, here, siblings =>
      match rows here with
      | none => ⟨siblings.reverse, .empty⟩
      | some (.leaf k h) => ⟨siblings.reverse, .leaf k h⟩
      | some (.branch l r) =>
          match bits[here.length]? with
          | none => ⟨siblings.reverse, .empty⟩
          | some bit => walk rows bits fuel (here ++ [bit]) ((if bit then l else r) :: siblings)

def openingOf (rows : List Bool → Option Row) (k : Digest) : Opening :=
  walk rows (keyBits k) 257 [] []

/-- Look a key up through rows, verified against the root: the answer, or a
refusal (the rows do not open to the root). -/
def lookupRows (rows : List Bool → Option Row) (root k : Digest) :
    Except String (Answer root k) :=
  let opening := openingOf rows k
  let answer := match opening.terminal with
    | .leaf other h => if other = k then some h else none
    | .empty => none
  if ok : verify root k answer opening = true then .ok ⟨answer, ⟨opening, ok⟩⟩
  else .error "spent map opening does not reach the authenticated spent root"

/-- The subtree replacing a terminal when `k` (absent) is inserted at depth
`depth`: its rows (prefix ↦ row) and digest. A leaf terminal of another key
splits down to their first differing bit. -/
def insertSubtree (k : Digest) (height : Nat) (depth : Nat) (terminal : Terminal) :
    List (List Bool × Row) × Digest :=
  let bits := keyBits k
  match terminal with
  | .empty => ([(bits.take depth, .leaf k height)], leafDigest k height)
  | .leaf other otherHeight =>
      let otherBits := keyBits other
      let differ := ((List.range 256).filter fun i => i ≥ depth ∧ bits[i]? ≠ otherBits[i]?).head?.getD 256
      let mine := leafDigest k height
      let theirs := leafDigest other otherHeight
      let bit := bits[differ]?.getD false
      let atDiffer : Row := if bit then .branch theirs mine else .branch mine theirs
      let rec up : Nat → Digest → List (List Bool × Row) → List (List Bool × Row) × Digest
        | 0, digest, rows => (rows, digest)
        | n + 1, digest, rows =>
            let level := depth + n
            let row : Row := if bits[level]?.getD false then .branch emptyDigest digest
              else .branch digest emptyDigest
            up n row.digest ((bits.take level, row) :: rows)
      up (differ - depth) atDiffer.digest
        [(bits.take differ, atDiffer), (bits.take (differ + 1), .leaf k height),
          (otherBits.take (differ + 1), .leaf other otherHeight)]

/-- Re-hash the ancestors of the replaced subtree with the opening's siblings. -/
def insertAncestors (bits : List Bool) : List Digest → Nat → Digest → List (List Bool × Row) →
    List (List Bool × Row) × Digest
  | [], _, digest, rows => (rows, digest)
  | sibling :: rest, level, digest, rows =>
      let (below, digestBelow) := insertAncestors bits rest (level + 1) digest rows
      let row : Row := if bits[level]?.getD false then .branch sibling digestBelow
        else .branch digestBelow sibling
      ((bits.take level, row) :: below, row.digest)

/-- Insert an ABSENT key at `height`, from its verified absence opening: the
new root and every row the append writes. -/
def insert (k : Digest) (height : Nat) (opening : Opening) : List (List Bool × Row) × Digest :=
  let (subRows, subDigest) := insertSubtree k height opening.siblings.length opening.terminal
  insertAncestors (keyBits k) opening.siblings 0 subDigest subRows

/-- Rows overlaid: the newest write of each prefix wins. -/
def overlay (store : List Bool → Option Row) (written : List (List Bool × Row)) : List Bool → Option Row :=
  fun p => match written.find? (·.1 = p) with
    | some (_, row) => some row
    | none => store p

/-- Insert keys one after another (each must be absent): the final root and
the rows to write (one per prefix, newest wins). -/
def insertAll (store : List Bool → Option Row) (root : Digest) (height : Nat) :
    List Digest → Except String (Digest × List (List Bool × Row))
  | [] => .ok (root, [])
  | k :: rest => do
      let answer ← lookupRows store root k
      if answer.value.isSome then
        throw "spent map already holds a key this record consumes (it disagrees with the executor)"
      let opening := openingOf store k
      let (rows, root') := insert k height opening
      let (finalRoot, later) ← insertAll (overlay store rows) root' height rest
      return (finalRoot, later ++ rows.filter fun row => !later.any (·.1 = row.1))

/-- The keys a record inserts: its transaction id, then its nullifiers. -/
def recordKeys (transactionId : TransactionId) (nullifiers : List StableNullifier) : List Digest :=
  transactionKey transactionId :: nullifiers.map nullifierKey

#assert_axioms empty_absent
#assert_axioms empty_present_refused

end Minidregg.Compiler.DurableSpent
