/-
# Compiler.DurableIndex — the Store's one authenticated keyed trie, at the deployed shape

KN2-STORE-OPEN unified trie (DEPUTY-KERNEL ruling 2026-10-07). The spent map,
the transaction index and the keyed index families (presence, links, backlinks,
fleet) are families of ONE compressed authenticated trie (`Theory.AuthTrie`)
with one root. This module pins its deployed shape:

* `IndexKey` — family byte, 32-byte primary, 32-byte secondary: 65 bytes, 520
  path bits for every key (`bitsOf_length`); a family without a secondary pads
  it with `noSecondary` (`key_injective` covers the padding: different
  families, primaries or secondaries never share bytes).
* `dig` — the node digest: cSHAKE256 under `nodeCustomization` over
  `nodeBytes` (injective, `nodeBytes_injective`).
* `collision_is_cshake` — a node collision of `dig` is a cSHAKE256 collision
  (two different inputs, one 32-byte output).
* `lookup_sound` / `reveal_sound` — `Theory.AuthTrie.verify_sound` and
  `Theory.AuthTrie.reveal_sound` instantiated at THIS key path and THIS digest:
  a verified single answer is the map's, and a verified reveal answers exactly
  the members under its prefix, or a cSHAKE256 collision is exhibited. The
  security floor is therefore cSHAKE256's COLLISION resistance at a 256-bit
  output (about 2^128 work), not its second-preimage resistance.
-/
import Theory.AuthTrieRange
import Compiler.Sp800185Cshake256
import Kernel.WorldRoot
import Compiler.DurableReceiverCodec
import Theory.AssertCompiled

namespace Minidregg.Compiler.DurableIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.AuthTrie (NodeIn Collision WF entries tree)

set_option autoImplicit false

/-! ## Keys -/

/-- A key of the one trie: its family, its primary (a 32-byte cSHAKE256 output) and
its secondary (32 bytes; `noSecondary` for a single-valued family). -/
structure IndexKey where
  family : UInt8
  primary : Digest256
  secondary : Digest256
  deriving DecidableEq, Repr

/-- The padding of a family that has no secondary. -/
def noSecondary : Digest256 := 0

/-- The key's 65 bytes: the family byte, then the primary, then the secondary. -/
def IndexKey.bytes (k : IndexKey) : List UInt8 :=
  k.family :: ((fixedStream 32).encode k.primary ++ (fixedStream 32).encode k.secondary)

theorem IndexKey.bytes_length (k : IndexKey) : k.bytes.length = 65 := by
  simp [IndexKey.bytes, fixedStream_encode_length]

private theorem fixed_injective {a b : Digest256}
    (same : (fixedStream 32).encode a = (fixedStream 32).encode b) : a = b := by
  have decodedA := (fixedStream 32).decodePrefix_encode a []
  have decodedB := (fixedStream 32).decodePrefix_encode b []
  rw [same] at decodedA
  rw [decodedA] at decodedB
  exact (Prod.mk.inj (Option.some.inj decodedB)).1

/-- **The key encoding is injective**, padding included: equal bytes are the same
family, primary and secondary. In particular keys of two families never share a
path (`family_disjoint`). -/
theorem key_injective {k₁ k₂ : IndexKey} (same : k₁.bytes = k₂.bytes) : k₁ = k₂ := by
  obtain ⟨f₁, p₁, s₁⟩ := k₁
  obtain ⟨f₂, p₂, s₂⟩ := k₂
  simp only [IndexKey.bytes, List.cons.injEq] at same
  obtain ⟨hf, rest⟩ := same
  have lenEq : ((fixedStream 32).encode p₁).length = ((fixedStream 32).encode p₂).length := by
    simp [fixedStream_encode_length]
  obtain ⟨hp, hs⟩ := List.append_inj rest lenEq
  rw [hf, fixed_injective hp, fixed_injective hs]

theorem family_disjoint {k₁ k₂ : IndexKey} (differ : k₁.family ≠ k₂.family) : k₁.bytes ≠ k₂.bytes :=
  fun same => differ (congrArg IndexKey.family (key_injective same))

/-- The key's path in the trie: its 520 bits. -/
def bitsOf (k : IndexKey) : List Bool := Kernel.WorldRoot.bytesBits k.bytes

/-- Every key path has the same length (the premise of the trie's soundness). -/
theorem bitsOf_length (k : IndexKey) : (bitsOf k).length = 520 := by
  simp [bitsOf, Kernel.WorldRoot.bytesBits_length, IndexKey.bytes_length]

/-! ## The node digest -/

def nodeCustomization : List UInt8 := "DREGG/NATIVE-HOST/INDEX-NODE/v1".toUTF8.toList

/-- What a node digest hashes: a tag byte, then the leaf's key bytes (fixed length)
and value, or the branch's two child digests. -/
def nodeBytes : NodeIn IndexKey (List UInt8) Digest → List UInt8
  | .empty => [2]
  | .leaf k v => 0 :: (k.bytes ++ v)
  | .branch l r => 1 :: (StreamCodec.product digestStream digestStream).encode (l, r)

theorem nodeBytes_injective {a b : NodeIn IndexKey (List UInt8) Digest}
    (same : nodeBytes a = nodeBytes b) : a = b := by
  cases a with
  | empty => cases b <;> simp_all [nodeBytes]
  | leaf k v =>
      cases b with
      | empty => simp [nodeBytes] at same
      | branch _ _ => simp [nodeBytes] at same
      | leaf k' v' =>
          simp only [nodeBytes, List.cons.injEq, true_and] at same
          have lenEq : k.bytes.length = k'.bytes.length := by rw [k.bytes_length, k'.bytes_length]
          obtain ⟨hk, hv⟩ := List.append_inj same lenEq
          rw [key_injective hk, hv]
  | branch l r =>
      cases b with
      | empty => simp [nodeBytes] at same
      | leaf _ _ => simp [nodeBytes] at same
      | branch l' r' =>
          simp only [nodeBytes, List.cons.injEq, true_and] at same
          have decoded := (StreamCodec.product digestStream digestStream).decodePrefix_encode (l, r) []
          rw [same, (StreamCodec.product digestStream digestStream).decodePrefix_encode (l', r') []] at decoded
          have := (Prod.mk.inj (Option.some.inj decoded)).1
          simp only [Prod.mk.injEq] at this
          rw [this.1, this.2]

/-- The deployed node digest. -/
def dig (node : NodeIn IndexKey (List UInt8) Digest) : Digest :=
  (Sp800185Cshake256.hash nodeCustomization (nodeBytes node)).digest

/-- **A node collision is a cSHAKE256 collision**: two different inputs under the
node customization with one 32-byte output. -/
theorem collision_is_cshake (collision : Collision dig) :
    ∃ x y : List UInt8, x ≠ y ∧
      Sp800185Cshake256.hash nodeCustomization x = Sp800185Cshake256.hash nodeCustomization y := by
  obtain ⟨a, b, differ, same⟩ := collision
  refine ⟨nodeBytes a, nodeBytes b, fun eq => differ (nodeBytes_injective eq), ?_⟩
  have bytesEq := congrArg Sp800185Cshake256.digestBytesLE same
  simp only [dig, Sp800185Cshake256.Output.digest] at bytesEq
  rw [Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ (Sp800185Cshake256.hash _ _).length_exact,
    Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ (Sp800185Cshake256.hash _ _).length_exact] at bytesEq
  cases houtA : Sp800185Cshake256.hash nodeCustomization (nodeBytes a)
  cases houtB : Sp800185Cshake256.hash nodeCustomization (nodeBytes b)
  rw [houtA, houtB] at bytesEq
  simp only at bytesEq
  subst bytesEq
  rfl

/-! ## Soundness at the deployed shape -/

/-- The canonical root of a logical map (key ↦ value bytes). -/
def rootOf (kvs : List (IndexKey × List UInt8)) : Digest := tree dig 520 (entries bitsOf kvs)

/-- **A verified single answer is the map's** (presence with its value, or verified
absence), or a cSHAKE256 collision is exhibited. -/
theorem lookup_sound (kvs : List (IndexKey × List UInt8)) (wf : WF 520 (entries bitsOf kvs))
    (k : IndexKey) (answer : Option (List UInt8))
    (opening : Theory.AuthTrie.Opening IndexKey (List UInt8) Digest)
    (accepted : Theory.AuthTrie.verify dig bitsOf (rootOf kvs) k answer opening = true) :
    answer = Theory.AuthTrie.lookup (entries bitsOf kvs) k ∨
      ∃ x y : List UInt8, x ≠ y ∧
        Sp800185Cshake256.hash nodeCustomization x = Sp800185Cshake256.hash nodeCustomization y :=
  (Theory.AuthTrie.verify_sound dig bitsOf 520 bitsOf_length kvs wf k answer opening accepted).imp_right
    collision_is_cshake

/-- **A verified reveal answers exactly the members under its prefix** — none
omitted (so an empty answer is a verified absence of the whole family member
set), none forged — or a cSHAKE256 collision is exhibited. -/
theorem reveal_sound (kvs : List (IndexKey × List UInt8)) (wf : WF 520 (entries bitsOf kvs))
    (p : List Bool) (reveal : Theory.AuthTrie.Reveal IndexKey (List UInt8) Digest)
    (accepted : Theory.AuthTrie.revealVerify dig bitsOf 520 (rootOf kvs) p reveal = true) :
    (∀ k v, (k, v) ∈ reveal.answer bitsOf p ↔ (k, v) ∈ kvs ∧ (bitsOf k).take p.length = p) ∨
      ∃ x y : List UInt8, x ≠ y ∧
        Sp800185Cshake256.hash nodeCustomization x = Sp800185Cshake256.hash nodeCustomization y :=
  (Theory.AuthTrie.reveal_sound dig bitsOf 520 bitsOf_length kvs wf p reveal accepted).imp_right
    collision_is_cshake

/-! ## Families and their keys

One byte names a family. The primary is cSHAKE256 under `keyCustomization`
over the family byte and the canonical bytes of what the family is keyed by
(as 32 octets: a cSHAKE256 output is below `256^32`, so `primaryOf` keeps it
whole). A single-valued family pads its secondary with `noSecondary`. -/

namespace Family
/-- A consumed nullifier ↦ the height that consumed it. -/
def spent : UInt8 := 0
/-- An accepted transaction id ↦ the height that accepted it. -/
def transaction : UInt8 := 1
end Family

def keyCustomization : List UInt8 := "DREGG/NATIVE-HOST/INDEX-KEY/v1".toUTF8.toList

/-- The 32-octet primary (or secondary) of `bytes` in `family`. -/
def primaryOf (family : UInt8) (bytes : List UInt8) : Digest256 :=
  ⟨(Sp800185Cshake256.hash keyCustomization (family :: bytes)).digest.value % 256 ^ 32,
    Nat.mod_lt _ (by decide)⟩

/-- The key of a consumed nullifier (family 0). -/
def nullifierKey (nullifier : Kernel.DurableDataIntent.StableNullifier) : IndexKey :=
  ⟨Family.spent, primaryOf Family.spent (DurableReceiverCodec.nullifierStream.encode nullifier), noSecondary⟩

/-- The key of an accepted transaction id (family 1). -/
def transactionKey (transactionId : Kernel.DurableDataIntent.TransactionId) : IndexKey :=
  ⟨Family.transaction, primaryOf Family.transaction (digestStream.encode transactionId), noSecondary⟩

/-- **A spent key is never a transaction key**, whatever the inputs: the family
byte differs, so the two never share a trie path (`family_disjoint`). -/
theorem nullifierKey_ne_transactionKey (nullifier : Kernel.DurableDataIntent.StableNullifier)
    (transactionId : Kernel.DurableDataIntent.TransactionId) :
    nullifierKey nullifier ≠ transactionKey transactionId := by
  intro same
  have families := congrArg IndexKey.family same
  simp [nullifierKey, transactionKey, Family.spent, Family.transaction] at families

/-- The value of a family-0/1 row: the height, as a canonical natural. -/
def heightValue (height : Nat) : List UInt8 := StreamCodec.nat.encode height

/-- Read a height value back: only the canonical encoding of a height is one
(`heightOf_some`), so a verified value names exactly one height. -/
def heightOf (value : List UInt8) : Option Nat :=
  match StreamCodec.nat.decodePrefix value with
  | some (height, []) => if heightValue height = value then some height else none
  | _ => none

@[simp] theorem heightOf_heightValue (height : Nat) : heightOf (heightValue height) = some height := by
  have decoded := StreamCodec.nat.decodePrefix_encode height []
  rw [List.append_nil] at decoded
  simp [heightOf, heightValue, decoded]

theorem heightOf_some {value : List UInt8} {height : Nat} (read : heightOf value = some height) :
    value = heightValue height := by
  unfold heightOf at read
  split at read
  · split at read
    · rename_i same; cases read; exact same.symm
    · cases read
  · cases read

/-! ## The verifier and its answers -/

abbrev Opening := Theory.AuthTrie.Opening IndexKey (List UInt8) Digest
abbrev Terminal := Theory.AuthTrie.Terminal IndexKey (List UInt8)

/-- The empty trie's root. -/
def emptyDigest : Digest := dig .empty

/-- **The verifier** (one key): `Theory.AuthTrie.verify` at this digest and path. -/
def verify (root : Digest) (k : IndexKey) (answer : Option (List UInt8)) (opening : Opening) : Bool :=
  Theory.AuthTrie.verify dig bitsOf root k answer opening

/-- The proposition a verified answer carries. -/
def Opens (root : Digest) (k : IndexKey) (answer : Option (List UInt8)) : Prop :=
  ∃ opening : Opening, verify root k answer opening = true

/-- An answer that passed `verify` against the authenticated root. -/
structure Answer (root : Digest) (k : IndexKey) where
  value : Option (List UInt8)
  opens : Opens root k value

/-- The height a family-0/1 answer carries (`none`: verified absence, or a value
that is not a height, which an honest trie never holds). -/
def Answer.height {root : Digest} {k : IndexKey} (answer : Answer root k) : Option Nat :=
  answer.value.bind heightOf

/-- **The verified answer is the map's** (at the deployed shape): whatever opening
was accepted, its value is the logical map's lookup, or cSHAKE256 collides. -/
theorem Answer.sound {kvs : List (IndexKey × List UInt8)} {k : IndexKey}
    (wf : WF 520 (entries bitsOf kvs)) (answer : Answer (rootOf kvs) k) :
    answer.value = Theory.AuthTrie.lookup (entries bitsOf kvs) k ∨
      ∃ x y : List UInt8, x ≠ y ∧
        Sp800185Cshake256.hash nodeCustomization x = Sp800185Cshake256.hash nodeCustomization y := by
  obtain ⟨opening, accepted⟩ := answer.opens
  exact lookup_sound kvs wf k answer.value opening accepted

theorem empty_absent (k : IndexKey) : verify emptyDigest k none ⟨[], .empty⟩ = true := by
  simp [verify, Theory.AuthTrie.verify, Theory.AuthTrie.climb, Theory.AuthTrie.Terminal.input, emptyDigest]

theorem empty_present_refused (root : Digest) (k : IndexKey) (siblings : List Digest) (v : List UInt8) :
    verify root k (some v) ⟨siblings, .empty⟩ = false := by
  simp [verify, Theory.AuthTrie.verify]

/-! ## Store rows (node space `indexSpace`)

The row at a bit prefix is the subtree there: a leaf (the one key under it)
or a branch (its children's digests). Rows are versioned by height and
UNTRUSTED: every opening built from them is checked by `verify`. The walk is
given the digest it EXPECTS at each prefix (the root, then the parent branch's
child digest), and an expected empty digest is an empty terminal whatever row
sits there — so rows left under a subtree that later collapsed or emptied are
never read, and no deletion row is needed. -/

/-- The Store node space of the trie (`durable_node.space`). Space 1 is the log
accumulator; space 2 (the separate spent map) is retired. -/
def indexSpace : Nat := 3
def accumulatorSpace : Nat := 1

inductive Row where
  | leaf (k : IndexKey) (value : List UInt8)
  | branch (left right : Digest)
  deriving DecidableEq, Repr

def keyStream : StreamCodec IndexKey :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.byte (StreamCodec.product (fixedStream 32) (fixedStream 32)))
    (fun k => (k.family, k.primary, k.secondary)) (fun w => ⟨w.1, w.2.1, w.2.2⟩) (by intro k; rfl)

def rowStream : StreamCodec Row :=
  StreamCodec.xmap (StreamCodec.sum (StreamCodec.product keyStream bytesStream)
      (StreamCodec.product digestStream digestStream))
    (fun | .leaf k v => .inl (k, v) | .branch l r => .inr (l, r))
    (fun | .inl (k, v) => .leaf k v | .inr (l, r) => .branch l r)
    (by intro value; cases value <;> rfl)

def Row.digest : Row → Digest
  | .leaf k v => dig (.leaf k v)
  | .branch l r => dig (.branch l r)

/-- Bits packed eight to an octet, most significant first (the last octet zero-padded). -/
def packBits (bits : List Bool) : List UInt8 :=
  (List.range ((bits.length + 7) / 8)).map fun i =>
    let chunk := (bits.drop (8 * i)).take 8
    UInt8.ofNat (chunk.foldl (fun acc bit => acc * 2 + (if bit then 1 else 0)) (0 : Nat) * 2 ^ (8 - chunk.length))

/-- The Store key of the row at a bit prefix: its length, then its packed bits. -/
def rowKey (prefixBits : List Bool) : List UInt8 :=
  StreamCodec.nat.encode prefixBits.length ++ packBits prefixBits

/-- The opening the rows claim for `bits`, walking from `here` (whose expected
digest is `expected`) with the siblings collected so far (deepest first). -/
def walk (rows : List Bool → Option Row) (bits : List Bool) :
    Nat → List Bool → Digest → List Digest → Opening
  | 0, _, _, siblings => ⟨siblings.reverse, .empty⟩
  | fuel + 1, here, expected, siblings =>
      if expected = emptyDigest then ⟨siblings.reverse, .empty⟩ else
      match rows here with
      | none => ⟨siblings.reverse, .empty⟩
      | some (.leaf k v) => ⟨siblings.reverse, .leaf k v⟩
      | some (.branch l r) =>
          match bits[here.length]? with
          | none => ⟨siblings.reverse, .empty⟩
          | some bit => walk rows bits fuel (here ++ [bit]) (if bit then r else l)
              ((if bit then l else r) :: siblings)

def openingOf (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) : Opening :=
  walk rows (bitsOf k) 521 [] root []

/-- The answer an opening claims for `k`. -/
def Opening.claims (opening : Opening) (k : IndexKey) : Option (List UInt8) :=
  match opening.terminal with
  | .leaf other v => if other = k then some v else none
  | .empty => none

/-- Look `k` up through rows, verified against `root`: the answer, or a refusal. -/
def lookupRows (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) :
    Except String (Answer root k) :=
  let opening := openingOf rows root k
  if ok : verify root k (opening.claims k) opening = true then .ok ⟨opening.claims k, ⟨opening, ok⟩⟩
  else .error "index opening does not reach the authenticated index root"

/-! ## Setting a key: insert, update and delete as one climb -/

/-- A subtree during a set: empty, one leaf, or a node of two or more entries. -/
inductive Sub where
  | empty
  | leaf (k : IndexKey) (v : List UInt8)
  | node (digest : Digest)

def Sub.digest : Sub → Digest
  | .empty => emptyDigest
  | .leaf k v => dig (.leaf k v)
  | .node d => d

/-- What a sibling digest stands for: empty, the leaf its row holds (checked
against the digest), or a node. -/
def siblingSub (rows : List Bool → Option Row) (at_ : List Bool) (sibling : Digest) : Sub :=
  if sibling = emptyDigest then .empty else
  match rows at_ with
  | some (.leaf k v) => if dig (.leaf k v) = sibling then .leaf k v else .node sibling
  | _ => .node sibling

/-- One level up: a lone leaf beside an empty subtree rises (the compressed
trie keeps a leaf at the highest level where it is alone); two empties are
empty; anything else is a branch, written as a row. -/
def combine (bit : Bool) (below sibling : Sub) : Sub × Option Row :=
  match below, sibling with
  | .empty, .empty => (.empty, none)
  | .empty, .leaf k v => (.leaf k v, some (.leaf k v))
  | .leaf k v, .empty => (.leaf k v, some (.leaf k v))
  | b, s =>
      let row : Row := if bit then .branch s.digest b.digest else .branch b.digest s.digest
      (.node row.digest, some row)

/-- Rebuild the path's ancestors (top first) over the new subtree at the
terminal depth: the new root's subtree and the rows written. -/
def rebuild (bits : List Bool) : List Sub → Nat → Sub → List (List Bool × Row) →
    Sub × List (List Bool × Row)
  | [], _, below, rows => (below, rows)
  | sibling :: rest, level, below, rows =>
      let (under, written) := rebuild bits rest (level + 1) below rows
      let (here, row?) := combine (bits[level]?.getD false) under sibling
      (here, match row? with
        | some row => (bits.take level, row) :: written
        | none => written)

/-- Two leaves split at depth `depth`: the chain of one-sided branches down to
their first differing bit, the branch there, and the two leaves below it. -/
def split (depth : Nat) (k : IndexKey) (v : List UInt8) (other : IndexKey) (otherValue : List UInt8) :
    Sub × List (List Bool × Row) :=
  let bits := bitsOf k
  let otherBits := bitsOf other
  let differ := ((List.range 520).filter fun i => i ≥ depth ∧ bits[i]? ≠ otherBits[i]?).head?.getD 520
  let mine := dig (.leaf k v)
  let theirs := dig (.leaf other otherValue)
  let atDiffer : Row := if bits[differ]?.getD false then .branch theirs mine else .branch mine theirs
  let rec up : Nat → Digest → List (List Bool × Row) → Sub × List (List Bool × Row)
    | 0, digest, rows => (.node digest, rows)
    | n + 1, digest, rows =>
        let level := depth + n
        let row : Row := if bits[level]?.getD false then .branch emptyDigest digest
          else .branch digest emptyDigest
        up n row.digest ((bits.take level, row) :: rows)
  up (differ - depth) atDiffer.digest
    [(bits.take differ, atDiffer), (bits.take (differ + 1), .leaf k v),
      (otherBits.take (differ + 1), .leaf other otherValue)]

/-- **Set `k` to `value`** (`none` deletes) from rows, against `root`: the
opening the rows give is verified first (a refusal if it does not reach the
root), then the new root and every row the change writes. Insert, update and
delete are one walk and one climb; a delete collapses a lone leaf upward. -/
def set (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) (value : Option (List UInt8)) :
    Except String (Digest × List (List Bool × Row)) := do
  let opening := openingOf rows root k
  unless verify root k (opening.claims k) opening do
    throw "index opening does not reach the authenticated index root"
  let bits := bitsOf k
  let depth := opening.siblings.length
  let siblings := (List.range depth).zip opening.siblings |>.map fun (level, sibling) =>
    siblingSub rows (bits.take level ++ [!(bits[level]?.getD false)]) sibling
  let bottom : Option (Sub × List (List Bool × Row)) :=
    match opening.terminal, value with
    | .empty, none => none
    | .empty, some v => some (.leaf k v, [(bits.take depth, .leaf k v)])
    | .leaf other _, none =>
        if other = k then some (.empty, []) else none
    | .leaf other otherValue, some v =>
        if other = k then
          if otherValue = v then none else some (.leaf k v, [(bits.take depth, .leaf k v)])
        else some (split depth k v other otherValue)
  match bottom with
  | none => return (root, [])
  | some (sub, written) =>
      let (top, rowsWritten) := rebuild bits siblings 0 sub written
      return (top.digest, rowsWritten)

/-- Rows overlaid: the newest write of each prefix wins. -/
def overlay (store : List Bool → Option Row) (written : List (List Bool × Row)) : List Bool → Option Row :=
  fun p => match written.find? (·.1 = p) with
    | some (_, row) => some row
    | none => store p

/-- Apply changes one after another: the final root and the rows to write (one
per prefix, newest wins). -/
def setAll (store : List Bool → Option Row) (root : Digest) :
    List (IndexKey × Option (List UInt8)) → Except String (Digest × List (List Bool × Row))
  | [] => .ok (root, [])
  | (k, value) :: rest => do
      let (root', rows) ← set store root k value
      let (finalRoot, later) ← setAll (overlay store rows) root' rest
      return (finalRoot, later ++ rows.filter fun row => !later.any (·.1 = row.1))

/-- The prefixes a set or lookup of `k` reads down to `depth` bits: every prefix
of its path and each one's sibling. -/
def readPrefixes (k : IndexKey) (depth : Nat) : List (List Bool) :=
  let bits := bitsOf k
  (List.range (min depth 520 + 1)).flatMap fun i =>
    let here := bits.take i
    match bits[i]? with
    | some bit => [here, bits.take i ++ [!bit]]
    | none => [here]

/-! ## Reveals over rows -/

/-- Every leaf of the subtree whose digest is `expected` at prefix `here`, by
following rows (untrusted; `revealVerify` checks the result). -/
def collect (rows : List Bool → Option Row) : Nat → List Bool → Digest → List (IndexKey × List UInt8)
  | 0, _, _ => []
  | fuel + 1, here, expected =>
      if expected = emptyDigest then [] else
      match rows here with
      | some (.leaf k v) => [(k, v)]
      | some (.branch l r) => collect rows fuel (here ++ [false]) l ++ collect rows fuel (here ++ [true]) r
      | none => []

/-- The reveal the rows give for prefix `p`: walk down `p` while there is a
branch, then every member of the subtree where the walk stopped. -/
def revealOf (rows : List Bool → Option Row) (root : Digest) (p : List Bool) :
    Theory.AuthTrie.Reveal IndexKey (List UInt8) Digest :=
  let rec down : Nat → List Bool → Digest → List Digest → Theory.AuthTrie.Reveal IndexKey (List UInt8) Digest
    | 0, _, _, siblings => ⟨siblings.reverse, []⟩
    | fuel + 1, here, expected, siblings =>
        if expected = emptyDigest then ⟨siblings.reverse, []⟩ else
        if here.length ≥ p.length then ⟨siblings.reverse, collect rows (521 - here.length) here expected⟩ else
        match rows here with
        | some (.leaf k v) => ⟨siblings.reverse, [(k, v)]⟩
        | some (.branch l r) =>
            let bit := p[here.length]?.getD false
            down fuel (here ++ [bit]) (if bit then r else l) ((if bit then l else r) :: siblings)
        | none => ⟨siblings.reverse, []⟩
  down 521 [] root []

/-- A reveal that passed `revealVerify` against the authenticated root. -/
structure Revealed (root : Digest) (p : List Bool) where
  reveal : Theory.AuthTrie.Reveal IndexKey (List UInt8) Digest
  verified : Theory.AuthTrie.revealVerify dig bitsOf 520 root p reveal = true

/-- The members under `p`: exactly the map's (`reveal_sound`), so an empty list is a verified absence. -/
def Revealed.members {root : Digest} {p : List Bool} (revealed : Revealed root p) : List (IndexKey × List UInt8) :=
  revealed.reveal.answer bitsOf p

def revealRows (rows : List Bool → Option Row) (root : Digest) (p : List Bool) :
    Except String (Revealed root p) :=
  let reveal := revealOf rows root p
  if ok : Theory.AuthTrie.revealVerify dig bitsOf 520 root p reveal = true then .ok ⟨reveal, ok⟩
  else .error "index reveal does not reach the authenticated index root (a member is missing or forged)"

/-! ## The rows of a record (families 0 and 1)

What an append changes is a pure function of the appended record: its
transaction id and each nullifier it consumes map to the record's height
(`IndexRows.changes`). `IndexRows.apply` performs them on the Store's rows, and
refuses a key the trie already holds (the executor never accepts a transaction
id twice or consumes a nullifier twice; a disagreement is a refusal, not an
overwrite). `IndexRows.changes_exact` is the model theorem: over the logical map,
the map after the append is the map before updated by the record's changes, where
"the map" of a history is defined without the trie — a key ↦ the height of the
first record that carries it (`IndexRows.declared`). -/

/-- The logical map after setting `k` (`none` deletes). -/
def modelSet (m : List (IndexKey × List UInt8)) (k : IndexKey) (value : Option (List UInt8)) :
    List (IndexKey × List UInt8) :=
  m.filter (·.1 ≠ k) ++ (value.map (k, ·)).toList

/-- A key's value in a logical map. -/
def mapLookup (m : List (IndexKey × List UInt8)) (k : IndexKey) : Option (List UInt8) :=
  (m.find? (·.1 = k)).map (·.2)

/-- A list of changes applied to a logical map, in order. -/
def modelApply (m : List (IndexKey × List UInt8)) (changes : List (IndexKey × Option (List UInt8))) :
    List (IndexKey × List UInt8) :=
  changes.foldl (fun acc change => modelSet acc change.1 change.2) m

namespace IndexRows

open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier)

/-- The keys a record inserts: its transaction id, then its nullifiers. -/
def keys (transactionId : TransactionId) (nullifiers : List StableNullifier) : List IndexKey :=
  transactionKey transactionId :: nullifiers.map nullifierKey

/-- **The rows of a record**: each of its keys ↦ its height. -/
def changes (height : Nat) (transactionId : TransactionId) (nullifiers : List StableNullifier) :
    List (IndexKey × Option (List UInt8)) :=
  (keys transactionId nullifiers).map fun k => (k, some (heightValue height))

/-- The families-0/1 map of a history, defined without the trie: a key ↦ the
height of the first record that carries it. -/
def declared (records : List Kernel.DurableReceiver.IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  ((records.zipIdx 1).find? fun entry => k ∈ keys entry.1.transactionId entry.1.nullifiers).map
    fun entry => heightValue entry.2

theorem mapLookup_modelSet_some (m : List (IndexKey × List UInt8)) (k k' : IndexKey) (v : List UInt8) :
    mapLookup (modelSet m k' (some v)) k = if k = k' then some v else mapLookup m k := by
  unfold mapLookup modelSet
  induction m with
  | nil => by_cases h : k = k' <;> simp [h, eq_comm]
  | cons e rest ih =>
      by_cases h : k = k'
      · subst h
        by_cases he : e.1 = k <;> simp [he, List.filter_cons] at ih ⊢ <;> exact ih
      · have h' : k' ≠ k := Ne.symm h
        by_cases he : e.1 = k
        · have hne : e.1 ≠ k' := he ▸ h
          simp [h, he, hne, List.filter_cons]
        · by_cases he' : e.1 = k' <;> simp [h, h', he, he', List.filter_cons, List.find?_cons] at ih ⊢ <;> exact ih

theorem mapLookup_modelApply_same (v : List UInt8) :
    ∀ (ks : List IndexKey) (m : List (IndexKey × List UInt8)) (k : IndexKey),
      mapLookup (modelApply m (ks.map fun k => (k, some v))) k =
        if k ∈ ks then some v else mapLookup m k
  | [], m, k => by simp [modelApply]
  | k' :: rest, m, k => by
      have step := mapLookup_modelApply_same v rest (modelSet m k' (some v)) k
      simp only [modelApply, List.map_cons, List.foldl_cons] at step ⊢
      rw [step, mapLookup_modelSet_some]
      by_cases inRest : k ∈ rest
      · simp [inRest]
      · by_cases same : k = k' <;> simp [inRest, same]

/-- **The model theorem.** If the map before the append is the history's map,
and the record's keys are fresh in it (the executor's guarantee, and what
`apply` refuses otherwise), then the map before updated by the record's rows is
the map of the history with the record appended. -/
theorem changes_exact (records : List Kernel.DurableReceiver.IntentRecord)
    (record : Kernel.DurableReceiver.IntentRecord) (m : List (IndexKey × List UInt8))
    (before : ∀ k, mapLookup m k = declared records k)
    (fresh : ∀ k ∈ keys record.transactionId record.nullifiers, declared records k = none) (k : IndexKey) :
    mapLookup (modelApply m (changes (records.length + 1) record.transactionId record.nullifiers)) k =
      declared (records ++ [record]) k := by
  rw [changes, mapLookup_modelApply_same]
  unfold declared
  rw [List.zipIdx_append, List.find?_append]
  by_cases mem : k ∈ keys record.transactionId record.nullifiers
  · have none : declared records k = none := fresh k mem
    unfold declared at none
    rw [Option.map_eq_none_iff] at none
    simp [mem, none, Nat.add_comm]
  · rw [if_neg mem, before]
    unfold declared
    cases hfind : (records.zipIdx 1).find? (fun entry => k ∈ keys entry.1.transactionId entry.1.nullifiers) with
    | some found => simp
    | none => simp [mem]

/-- Insert the record's keys at `height` on the Store's rows, against `root`:
the new root and the rows to write. A key already present is refused. -/
def apply (store : List Bool → Option Row) (root : Digest) (height : Nat)
    (transactionId : TransactionId) (nullifiers : List StableNullifier) :
    Except String (Digest × List (List Bool × Row)) :=
  let rec insert (store : List Bool → Option Row) (root : Digest) :
      List IndexKey → Except String (Digest × List (List Bool × Row))
    | [] => .ok (root, [])
    | k :: rest => do
        let answer ← lookupRows store root k
        if answer.value.isSome then
          throw "the index already holds a key this record inserts (it disagrees with the executor)"
        let (root', rows) ← set store root k (some (heightValue height))
        let (finalRoot, later) ← insert (overlay store rows) root' rest
        return (finalRoot, later ++ rows.filter fun row => !later.any (·.1 = row.1))
  insert store root (keys transactionId nullifiers)

end IndexRows

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

#assert_axioms key_injective
#assert_axioms family_disjoint
#assert_axioms bitsOf_length
#assert_axioms nodeBytes_injective
#assert_axioms collision_is_cshake
#assert_axioms lookup_sound
#assert_axioms reveal_sound
#assert_axioms nullifierKey_ne_transactionKey
#assert_axioms heightOf_heightValue
#assert_axioms heightOf_some
#assert_axioms Answer.sound
#assert_axioms empty_absent
#assert_axioms empty_present_refused
#assert_axioms IndexRows.mapLookup_modelSet_some
#assert_axioms IndexRows.changes_exact
#assert_compiled Probe.incremental_matches_canonical
#assert_compiled Probe.wrong_root_refused

end Minidregg.Compiler.DurableIndex
