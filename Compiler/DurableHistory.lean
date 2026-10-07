/-
# Compiler.DurableHistory — history records are read only through their inclusion proof

KN2-STORE-OPEN (root decision, PRIORITY-ON-RETURN #6): the Store open no longer
decodes, chains and MACs every record. Old records are verified AT USE, through
an authenticated structure: the log accumulator of `Theory.LogAccumulator`
instantiated at the deployed hash.

* **Leaf** of height `h`: `leafDigest h record chain root` — cSHAKE256 over the
  height, the hash of the RAW stored record bytes (nothing is decoded before it
  is verified), the log chain after `h` and the world root after `h`.
* **Node**: `nodeDigest l r`, cSHAKE256 under its own customization. This is the
  deployed hash (`Sp800185Cshake256.hash`), not a model: the collision disjunct
  of `verifyAt_sound` is a cSHAKE256 collision, the same floor as the log chain
  and the world root.
* **Frontier**: the peaks after `n` leaves. The Host binds it (its digest
  `frontierDigest`) into every entry's tag MAC and into the checkpoint; the
  MINIANC2 head anchor fixes the head entry's exact bytes. So a frontier read
  from a verified head tag is "the MAC'd, anchor-bound root".
* **Trailer** (the Store's tag column, v3): the root and chain after `h`, the
  frontier digest and spent root after `h`, then the MAC (`tagMac`) over all
  four. The chain binds the record (it hashes it); the MAC binds the rest.

The Store hands Lean `RawEntry` and `RawNode` values. Their fields are PRIVATE
to this module: no other module can read stored history bytes except through
`verifyAt`, whose only success value is `Verified`, which carries the inclusion
check. That is the "no read path returns unverified bytes" property, enforced
by the compiler; `verifyAt_included`, `verifyAt_bytes` and `verifyAt_sound`
state what a `Verified` value means.
-/
import Compiler.DurableCheckpointCodec
import Theory.LogAccumulator
import Compiler.DurableSpent

namespace Minidregg.Compiler.DurableHistory

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LogAccumulator (verify block Honest NodeCollision frontierOf push)
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableCheckpointCodec (MacKey logTagLabel frontierStream)
open Minidregg.Compiler.Sp800185Cshake256 (kmac256Bytes)

set_option autoImplicit false

/-! ## The deployed hashes -/

def recordCustomization : List UInt8 := "DREGG/NATIVE-HOST/LOG-RECORD/v1".toUTF8.toList
def leafCustomization : List UInt8 := "DREGG/NATIVE-HOST/LOG-LEAF/v1".toUTF8.toList
def nodeCustomization : List UInt8 := "DREGG/NATIVE-HOST/LOG-NODE/v1".toUTF8.toList
def frontierCustomization : List UInt8 := "DREGG/NATIVE-HOST/LOG-FRONTIER/v1".toUTF8.toList

/-- The hash of a record's RAW stored bytes. -/
def recordHash (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash recordCustomization bytes).digest

def leafInput : StreamCodec (Nat × Digest × Digest × Digest) :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream))

/-- Leaf of height `h`: the height, the raw record's hash, the chain and the root after `h`. -/
def leafDigest (height : Nat) (record : List UInt8) (chain root : Digest) : Digest :=
  (Sp800185Cshake256.hash leafCustomization
    (leafInput.encode (height, recordHash record, chain, root))).digest

/-- The accumulator's node hash (deployed cSHAKE256). -/
def nodeDigest (left right : Digest) : Digest :=
  (Sp800185Cshake256.hash nodeCustomization
    (digestStream.encode left ++ digestStream.encode right)).digest

/-- The frontier's digest at height `n`: what each tag MAC binds. -/
def frontierDigest (height : Nat) (frontier : List (Nat × Digest)) : Digest :=
  (Sp800185Cshake256.hash frontierCustomization
    ((StreamCodec.product StreamCodec.nat frontierStream).encode (height, frontier))).digest

/-- The frontier after appending height `h`'s leaf. -/
def Frontier.push (frontier : List (Nat × Digest)) (leaf : Digest) : List (Nat × Digest) :=
  LogAccumulator.push nodeDigest frontier 0 leaf

/-- The Store key of the accumulator node `(level, end)` (`durable_node` space 1). -/
def nodeKey (level finish : Nat) : List UInt8 :=
  (StreamCodec.product StreamCodec.nat StreamCodec.nat).encode (level, finish)

/-- The nodes `Frontier.push` completes when it appends the leaf of height `h`
(each `(level, end = h)`): what the append writes beside the entry. The leaf
itself is level 0. -/
def completedNodes (frontier : List (Nat × Digest)) (height : Nat) (leaf : Digest) :
    List ((Nat × Nat) × Digest) :=
  go frontier 0 leaf
where
  go : List (Nat × Digest) → Nat → Digest → List ((Nat × Nat) × Digest)
    | (k', l) :: rest, k, r =>
        ((k, height), r) :: (if k' = k then go rest (k + 1) (nodeDigest l r) else [])
    | [], k, r => [((k, height), r)]

/-! ## The trailer (tag column, v3) -/

/-- What a trailer carries besides its MAC: root, chain, frontier digest, spent root. -/
structure Carried where
  root : Digest
  chain : Digest
  frontier : Digest
  spentRoot : Digest
  deriving DecidableEq, Repr

def trailerStream : StreamCodec (Carried × List UInt8) :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream))))
    (fun t => (t.1.root, t.1.chain, t.1.frontier, t.1.spentRoot, t.2))
    (fun t => (⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1⟩, t.2.2.2.2))
    (by intro value; cases value; rfl)

def tagInputStream : StreamCodec (List UInt8 × Nat × Digest × Digest × Digest × Digest) :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream digestStream))))

/-- `KMAC256(key, logTagLabel, (keyId, h, chain, root, frontierDigest, spentRoot))`. -/
def tagMac (key : MacKey) (height : Nat) (carried : Carried) : List UInt8 :=
  kmac256Bytes key.bytes logTagLabel.toUTF8.toList
    (tagInputStream.encode (key.id, height, carried.chain, carried.root, carried.frontier,
      carried.spentRoot))

/-- The stored tag of height `h`. -/
def trailer (key : MacKey) (height : Nat) (carried : Carried) : List UInt8 :=
  trailerStream.encode (carried, tagMac key height carried)

/-- What a stored tag carries (its prefix), whether or not its MAC verifies. -/
def trailerCarried (tag : List UInt8) : Option Carried :=
  (trailerStream.toLawful.decode tag).map Prod.fst

@[simp] theorem trailerCarried_trailer (key : MacKey) (height : Nat) (carried : Carried) :
    trailerCarried (trailer key height carried) = some carried := by
  have decoded : trailerStream.toLawful.decode (trailerStream.encode (carried, tagMac key height carried)) =
      some (carried, tagMac key height carried) :=
    trailerStream.toLawful.decode_encode (carried, tagMac key height carried)
  simp [trailerCarried, trailer, decoded]

/-! ## Raw Store bytes: constructed by transports, read only here -/

/-- One stored entry as the Store returned it. Its bytes are readable only in
this module (`verifyAt`, `verifyTagged`). -/
structure RawEntry where
  private mk ::
  private height : Nat
  private record : List UInt8
  private tag : List UInt8

def RawEntry.ofStore (height : Nat) (record tag : List UInt8) : RawEntry := ⟨height, record, tag⟩

/-- The height a raw entry claims (not authenticated by itself). -/
def RawEntry.claimedHeight (entry : RawEntry) : Nat := entry.height

/-- One stored accumulator node `(level, end)` as the Store returned it. -/
structure RawNode where
  private mk ::
  private level : Nat
  private finish : Nat
  private value : List UInt8

def RawNode.ofStore (level finish : Nat) (value : List UInt8) : RawNode := ⟨level, finish, value⟩

/-- Exact 32-byte digest decode (no trailing bytes). -/
def decodeDigest (bytes : List UInt8) : Option Digest :=
  match digestStream.decodePrefix bytes with
  | some (digest, []) => some digest
  | _ => none

/-- The sibling lookup a read uses: the first stored node with that key. -/
def lookupNode (nodes : List RawNode) (level finish : Nat) : Option Digest :=
  nodes.findSome? fun node =>
    if node.level = level ∧ node.finish = finish then decodeDigest node.value else none

/-! ## Verified records -/

/-- Why a history read refused. Each names the height. -/
inductive Refusal where
  | malformedTrailer (height : Nat)
  | wrongHeight (height : Nat) (stored : Nat)
  | notIncluded (height : Nat)
  | beyondHead (height : Nat) (head : Nat)
  | unavailable (height : Nat) (detail : String)
  | undecodable (height : Nat)
  deriving DecidableEq, Repr

def Refusal.message : Refusal → String
  | .malformedTrailer h => s!"durable history record refused at height {h}: its tag is not a v3 trailer"
  | .wrongHeight h stored => s!"durable history record refused at height {h}: the Store returned height {stored}"
  | .notIncluded h => s!"durable history record refused at height {h}: its inclusion proof does not reach the anchored log frontier (the record, its tag or a node on its path was altered); run `mini store audit`"
  | .beyondHead h head => s!"durable history record refused at height {h}: beyond the authenticated head {head}"
  | .unavailable h detail => s!"durable history record at height {h} unavailable: {detail}"
  | .undecodable h => s!"durable history record refused at height {h}: its verified bytes are not a canonical record"

/-- The inclusion of `(record, chain, root)` at height `h` in the log whose
frontier after `n` leaves is `frontier`, witnessed by some sibling lookup. -/
def Included (frontier : List (Nat × Digest)) (n height : Nat) (record : List UInt8)
    (chain root : Digest) : Prop :=
  ∃ nodes : Nat → Nat → Option Digest,
    verify nodeDigest frontier n height (leafDigest height record chain root) nodes = true

/-- A history record that passed its inclusion check. The ONLY way stored
history bytes reach a caller. -/
structure Verified (frontier : List (Nat × Digest)) (n height : Nat) where
  record : List UInt8
  chain : Digest
  root : Digest
  included : Included frontier n height record chain root

/-- **The read check.** Trailer decode, the height the Store returned, then the
accumulator climb from the leaf recomputed over the RAW bytes. -/
def verifyAt (frontier : List (Nat × Digest)) (n height : Nat) (entry : RawEntry)
    (nodes : List RawNode) : Except Refusal (Verified frontier n height) :=
  if beyond : n < height ∨ height = 0 then .error (.beyondHead height n) else
  if entry.height ≠ height then .error (.wrongHeight height entry.height) else
  match trailerCarried entry.tag with
  | none => .error (.malformedTrailer height)
  | some carried =>
      if ok : verify nodeDigest frontier n height
          (leafDigest height entry.record carried.chain carried.root) (lookupNode nodes) = true then
        .ok ⟨entry.record, carried.chain, carried.root, ⟨_, ok⟩⟩
      else .error (.notIncluded height)

/-- **Every verified read carries its inclusion** (by construction: `Verified`
has no other constructor). Stated over `verifyAt` itself. -/
theorem verifyAt_included {frontier : List (Nat × Digest)} {n height : Nat} {entry : RawEntry}
    {nodes : List RawNode} {read : Verified frontier n height}
    (_ok : verifyAt frontier n height entry nodes = .ok read) :
    Included frontier n height read.record read.chain read.root :=
  read.included

/-- **The returned bytes are the stored bytes**: `verifyAt` re-encodes nothing. -/
theorem verifyAt_bytes {frontier : List (Nat × Digest)} {n height : Nat} {entry : RawEntry}
    {nodes : List RawNode} {read : Verified frontier n height}
    (ok : verifyAt frontier n height entry nodes = .ok read) :
    read.record = entry.record := by
  unfold verifyAt at ok
  split at ok
  · cases ok
  split at ok
  · cases ok
  split at ok
  · cases ok
  · split at ok
    · cases ok; rfl
    · cases ok

/-- **Soundness at the deployed hash.** Under an honest frontier for the
stored log's leaves `leaves`, a verified read of height `h` has exactly the
honest leaf of `h` — the same record hash, chain and root — or the read
exhibits a cSHAKE256 collision of `nodeDigest`. Nothing is assumed about the
Store's node bytes. -/
theorem verifyAt_sound (leaves : Nat → Digest) {frontier : List (Nat × Digest)} {n height : Nat}
    (honest : Honest nodeDigest leaves n frontier)
    {entry : RawEntry} {nodes : List RawNode} {read : Verified frontier n height}
    (ok : verifyAt frontier n height entry nodes = .ok read) :
    leafDigest height read.record read.chain read.root = leaves height ∨ NodeCollision nodeDigest := by
  have within : 1 ≤ height ∧ height ≤ n := by
    unfold verifyAt at ok
    split at ok
    · cases ok
    · rename_i inRange; omega
  obtain ⟨lookup, accepted⟩ := read.included
  exact LogAccumulator.verify_sound nodeDigest leaves n height within.1 within.2 frontier honest _
    lookup accepted

/-- **A read whose leaf no lookup lifts to the frontier refuses, naming its
height** (for an in-range, well-formed entry). -/
theorem verifyAt_refuses {frontier : List (Nat × Digest)} {n height : Nat} {entry : RawEntry}
    {nodes : List RawNode} (inRange : 1 ≤ height ∧ height ≤ n) (sameHeight : entry.height = height)
    {carried : Carried} (decoded : trailerCarried entry.tag = some carried)
    (notLifted : verify nodeDigest frontier n height
      (leafDigest height entry.record carried.chain carried.root) (lookupNode nodes) = false) :
    verifyAt frontier n height entry nodes = .error (.notIncluded height) := by
  unfold verifyAt
  rw [dif_neg (by omega), if_neg (by simpa using sameHeight)]
  simp only [decoded]
  rw [dif_neg (by simp [notLifted])]

/-! ## The suffix and head tags (verified with the key at open) -/

/-- Verify a tag the open reads with the key (the head and every entry after
the checkpoint) against the open's own recomputed chain, frontier and spent
root: the carried values must equal them and the MAC must verify. Returns the
carried root (the receipt root of `h`). -/
def verifyTagged (key : MacKey) (height : Nat) (tag : List UInt8) (chain frontier spentRoot : Digest) :
    Except Refusal Digest :=
  match trailerStream.toLawful.decode tag with
  | none => .error (.malformedTrailer height)
  | some (carried, mac) =>
      if carried.chain = chain ∧ carried.frontier = frontier ∧ carried.spentRoot = spentRoot ∧
          mac = tagMac key height carried then .ok carried.root
      else .error (.notIncluded height)

/-- What the Host writes verifies, exactly. -/
theorem verifyTagged_trailer (key : MacKey) (height : Nat) (carried : Carried) :
    verifyTagged key height (trailer key height carried) carried.chain carried.frontier
      carried.spentRoot = .ok carried.root := by
  have decoded : trailerStream.toLawful.decode (trailerStream.encode (carried, tagMac key height carried)) =
      some (carried, tagMac key height carried) :=
    trailerStream.toLawful.decode_encode (carried, tagMac key height carried)
  simp [verifyTagged, trailer, decoded]

/-! ## The authenticated head

A `Head` is the height, chain, accumulator frontier and spent root that the
head entry's tag MACs under the Store key — or the empty log's canonical
values. Its constructor is PRIVATE: the only ways to obtain one are
`Head.verify` (which checks the tag's MAC against the frontier the caller
recomputed) and `Head.genesis`. Every `Verified`, `ByTx`, spent answer and
state answer of `Compiler.DurableHistoryReader` is stated relative to a
`Head`, so nothing downstream is sound "relative to whatever frontier someone
put there". Which tag: the helper serves durable reads only under the MINIANC2
head anchor (`docs/DURABLE-STORE.md`), so the tag the open passes here is the
anchor-fixed head entry's. -/

structure Head where
  private mk ::
  key : MacKey
  height : Nat
  chain : Digest
  frontier : List (Nat × Digest)
  spentRoot : Digest
  root : Digest
  bound : (height = 0 ∧ frontier = [] ∧ spentRoot = DurableSpent.emptyDigest) ∨
    ∃ tag, verifyTagged key height tag chain (frontierDigest height frontier) spentRoot = .ok root

/-- The empty log's head. -/
def Head.genesis (key : MacKey) (chain root : Digest) : Head :=
  ⟨key, 0, chain, [], DurableSpent.emptyDigest, root, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- A head from the head entry's tag: the MAC must verify for this height, the
recomputed chain and frontier, and the spent root the tag carries. -/
def Head.verify (key : MacKey) (height : Nat) (tag : List UInt8) (chain : Digest)
    (frontier : List (Nat × Digest)) : Except Refusal Head :=
  match trailerCarried tag with
  | none => .error (.malformedTrailer height)
  | some carried =>
      match checked : verifyTagged key height tag chain (frontierDigest height frontier) carried.spentRoot with
      | .ok root => .ok ⟨key, height, chain, frontier, carried.spentRoot, root, Or.inr ⟨tag, checked⟩⟩
      | .error refusal => .error refusal

/-- **A head is MAC-bound**: unless it is the empty log's, some tag of its
height verifies under its key for its chain, frontier and spent root. -/
theorem Head.bound_tag (head : Head) (nonempty : head.height ≠ 0) :
    ∃ tag, verifyTagged head.key head.height tag head.chain (frontierDigest head.height head.frontier)
      head.spentRoot = .ok head.root := by
  rcases head.bound with ⟨zero, _⟩ | tagged
  · exact absurd zero nonempty
  · exact tagged

#assert_axioms verifyAt_bytes
#assert_axioms verifyAt_sound
#assert_axioms verifyAt_refuses
#assert_axioms verifyTagged_trailer
#assert_axioms Head.bound_tag

end Minidregg.Compiler.DurableHistory
