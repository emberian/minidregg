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
* **Trailer** (the Store's tag column, v4): the root and chain after `h`, the
  frontier digest and index root after `h`, then the MAC (`tagMac`) over all
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
import Compiler.DurableIndex

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

/-! ## The trailer (tag column, v4) -/

/-- What a trailer carries besides its MAC: root, chain, frontier digest, index root. -/
structure Carried where
  root : Digest
  chain : Digest
  frontier : Digest
  indexRoot : Digest
  deriving DecidableEq, Repr

def trailerStream : StreamCodec (Carried × List UInt8) :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream))))
    (fun t => (t.1.root, t.1.chain, t.1.frontier, t.1.indexRoot, t.2))
    (fun t => (⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1⟩, t.2.2.2.2))
    (by intro value; cases value; rfl)

def tagInputStream : StreamCodec (List UInt8 × Nat × Digest × Digest × Digest × Digest) :=
  StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream digestStream))))

/-- `KMAC256(key, logTagLabel, (keyId, h, chain, root, frontierDigest, indexRoot))`. -/
def tagMac (key : MacKey) (height : Nat) (carried : Carried) : List UInt8 :=
  kmac256Bytes key.bytes logTagLabel.toUTF8.toList
    (tagInputStream.encode (key.id, height, carried.chain, carried.root, carried.frontier,
      carried.indexRoot))

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
  | .malformedTrailer h => s!"durable history record refused at height {h}: its tag is not a v4 trailer"
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
def verifyTagged (key : MacKey) (height : Nat) (tag : List UInt8) (chain frontier indexRoot : Digest) :
    Except Refusal Digest :=
  match trailerStream.toLawful.decode tag with
  | none => .error (.malformedTrailer height)
  | some (carried, mac) =>
      if carried.chain = chain ∧ carried.frontier = frontier ∧ carried.indexRoot = indexRoot ∧
          mac = tagMac key height carried then .ok carried.root
      else .error (.notIncluded height)

/-- What the Host writes verifies, exactly. -/
theorem verifyTagged_trailer (key : MacKey) (height : Nat) (carried : Carried) :
    verifyTagged key height (trailer key height carried) carried.chain carried.frontier
      carried.indexRoot = .ok carried.root := by
  have decoded : trailerStream.toLawful.decode (trailerStream.encode (carried, tagMac key height carried)) =
      some (carried, tagMac key height carried) :=
    trailerStream.toLawful.decode_encode (carried, tagMac key height carried)
  simp [verifyTagged, trailer, decoded]

/-! ## The opened Store's identity and its authenticated head

`StoreIdentity` is the opened Store: its MAC key and its genesis log start
(the deployment's domain and semantics and the seed, `NativeHostCodec.logRoot0`).
A `Head store` is the height, chain, accumulator frontier and index root that
the head entry's tag MACs under `store.key` — or the empty log's values.
Every `Verified`, `ByTx`, spent answer and state answer of
`Compiler.DurableHistoryReader` is indexed by a `Head store`, so a head of
another Store (another key, another genesis) does not typecheck where the
opened Store's is expected.

Two layers. LAYER 1 (types): `Head` is indexed by the identity and its key is
not a free field; `Head.verify` checks the tag's MAC under `store.key`.
LAYER 2 (token audit): `StoreIdentity.ofOpen` and `Head.genesis` are minted
only by the open (`DurableHistoryStore.readerOf`, `DurableReceiverIO`): a
genesis head says every key is absent, so a genesis head for a non-empty Store
would be a replay bypass. Both are on the receiver-token audit list
(`scripts/kn2/token-audit-list.txt`, for Host/ReceiverTokenAudit), and
`scripts/kn2/planted-api-faults.lean` carries their planted forges.
Which tag: the helper serves durable reads only under the MINIANC2 head anchor
(`docs/DURABLE-STORE.md`), so the tag the open passes is the anchor-fixed head
entry's. -/

/-- Where a Store identity comes from: the deployment's own Store, minted by the
open (`StoreIdentity.ofOpen`), or a scratch Store a portable foreign image was
written into (`StoreIdentity.ofScratch`, `DurableHistoryStore.scratchReader`). A
scratch Store's head is bound only to the chain recomputed from that image's bytes
and the commitment its caller checked. It reads history (the walk re-admits the
foreign prefix through it) but is never a light opening of the deployment: an
`Opening`, the write path's state, carries `live : store.origin = .deployment`. -/
inductive StoreOrigin where
  | deployment
  | scratch
  deriving DecidableEq, Repr

structure StoreIdentity where
  private mk ::
  origin : StoreOrigin
  key : MacKey
  logStart : Digest

/-- LAYER 2: the deployment's Store, minted only by the open (token audit list). -/
def StoreIdentity.ofOpen (key : MacKey) (logStart : Digest) : StoreIdentity := ⟨.deployment, key, logStart⟩

/-- LAYER 2: a scratch Store holding a portable foreign image, minted only by
`DurableHistoryStore.scratchReader` (token audit list). -/
def StoreIdentity.ofScratch (key : MacKey) (logStart : Digest) : StoreIdentity := ⟨.scratch, key, logStart⟩

@[simp] theorem StoreIdentity.ofOpen_origin (key : MacKey) (logStart : Digest) :
    (StoreIdentity.ofOpen key logStart).origin = .deployment := rfl

@[simp] theorem StoreIdentity.ofScratch_origin (key : MacKey) (logStart : Digest) :
    (StoreIdentity.ofScratch key logStart).origin = .scratch := rfl

/-- **A scratch Store is never the deployment's**: no scratch identity equals an
opened one, whatever the key and log start, so a scratch Store's `Head` (and every
answer indexed by it) does not typecheck where an opened Store's is expected. -/
theorem StoreIdentity.ofScratch_ne_ofOpen (key key' : MacKey) (logStart logStart' : Digest) :
    StoreIdentity.ofScratch key logStart ≠ StoreIdentity.ofOpen key' logStart' := by
  intro same
  have := congrArg StoreIdentity.origin same
  simp at this

structure Head (store : StoreIdentity) where
  private mk ::
  height : Nat
  chain : Digest
  frontier : List (Nat × Digest)
  indexRoot : Digest
  root : Digest
  bound : (height = 0 ∧ chain = store.logStart ∧ frontier = [] ∧ indexRoot = DurableIndex.emptyDigest) ∨
    ∃ tag, verifyTagged store.key height tag chain (frontierDigest height frontier) indexRoot = .ok root

/-- The empty log's head: its chain is the Store's genesis log start. LAYER 2:
minted only by the open, and only when the anchored read's head is 0. -/
def Head.genesis (store : StoreIdentity) (root : Digest) : Head store :=
  ⟨0, store.logStart, [], DurableIndex.emptyDigest, root, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

/-- A head from the head entry's tag: the MAC must verify under the Store's key
for this height, the recomputed chain and frontier, and the index root the tag carries. -/
def Head.verify (store : StoreIdentity) (height : Nat) (tag : List UInt8) (chain : Digest)
    (frontier : List (Nat × Digest)) : Except Refusal (Head store) :=
  match trailerCarried tag with
  | none => .error (.malformedTrailer height)
  | some carried =>
      match checked : verifyTagged store.key height tag chain (frontierDigest height frontier)
          carried.indexRoot with
      | .ok root => .ok ⟨height, chain, frontier, carried.indexRoot, root, Or.inr ⟨tag, checked⟩⟩
      | .error refusal => .error refusal

/-- A verified head is at the height, chain and frontier it was verified for. -/
theorem Head.verify_fields {store : StoreIdentity} {height : Nat} {tag : List UInt8} {chain : Digest}
    {frontier : List (Nat × Digest)} {head : Head store}
    (verified : Head.verify store height tag chain frontier = .ok head) :
    head.height = height ∧ head.chain = chain ∧ head.frontier = frontier := by
  unfold Head.verify at verified
  split at verified
  · cases verified
  · split at verified
    · cases verified
      exact ⟨rfl, rfl, rfl⟩
    · cases verified

theorem Head.genesis_fields (store : StoreIdentity) (root : Digest) :
    (Head.genesis store root).height = 0 ∧ (Head.genesis store root).chain = store.logStart ∧
      (Head.genesis store root).frontier = [] := ⟨rfl, rfl, rfl⟩

/-- **A head is MAC-bound to its Store**: unless it is the empty log's (whose
chain is the Store's genesis log start), some tag of its height verifies under
the Store's key for its chain, frontier and index root. -/
theorem Head.bound_tag {store : StoreIdentity} (head : Head store) (nonempty : head.height ≠ 0) :
    ∃ tag, verifyTagged store.key head.height tag head.chain (frontierDigest head.height head.frontier)
      head.indexRoot = .ok head.root := by
  rcases head.bound with ⟨zero, _⟩ | tagged
  · exact absurd zero nonempty
  · exact tagged

#assert_axioms verifyAt_bytes
#assert_axioms verifyAt_sound
#assert_axioms verifyAt_refuses
#assert_axioms verifyTagged_trailer
#assert_axioms Head.bound_tag

end Minidregg.Compiler.DurableHistory
