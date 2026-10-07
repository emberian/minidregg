/-
# Compiler.DurableIndexFamilies — every family of the one index trie, and the rows of a record

KN2-TRIE sub-range B1 (design `TRIE-B-DESIGN` §1, §2, §6). The one authenticated
trie of `Compiler.DurableIndex` holds, beside the spent map (family 0) and the
transaction index (family 1):

| family | key (family, primary, secondary)                  | value                                   |
|--------|---------------------------------------------------|-----------------------------------------|
| 2 presence  | (2, H subject, H' cell)                      | (cell, height)                          |
| 4 links     | (4, H cell, H' link id)                      | `LinkFacts` (record digest, target primaries, row) |
| 5 backlinks | (5, H target, H' (cell, link id))            | `LinkRow` of the link                   |
| 6 payer     | (6, H payer, `noSecondary`)                  | (count, latest height, latest txid)     |
| 7 incoming  | (7, H destination, `heightSecondary` height) | the paying record's transaction id      |

`H = primaryOf family`, `H' = secondaryOf family` (the primary of `0xFF ::` the
bytes, separated from every primary). Family byte 3 is unused: the old `touched`
map (any writer of a cell) is deleted, not re-homed (DEPUTY-KERNEL ruling).

**Bounded values.** The Store refuses a `durable_node.value` over 4096 bytes and
a leaf row is its 65-byte key plus the value. Every value here is a fixed
number of naturals below `2^256` (a cell id, link id, operation digest,
relation, target id, the anchor's atom), each at most 34 bytes in
`StreamCodec.nat`, plus at most two 32-byte target primaries (`targetsOf` has
one or two members): under 600 bytes. No payload, link record or external
target bytes are stored — only their digests.

**The rows of a record** (`IndexRows.changes`) are a pure function of the
record and VERIFIED priors (`IndexRows.reads`: the family-0/1 keys, the payer
key, and the family-4 prefix of each written cell): `IndexRows.apply` opens and
reveals them against the authenticated root, then sets every change
(`setAll`). A record is atomic: a cell written twice in one record is indexed by
its LAST write (DEPUTY-KERNEL condition 1); a link dropped and re-added inside
one record keeps its live-since height when its record is unchanged.

**The model theorem** (`IndexRows.changes_exact`): over the logical map, a map
that represents a log (`Represents`: every key's value is the log's
`declared` value, defined by search over the log, never through the trie or
`changes`) is advanced by a record's changes to a map that represents the
longer log. Families 4 and 5 hold under `KeysDistinct keyHash (hashInputs log)`:
the key hash is injective on the byte strings the log feeds it. That is the
cSHAKE256 COLLISION floor — about 2^128 work at a 256-bit output — and its
failure for the deployed hash exhibits a cSHAKE256 collision
(`keysDistinct_or_collision`). `KeysDistinct` has a named satisfying instance
(`Teeth.keysDistinct_deployed`) and a named refuting one
(`Teeth.keysDistinct_refuted`). The meaning theorems state what each family's
declared value IS in domain terms: presence = the greatest height the subject
wrote the cell (`presence_meaning`), links = the latest live links with their
live-since heights (`linkState_keys`, `links_meaning`), backlinks = the
inversion over `targetsOf` (`backlinks_meaning`), payer = count, last height
and its txid (`payer_meaning`), incoming = the heights paying the destination
(`incoming_meaning`).

Semantic change against `Kernel.LinkIndex` (reported in the commit): a
transclusion that reads document D is filed as a backlink of D directly
(`targetsOf`); the old `transclusionKeys` scan also listed OTHER links to the
same transclusion identifier under D.
-/
import Compiler.DurableIndex
import Kernel.LinkIndex
import Kernel.FleetTurnCodec
import Compiler.HyperdocumentCell

namespace Minidregg.Compiler.DurableIndex

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.LinkIndex (TargetKey LinkKey lastWrite liveLinks)

set_option autoImplicit false

/-! ## Families -/

namespace Family
/-- `(subject, cell) ↦ (cell, height)`: the greatest height the subject wrote the cell. -/
def presence : UInt8 := 2
/-- `(cell, link id) ↦ LinkFacts`: the live links of a cell's latest write. -/
def links : UInt8 := 4
/-- `(target, (cell, link id)) ↦ LinkRow`: the live links pointing at a target. -/
def backlinks : UInt8 := 5
/-- `payer ↦ (count, latest height, latest txid)` of the fleet turns it paid. -/
def payer : UInt8 := 6
/-- `(destination, height) ↦ txid`: the fleet turns whose transfer paid the destination. -/
def incoming : UInt8 := 7
end Family

/-- The 32-octet secondary of `bytes` in `family`: the primary of `0xFF :: bytes`. -/
def secondaryOf (family : UInt8) (bytes : List UInt8) : Digest256 := primaryOf family (0xFF :: bytes)

/-! ## Canonical bytes of what the keys name -/

def subjectBytes (subject : SubjectId) : List UInt8 := StreamCodec.nat.encode subject.value
def cellBytes (cell : CellId) : List UInt8 := digestStream.encode cell
def linkBytes (link : LinkId) : List UInt8 := digestStream.encode link.digest
def pairBytes (cell : CellId) (link : LinkId) : List UInt8 := cellBytes cell ++ linkBytes link
def accountBytes (account : Nat) : List UInt8 := StreamCodec.nat.encode account

/-- A link target key's canonical bytes (tagged sum: document, element,
transclusion, external with its three byte strings). -/
def targetKeyStream : StreamCodec TargetKey :=
  StreamCodec.xmap
    (StreamCodec.sum digestStream (StreamCodec.sum digestStream (StreamCodec.sum digestStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream)))))
    (fun
      | .document ident => .inl ident.digest
      | .element ident => .inr (.inl ident.digest)
      | .transclusion ident => .inr (.inr (.inl ident.digest))
      | .external scheme authority path => .inr (.inr (.inr (scheme, authority, path))))
    (fun
      | .inl d => .document ⟨d⟩
      | .inr (.inl d) => .element ⟨d⟩
      | .inr (.inr (.inl d)) => .transclusion ⟨d⟩
      | .inr (.inr (.inr (scheme, authority, path))) => .external scheme authority path)
    (by intro target; cases target <;> rfl)

def targetBytes (target : TargetKey) : List UInt8 := targetKeyStream.encode target

def linkRecordBytes (link : LinkId) (record : LinkRecord) : List UInt8 :=
  linkBytes link ++ HyperdocumentCell.linkRecordStream.encode record

/-! ## Keys -/

def presenceKey (subject : SubjectId) (cell : CellId) : IndexKey :=
  ⟨Family.presence, primaryOf Family.presence (subjectBytes subject),
    secondaryOf Family.presence (cellBytes cell)⟩

def cellPrimary (cell : CellId) : Digest256 := primaryOf Family.links (cellBytes cell)

def linkSecondary (link : LinkId) : Digest256 := secondaryOf Family.links (linkBytes link)

def linkKey (cell : CellId) (link : LinkId) : IndexKey := ⟨Family.links, cellPrimary cell, linkSecondary link⟩

def targetPrimary (target : TargetKey) : Digest256 := primaryOf Family.backlinks (targetBytes target)

def pairSecondary (cell : CellId) (link : LinkId) : Digest256 :=
  secondaryOf Family.backlinks (pairBytes cell link)

/-- The backlink row of `(cell, link)` filed under the target whose primary is `target`. -/
def backlinkKey (target : Digest256) (cell : CellId) (link : LinkId) : IndexKey :=
  ⟨Family.backlinks, target, pairSecondary cell link⟩

def payerKey (payer : Nat) : IndexKey :=
  ⟨Family.payer, primaryOf Family.payer (accountBytes payer), noSecondary⟩

/-- The digest a link's family-4 value carries for its record: a changed record
(retarget, new relation, new range) restarts the link's live-since height. -/
def recordDigest (link : LinkId) (record : LinkRecord) : Digest256 :=
  primaryOf Family.links (0xFE :: linkRecordBytes link record)

/-- The prefix of a cell's family-4 keys: the family byte and the cell's primary (264 bits). -/
def linkPrefix (cell : CellId) : List Bool := (bitsOf ⟨Family.links, cellPrimary cell, noSecondary⟩).take 264

/-! ## Heights as secondaries, in trie order

`heightSecondary h` is the 32-octet value whose stored octets (`fixedStream`,
little-endian) are the BIG-endian encoding of `h`, so its 256 path bits are
`h`'s big-endian bits and the depth-first order of the family-7 keys under one
destination is ascending height (`rank_heightSecondary`). -/

def heightSecondary (height : Nat) : Digest256 :=
  ⟨fixedValue (fixedOctets 32 height).reverse, by
    simpa using fixedValue_lt (fixedOctets 32 height).reverse⟩

def incomingKey (destination height : Nat) : IndexKey :=
  ⟨Family.incoming, primaryOf Family.incoming (accountBytes destination), heightSecondary height⟩

/-- The big-endian value of a bit string. -/
def rank (bits : List Bool) : Nat := bits.foldl (fun acc bit => 2 * acc + if bit then 1 else 0) 0

/-- A secondary's 256 path bits. -/
def secondaryBits (secondary : Digest256) : List Bool :=
  Kernel.WorldRoot.bytesBits ((fixedStream 32).encode secondary)

theorem fixedOctets_fixedValue :
    ∀ (octets : List UInt8), fixedOctets octets.length (fixedValue octets) = octets
  | [] => rfl
  | byte :: rest => by
      have tail := fixedOctets_fixedValue rest
      unfold fixedOctets fixedValue at tail ⊢
      simp only [List.map_cons, Minidregg.Theory.Bignum.denoteNat_cons,
        Minidregg.Theory.Bignum.digitsLE]
      have low : (byte.toNat + 256 * Minidregg.Theory.Bignum.denoteNat 256 (rest.map UInt8.toNat)) % 256 =
          byte.toNat := by
        have := byte.toNat_lt; omega
      have high : (byte.toNat + 256 * Minidregg.Theory.Bignum.denoteNat 256 (rest.map UInt8.toNat)) / 256 =
          Minidregg.Theory.Bignum.denoteNat 256 (rest.map UInt8.toNat) := by
        have := byte.toNat_lt; omega
      rw [low, high, tail]
      simp

theorem rank_foldl (bits : List Bool) (acc : Nat) :
    bits.foldl (fun acc bit => 2 * acc + if bit then 1 else 0) acc = acc * 2 ^ bits.length + rank bits := by
  induction bits generalizing acc with
  | nil => simp [rank]
  | cons bit rest ih =>
      simp only [rank, List.foldl_cons, List.length_cons] at ih ⊢
      rw [ih, ih (2 * 0 + if bit then 1 else 0)]
      rw [pow_succ]; cases bit <;> simp <;> ring

theorem rank_testBits (n : Nat) :
    ∀ (width : Nat), n < 2 ^ width → rank ((List.range width).reverse.map n.testBit) = n := by
  intro width
  induction width generalizing n with
  | zero => intro fits; simp at fits; subst fits; rfl
  | succ width ih =>
      intro fits
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons]
      unfold rank
      rw [List.foldl_cons, rank_foldl]
      have below : n % 2 ^ width < 2 ^ width := Nat.mod_lt _ (by positivity)
      have same : (List.range width).reverse.map n.testBit =
          (List.range width).reverse.map (n % 2 ^ width).testBit := by
        apply List.map_congr_left
        intro i member
        rw [List.mem_reverse, List.mem_range] at member
        rw [Nat.testBit_mod_two_pow]; simp [member]
      rw [same, ih _ below, List.length_map, List.length_reverse, List.length_range]
      have split := Nat.div_add_mod n (2 ^ width)
      have top : n / 2 ^ width < 2 := by
        rw [pow_succ] at fits; exact Nat.div_lt_of_lt_mul fits
      have bit : n.testBit width = decide (n / 2 ^ width % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
      rw [bit]
      generalize n / 2 ^ width = q at split top
      generalize n % 2 ^ width = r at split
      interval_cases q <;> simp <;> omega

theorem rank_byteBits (byte : UInt8) : rank (Kernel.WorldRoot.byteBits byte) = byte.toNat :=
  rank_testBits byte.toNat 8 byte.toNat_lt

theorem rank_bytesBits (octets : List UInt8) :
    rank (Kernel.WorldRoot.bytesBits octets) = octets.foldl (fun acc byte => 256 * acc + byte.toNat) 0 := by
  suffices general : ∀ acc, (Kernel.WorldRoot.bytesBits octets).foldl
      (fun acc bit => 2 * acc + if bit then 1 else 0) acc =
      octets.foldl (fun acc byte => 256 * acc + byte.toNat) acc from general 0
  induction octets with
  | nil => intro acc; rfl
  | cons byte rest ih =>
      intro acc
      have step : (Kernel.WorldRoot.byteBits byte).foldl (fun acc bit => 2 * acc + if bit then 1 else 0) acc =
          256 * acc + byte.toNat := by
        rw [rank_foldl, rank_byteBits, Kernel.WorldRoot.byteBits_length]; ring
      rw [Kernel.WorldRoot.bytesBits, List.flatMap_cons, List.foldl_append, step, List.foldl_cons]
      exact ih _

theorem foldl_reverse_denote (digits : List UInt8) :
    digits.reverse.foldl (fun acc byte => 256 * acc + byte.toNat) 0 = fixedValue digits := by
  rw [List.foldl_reverse]
  unfold fixedValue
  induction digits with
  | nil => rfl
  | cons byte rest ih =>
      simp only [List.foldr_cons, List.map_cons, Minidregg.Theory.Bignum.denoteNat_cons]
      rw [ih]; ring

/-- **A height's secondary ranks as the height**: the big-endian value of its
256 path bits is `h` (for `h < 2^256`), so the family-7 keys of one destination
are in ascending height in the trie. -/
theorem rank_heightSecondary (height : Nat) (fits : height < 256 ^ 32) :
    rank (secondaryBits (heightSecondary height)) = height := by
  have encoded : (fixedStream 32).encode (heightSecondary height) = (fixedOctets 32 height).reverse := by
    show fixedOctets 32 (fixedValue (fixedOctets 32 height).reverse) = _
    have := fixedOctets_fixedValue (fixedOctets 32 height).reverse
    simpa using this
  unfold secondaryBits
  rw [encoded, rank_bytesBits, foldl_reverse_denote]
  exact fixedValue_fixedOctets 32 height fits

theorem heightSecondary_injective {a b : Nat} (fitsA : a < 256 ^ 32) (fitsB : b < 256 ^ 32)
    (same : heightSecondary a = heightSecondary b) : a = b := by
  rw [← rank_heightSecondary a fitsA, ← rank_heightSecondary b fitsB, same]

/-! ## Values -/

/-- One link row: source cell, link id, the source range's start atom, the
link's revision (the operation that wrote it), the height from which it has
been live (RELATIVE to the log: genesis is added where the row is rendered),
the target's kind and id, and the relation. Every field is a natural below `2^256`. -/
structure LinkRow where
  source : Nat
  link : Nat
  anchor : Option Nat
  revision : Nat
  height : Nat
  kind : Nat
  target : Nat
  relation : Nat
  deriving DecidableEq, Repr

def linkRowStream : StreamCodec LinkRow :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option StreamCodec.nat) (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun row => (row.source, row.link, row.anchor, row.revision, row.height, row.kind, row.target,
      row.relation))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1, wire.2.2.2.2.2.1,
      wire.2.2.2.2.2.2.1, wire.2.2.2.2.2.2.2⟩)
    (by intro row; cases row; rfl)

/-- The row of link `link` of `cell`, with record `record`, live since `height`. -/
def LinkRow.of (cell : CellId) (link : LinkId) (record : LinkRecord) (height : Nat) : LinkRow :=
  ⟨cell.value, link.digest.value,
    (record.source.bind fun range => range.start.neighbor).map (·.digest.value),
    record.operation.digest.value, height,
    Kernel.LinkIndex.targetKind record.target, Kernel.LinkIndex.targetId record.target, record.relation.value⟩

/-- What a link is filed under: the key of its target, and — for a transclusion
— the document it reads (a transclusion of D is a backlink of D). -/
def targetsOf (record : LinkRecord) : List TargetKey :=
  TargetKey.of record.target :: (Kernel.LinkIndex.transcludedDocument record.target).toList.map TargetKey.document

def targetPrimaries (record : LinkRecord) : List Digest256 := (targetsOf record).map targetPrimary

/-- The family-4 value of a link: its record's digest, the family-5 primaries it
is filed under, and its row. -/
structure LinkFacts where
  recordDigest : Digest256
  targets : List Digest256
  row : LinkRow
  deriving DecidableEq, Repr

def linkFactsStream : StreamCodec LinkFacts :=
  StreamCodec.xmap
    (StreamCodec.product (fixedStream 32) (StreamCodec.product (StreamCodec.list (fixedStream 32)) linkRowStream))
    (fun facts => (facts.recordDigest, facts.targets, facts.row))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro facts; cases facts; rfl)

def factsOf (cell : CellId) (link : LinkId) (record : LinkRecord) (height : Nat) : LinkFacts :=
  ⟨recordDigest link record, targetPrimaries record, LinkRow.of cell link record height⟩

def factsValue (cell : CellId) (link : LinkId) (record : LinkRecord) (height : Nat) : List UInt8 :=
  linkFactsStream.encode (factsOf cell link record height)

def rowValue (cell : CellId) (link : LinkId) (record : LinkRecord) (height : Nat) : List UInt8 :=
  linkRowStream.encode (LinkRow.of cell link record height)

def presenceValue (cell : CellId) (height : Nat) : List UInt8 :=
  (StreamCodec.product digestStream StreamCodec.nat).encode (cell, height)

def payerStream : StreamCodec (Nat × Nat × Digest) :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat digestStream)

def payerValue (count height : Nat) (transactionId : TransactionId) : List UInt8 :=
  payerStream.encode (count, height, transactionId)

/-- The count a family-6 value carries (0 when absent or not a payer value). -/
def payerCount (value : Option (List UInt8)) : Nat :=
  ((value.bind payerStream.toLawful.decode).map (·.1)).getD 0

def transactionValue (transactionId : TransactionId) : List UInt8 := digestStream.encode transactionId

/-! ## What a record contributes -/

/-- A fleet turn's payer and its transfer's destination (exactly the decode the
fleet controller runs, `FleetTurn.decodeIngress`). -/
def fleetOf (record : IntentRecord) : Option (Nat × Option Nat) :=
  (Kernel.FleetTurn.decodeIngress record.event.canonicalBytes).map fun ingress =>
    (ingress.command.payer, ingress.command.transfer.map (·.destination))

/-- The cells a record writes, each once. -/
def writtenCells (record : IntentRecord) : List CellId := (record.writes.map DataWrite.cellId).dedup

/-- The live links of a cell after the record's LAST write of it. -/
def lastLinks (cell : CellId) (record : IntentRecord) : List LinkKey :=
  match lastWrite cell record with
  | some write => liveLinks write.canonicalPostBytes
  | none => []

/-- The keys of families 0 and 1: the transaction id, then the nullifiers. -/
def keys01 (record : IntentRecord) : List IndexKey :=
  transactionKey record.transactionId :: record.nullifiers.map nullifierKey

/-! ## The rows of a record -/

namespace IndexRows

/-- What a record's rows read before they are computed (all VERIFIED against
the root): the family-0/1 keys (freshness) and the payer key, and the family-4
prefix of each written cell (its prior links). -/
def reads (record : IntentRecord) : List IndexKey × List (List Bool) :=
  (keys01 record ++ ((fleetOf record).map fun fleet => payerKey fleet.1).toList,
    (writtenCells record).map linkPrefix)

/-- The verified priors a record's rows depend on. -/
structure Priors where
  /-- The family-6 value at the record's payer key (`none` if absent or not a fleet turn). -/
  payer : Option (List UInt8)
  /-- The family-4 members under a written cell's prefix. -/
  links : CellId → List (IndexKey × List UInt8)

/-- The priors read through a lookup and a reveal (`apply` passes verified ones). -/
def priorsWith (lookup : IndexKey → Option (List UInt8))
    (members : List Bool → List (IndexKey × List UInt8)) (record : IntentRecord) : Priors :=
  ⟨(fleetOf record).bind fun fleet => lookup (payerKey fleet.1), fun cell => members (linkPrefix cell)⟩

/-- The prior links of a cell, decoded from its family-4 values (link id from the row). -/
def priorFacts (prior : List (IndexKey × List UInt8)) : List (LinkId × LinkFacts) :=
  prior.filterMap fun entry =>
    (linkFactsStream.toLawful.decode entry.2).map fun facts => (⟨⟨facts.row.link⟩⟩, facts)

/-- The family-4 and family-5 rows a cell's links stand for. -/
def linkRows (cell : CellId) (facts : List (LinkId × LinkFacts)) : List (IndexKey × List UInt8) :=
  facts.map (fun entry => (linkKey cell entry.1, linkFactsStream.encode entry.2)) ++
    facts.flatMap fun entry =>
      entry.2.targets.map fun target => (backlinkKey target cell entry.1, linkRowStream.encode entry.2.row)

/-- The new links of a cell at `height`: each keeps the live-since height of a
prior link with the same identifier and the same record digest, else starts at `height`. -/
def newFacts (height : Nat) (cell : CellId) (record : IntentRecord)
    (prior : List (IndexKey × List UInt8)) : List (LinkId × LinkFacts) :=
  (lastLinks cell record).map fun link =>
    let kept := ((priorFacts prior).find? fun entry =>
      entry.1 = link.1 ∧ entry.2.recordDigest = recordDigest link.1 link.2).map (·.2.row.height)
    (link.1, factsOf cell link.1 link.2 (kept.getD height))

/-- The rows a cell's links had: its family-4 members as read, and the family-5
rows their facts name. -/
def priorRows (cell : CellId) (prior : List (IndexKey × List UInt8)) : List (IndexKey × List UInt8) :=
  prior ++ (priorFacts prior).flatMap fun entry =>
    entry.2.targets.map fun target => (backlinkKey target cell entry.1, linkRowStream.encode entry.2.row)

/-- From the prior rows to the new, key by key: every key either list holds is
set to its new value (`none`: deleted) when the two differ; an
unchanged row is not rewritten. -/
def diff (before after : List (IndexKey × List UInt8)) : List (IndexKey × Option (List UInt8)) :=
  ((before.map (·.1)) ++ (after.map (·.1))).dedup.filterMap fun k =>
    if mapLookup after k = mapLookup before k then none else some (k, mapLookup after k)

def changes01 (height : Nat) (record : IntentRecord) : List (IndexKey × Option (List UInt8)) :=
  (keys01 record).map fun k => (k, some (heightValue height))

def changes2 (height : Nat) (record : IntentRecord) : List (IndexKey × Option (List UInt8)) :=
  match record.subject with
  | none => []
  | some subject => (writtenCells record).map fun cell => (presenceKey subject cell, some (presenceValue cell height))

def changesLinks (height : Nat) (record : IntentRecord) (priors : Priors) :
    List (IndexKey × Option (List UInt8)) :=
  (writtenCells record).flatMap fun cell =>
    diff (priorRows cell (priors.links cell)) (linkRows cell (newFacts height cell record (priors.links cell)))

def changes6 (height : Nat) (record : IntentRecord) (prior : Option (List UInt8)) :
    List (IndexKey × Option (List UInt8)) :=
  match fleetOf record with
  | some fleet => [(payerKey fleet.1, some (payerValue (payerCount prior + 1) height record.transactionId))]
  | none => []

def changes7 (height : Nat) (record : IntentRecord) : List (IndexKey × Option (List UInt8)) :=
  match fleetOf record with
  | some (_, some destination) => [(incomingKey destination height, some (transactionValue record.transactionId))]
  | _ => []

/-- **The rows of a record** at `height`, given its verified priors. -/
def changes (height : Nat) (record : IntentRecord) (priors : Priors) : List (IndexKey × Option (List UInt8)) :=
  changes01 height record ++ changes2 height record ++ changesLinks height record priors ++
    changes6 height record priors.payer ++ changes7 height record

/-- Apply a record's rows on the Store's rows, against `root`: every prior is
opened or revealed and VERIFIED against `root` first; a family-0/1 key already
present (or repeated within the record) is refused — the executor never accepts
a transaction id twice or consumes a nullifier twice, so a disagreement is a
refusal, not an overwrite. -/
def apply (store : List Bool → Option Row) (root : Digest) (height : Nat) (record : IntentRecord) :
    Except String (Digest × List (List Bool × Row)) := do
  unless (keys01 record).Nodup do
    throw "the index already holds a key this record inserts (it disagrees with the executor)"
  let (points, prefixes) := reads record
  let mut answers : List (IndexKey × Option (List UInt8)) := []
  for k in points do
    let answer ← lookupRows store root k
    answers := (k, answer.value) :: answers
  if (keys01 record).any fun k => (answers.find? (·.1 = k)).bind (·.2) |>.isSome then
    throw "the index already holds a key this record inserts (it disagrees with the executor)"
  let mut revealed : List (List Bool × List (IndexKey × List UInt8)) := []
  for p in prefixes do
    let members ← revealRows store root p
    revealed := (p, members.members) :: revealed
  let priors := priorsWith (fun k => (answers.find? (·.1 = k)).bind (·.2))
    (fun p => ((revealed.find? (·.1 = p)).map (·.2)).getD []) record
  setAll store root (changes height record priors)

/-- The keys whose paths a batch of records (heights `start + 1`, …) may set or
delete, planned from the family-4 members read at the start: every change of
each record computed against the START priors. A link added by an earlier record
of the batch and changed by a later one is a new-row key of the earlier record,
so it is covered too. Only WHICH rows to read is planned here: `apply` verifies
everything it uses against the root it is given, and refuses what the rows do
not reach. -/
def plannedKeys (start : Nat) (records : List IntentRecord)
    (members : List Bool → List (IndexKey × List UInt8)) : List IndexKey :=
  (records.zipIdx (start + 1)).flatMap fun entry =>
    (changes entry.2 entry.1 (priorsWith (fun _ => none) members entry.1)).map (·.1)

end IndexRows

#assert_axioms fixedOctets_fixedValue
#assert_axioms rank_foldl
#assert_axioms rank_testBits
#assert_axioms rank_byteBits
#assert_axioms rank_bytesBits
#assert_axioms foldl_reverse_denote
#assert_axioms rank_heightSecondary
#assert_axioms heightSecondary_injective

end Minidregg.Compiler.DurableIndex
