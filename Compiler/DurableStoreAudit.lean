/-
# Compiler.DurableStoreAudit — `mini store audit`: the Store re-derived from genesis

KN2-STORE-OPEN moves the prefix checks from the open to the moment of use
(`Compiler.DurableHistoryStore`). The full re-check stays available, on demand
and in the journey gate: this audit reads EVERY entry and re-derives, from the
seed, everything the Store holds:

1. the log chain over every record and every tag's MAC (`verifyTags`);
2. the accumulator: every tag's carried frontier digest (`walkFrontier`) and
   every stored accumulator node row (space 1) against the honest node;
3. the index trie: the root after every record (each tag's carried index root)
   and every stored row (space 3, newest version at the head), by applying each
   record's rows (`IndexRows.apply`, every family) in order over an in-memory row map — a row
   missing from the Store, or a different one, is refused naming its prefix;
4. every retained checkpoint: its body equals the genesis replay at its height
   (state, chain, frontier, index root);
5. the head root against the replayed root.

The Host's `store-audit` arm runs this, then `NativeHost.audit` (every signed
ingress re-admitted at its original prefix). Each failure is a named refusal.
-/
import Compiler.DurableHistoryStore

namespace Minidregg.Compiler.DurableStoreAudit

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed Image)
open Minidregg.Kernel.DurableCheckpoint (State prepare)
open Minidregg.Compiler.DurableReceiverIO
open Minidregg.Compiler.DurableHistory (trailerCarried leafDigest frontierDigest nodeKey)
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.DurableLogTags (chainPrefixes verifyTags)

set_option autoImplicit false

/-! ## What the frontier walk establishes (the open and the audit both run it) -/

/-- The accumulator frontier after pushing the leaves of `entries` (each with
the chain after it and the root its tag carries). -/
def frontierAfter : Nat → List (Nat × Digest) → List (Entry × Digest) → List (Nat × Digest)
  | _, frontier, [] => frontier
  | height, frontier, (entry, chain) :: rest =>
      frontierAfter (height + 1) (DurableHistory.Frontier.push frontier
        (leafDigest (height + 1) entry.record chain
          ((trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩))) rest

/-- **The walk's frontier is the accumulator's**, and **the last tag carries
its digest**: so the frontier the open hands to `Head.verify` is the one the
head tag's MAC binds. -/
theorem walkFrontier_ok :
    ∀ (height : Nat) (frontier : List (Nat × Digest)) (entries : List (Entry × Digest))
      (result : List (Nat × Digest)),
      walkFrontier height frontier entries = .ok result →
        result = frontierAfter height frontier entries ∧
        ∀ last ∈ entries.getLast?, ∃ carried, trailerCarried last.1.tag = some carried ∧
          carried.frontier = frontierDigest (height + entries.length) result
  | height, frontier, [], result, walked => by
      simp only [walkFrontier, Except.ok.injEq] at walked
      subst walked
      exact ⟨rfl, by simp⟩
  | height, frontier, (entry, chain) :: rest, result, walked => by
      unfold walkFrontier at walked
      split at walked
      · cases walked
      · rename_i carried found
        simp only at walked
        split at walked
        · cases walked
        · rename_i reached
          have next := walkFrontier_ok (height + 1) _ rest result walked
          have carriedRoot : (trailerCarried entry.tag).map (·.root) = some carried.root := by
            rw [found]; rfl
          refine ⟨by rw [next.1]; simp only [frontierAfter, carriedRoot, Option.getD_some], ?_⟩
          intro last member
          cases rest with
          | nil =>
              simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at member
              subst member
              simp only [walkFrontier, Except.ok.injEq] at walked
              subst walked
              exact ⟨carried, found, by simpa using Classical.not_not.mp reached⟩
          | cons second more =>
              have inner := next.2 last (by simpa [List.getLast?_cons_cons] using member)
              simpa [Nat.add_assoc, Nat.add_comm 1] using inner

#assert_axioms walkFrontier_ok

structure Report where
  records : Nat
  accumulatorNodes : Nat
  indexKeys : Nat
  indexRows : Nat
  checkpoints : Nat
  deriving Repr

def Report.line (report : Report) : String :=
  s!"store audit: {report.records} records; chain, tags, accumulator ({report.accumulatorNodes} nodes), index ({report.indexKeys} keys, {report.indexRows} nodes), {report.checkpoints} checkpoints and the head root re-derived from genesis"

def refused {α : Type} (name : String) : Except String α := .error s!"store audit refused: {name}"

/-- Every accumulator node the log's appends complete, with its honest digest. -/
def honestNodes (entries : List Entry) (chains : List Digest) : List ((Nat × Nat) × Digest) :=
  let rec go : Nat → List (Nat × Digest) → List (Entry × Digest) → List ((Nat × Nat) × Digest)
    | _, _, [] => []
    | height, frontier, (entry, chain) :: rest =>
        let root := (trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩
        let leaf := leafDigest (height + 1) entry.record chain root
        DurableHistory.completedNodes frontier (height + 1) leaf ++
          go (height + 1) (DurableHistory.Frontier.push frontier leaf) rest
  go 0 [] (entries.zip (chains.drop 1))

/-- Apply every record's rows from the empty trie — through `IndexRows.apply`,
the one function every append and every open runs, never a second copy — checking
each tag's carried index root; the final rows (newest version per prefix) and
the number of keys the final trie holds. -/
def rebuildIndex (records : List IntentRecord) (entries : List Entry) :
    Except String (List (List Bool × DurableIndex.Row) × Nat) := do
  let mut rows : Std.HashMap (List Bool) DurableIndex.Row := {}
  let mut root := DurableIndex.emptyDigest
  for (height, record, entry) in (List.range' 1 records.length).zip (records.zip entries) do
    let current := rows
    let (root', written) ← (DurableIndex.IndexRows.apply (fun path => current.get? path) root height
        record).mapError
      fun message => s!"store audit refused: index at height {height}: {message}"
    rows := written.foldl (fun map row => map.insert row.1 row.2) rows
    root := root'
    match trailerCarried entry.tag with
    | some carried =>
        if carried.indexRoot ≠ root then
          throw s!"store audit refused: the tag at height {height} carries an index root the log does not reach"
    | none => throw s!"store audit refused: the tag at height {height} is not a v4 trailer"
  let final := rows
  return (rows.toList, (DurableIndex.collect (fun path => final.get? path) 521 [] root).length)

/-- Every retained checkpoint, oldest first (walked down from the head). -/
def retainedCheckpoints (transport : Transport) (head : Nat) :
    IO (Except String (List (Nat × List UInt8))) := do
  let mut heights : List (Nat × List UInt8) := []
  let mut below := head
  for _ in List.range (head + 1) do
    match ← transport.checkpointAt below with
    | .error message => return .error message
    | .ok none => return .ok heights
    | .ok (some checkpoint) =>
        heights := (checkpoint.height, checkpoint.bytes) :: heights
        if checkpoint.height = 0 then return .ok heights
        below := checkpoint.height - 1
  return .ok heights

/-- **The audit.** Reads every entry; every check refuses by name. -/
def audit (transport : Transport) (rootBytes : List UInt8 → Digest) : IO (Except String Report) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let stored ← match ← transport.read 1 true with
    | .error message => return .error message
    | .ok none => return .error "durable store is not initialized"
    | .ok (some stored) => pure stored
  let some seedBytes := stored.seed | return .error "durable seed missing"
  let some seed := seedFrame.decode seedBytes | return .error "noncanonical durable seed"
  if stored.entries.length ≠ stored.head then return refused "the head does not match its entries"
  let mut records : List IntentRecord := []
  for (height, entry) in (List.range' 1 stored.entries.length).zip stored.entries do
    match recordFrame.decode entry.record with
    | some record => records := records ++ [record]
    | none => return refused s!"noncanonical durable log record at height {height}"
  let logStart := transport.logStart seed
  let chains := chainPrefixes logStart records
  -- 1. chain + every tag MAC
  if let .error message := verifyTags key 0 chains (stored.entries.map (·.tag)) then
    return refused message
  -- 2. accumulator: carried frontier digests, then every stored node row
  if let .error message := walkFrontier 0 [] (stored.entries.zip (chains.drop 1)) then
    return refused message
  let nodes := honestNodes stored.entries chains
  match ← transport.history ⟨stored.head, [],
      nodes.map fun node => (DurableIndex.accumulatorSpace, nodeKey node.1.1 node.1.2)⟩ with
  | .error message => return .error message
  | .ok read =>
      for (node, found) in nodes.zip read.nodes do
        if found.2.2.map (·.2) ≠ some (Tower256ConcreteBackend.digestStream.encode node.2) then
          return refused s!"accumulator node (level {node.1.1}, end {node.1.2}) differs from the log"
  -- 3. index: carried roots, then every stored row (newest version at the head)
  let (rows, keys) ← match rebuildIndex records stored.entries with
    | .error message => return .error message
    | .ok result => pure result
  match ← transport.history ⟨stored.head, [],
      rows.map fun row => (DurableIndex.indexSpace, DurableIndex.rowKey row.1)⟩ with
  | .error message => return .error message
  | .ok read =>
      for (row, found) in rows.zip read.nodes do
        if found.2.2.map (·.2) ≠ some (DurableIndex.rowStream.encode row.2) then
          return refused s!"index node at prefix of length {row.1.length} differs from the log (missing or altered)"
  -- 4 + 5. replay from the seed; every retained checkpoint equals the replay at its height
  let checkpointHeights ← match ← retainedCheckpoints transport stored.head with
    | .error message => return .error message
    | .ok heights => pure heights
  let initial ← match loadSeed rootBytes logStart seed with
    | .error message => return .error message
    | .ok loaded => pure loaded
  let mut current := initial
  let mut indexAt : Digest := DurableIndex.emptyDigest
  for (height, record, entry) in (List.range' 1 records.length).zip (records.zip stored.entries) do
    let some intent := record.bind? rootBytes
      | return refused s!"the record at height {height} does not bind its roots"
    match prepare current.image current.baseHeight current.base current.snapshot
        current.withinLog current.resumed intent with
    | .inl ready => current := current.extend ready
    | .inr _ => return refused s!"the record at height {height} does not replay through the canonical executor"
    indexAt := (trailerCarried entry.tag).map (·.indexRoot) |>.getD indexAt
    if let some bytes := (checkpointHeights.find? (·.1 = height)).map (·.2) then
      let expected := checkpointFrame.encode (sealAt key height current.chain (current.frontier.getD [])
        indexAt (State.ofSnapshot current.image current.snapshot) current.worldRoot)
      if bytes ≠ expected then
        return refused s!"checkpoint at height {height} differs from the genesis replay"
  match stored.entries.getLast?.bind (trailerCarried ·.tag) with
  | some carried =>
      if carried.root ≠ current.worldRoot then return refused "the head root differs from the replayed root"
  | none => pure ()
  return .ok ⟨records.length, nodes.length, keys, rows.length, checkpointHeights.length⟩

end Minidregg.Compiler.DurableStoreAudit
