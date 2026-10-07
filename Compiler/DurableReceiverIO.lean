/-
# Compiler.DurableReceiverIO — the host's durable log, checkpoints and receiving loop

The store is a seed, an append-only log of accepted records, and MAC'd
checkpoints (`Compiler.DurableCheckpointCodec`). Lean decodes, chains, MACs,
resumes and executes; the native helper stores opaque bytes, appends entry
`h + 1` only while the head is `h`, and assigns no meaning to anything.

* **Open** (`load`): recompute the log chain over every stored record, open
  the latest checkpoint (key id, recomputed world root, MAC, chain value),
  verify every entry's tag (`DurableLogTags.verifyTags`), then
  `DurableCheckpoint.resume` — materialize the checkpoint and replay only the
  records after it. No signed ingress is re-admitted here; that is the operator `audit` (`NativeHostReplay.verifyLoaded`).
* **Receive** (`receiveLoadedDetailed`): run the shared executor at the loaded
  snapshot (`DurableCheckpoint.prepare`), append one entry, read that one entry
  back. Every `checkpointEvery` records the receiver seals a checkpoint of the
  new head and rebases its in-memory state on it.
* A store holding the retired whole-image record refuses (the helper reports
  it); there is no migration: re-genesis.

The physical assumptions are SQLite transaction integrity, honest byte
transport and the OS durability floor; no Lean theorem proves those systems.
The MAC key file's custody is the operator's (`DurableCheckpointCodec`).
-/
import Compiler.DurableCheckpointCodec
import Compiler.NativeCoprocess
import Compiler.DurableLogTags
import Compiler.DurableHistory
import Compiler.DurableIndexFamilies
import Std.Data.HashMap
import Std.Data.HashSet
import Kernel.PresenceIndex
import Kernel.TailBound
import Kernel.LinkIndex
import Kernel.SessionIndex

namespace Minidregg.Compiler.DurableReceiverIO

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.DurableLogTags (chainPrefixes verifyTags)
open Minidregg.Compiler.DurableHistory (Carried trailer trailerCarried leafDigest frontierDigest)

set_option autoImplicit false

inductive CasObservation where
  | installed
  | alreadyPresent
  | conflict
  | uncertain (detail : String)
  deriving Repr, DecidableEq

/-- One stored log entry: record bytes and the host's tag. -/
structure Entry where
  record : List UInt8
  tag : List UInt8
  deriving DecidableEq, Repr

structure StoredCheckpoint where
  height : Nat
  bytes : List UInt8

/-- One accumulator / spent-map node row an append writes beside its entry
(`durable_node`; space 1 = log accumulator, space 3 = the index trie). -/
structure NodeWrite where
  space : Nat
  key : List UInt8
  value : List UInt8
  deriving DecidableEq, Repr

/-- An at-use history read (`durable-history`): the head, the named entries,
and each named node's latest version at or below the requested height. -/
structure HistoryRequest where
  atHeight : Nat
  heights : List Nat
  nodes : List (Nat × List UInt8)

structure HistoryRead where
  head : Nat
  entries : List (Nat × Entry)
  nodes : List (Nat × List UInt8 × Option (Nat × List UInt8))

/-- One physical read: the head height, optionally the seed and the latest
checkpoint, and the consecutive entries from the requested height. -/
structure Stored where
  head : Nat
  seed : Option (List UInt8)
  checkpoint : Option StoredCheckpoint
  entries : List Entry

/-- The only native boundary. An error is not proof a write failed. -/
structure Transport where
  /-- Entries from the given height; the Bool asks for the seed and checkpoint. -/
  read : Nat → Bool → IO (Except String (Option Stored))
  /-- Append at the given height iff the head is one below it, with the node
  rows the append completes, in one transaction. -/
  append : Nat → Entry → List NodeWrite → IO CasObservation
  putCheckpoint : Nat → List UInt8 → IO (Except String Unit)
  initializeSeed : List UInt8 → IO CasObservation
  key : IO (Except String MacKey)
  checkpointEvery : Nat
  /-- The log chain's start for a seed (the host: `NativeHostCodec.logRoot0`
  of its domain and semantics), so one chain is both MAC'd and rooted. -/
  logStart : Seed → Digest
  /-- The deployment's system cell, whose tail law judges every new commit
  (`Kernel.TailBound.gate`).  Every native-host deployment sets it
  (`NativeHostContext.Config.transport`); `none` is a bare durable log with no
  system law, which only the durable-protocol probes construct. -/
  systemCell : Option CellId
  /-- A deployment-pinned source gate. Live receive and semantic replay run
  the same gate over the actual loaded snapshot. Native joint controllers use
  a typed exact-intent capability; raw client records never select an exemption. -/
  sourceGate : {rootBytes : List UInt8 → Digest} → DataSnapshot rootBytes →
    DataIntent rootBytes → Except RejectReason Unit := fun _ _ => .ok ()
  /-- The seed bytes alone, read before the physical head anchor, so a Store of
  another epoch is refused by naming its epoch (`SeedEpoch.refusal`), not as an
  anchor conflict. `none`: no seed, or no such read on this transport. -/
  peekSeed : IO (Except String (Option (List UInt8))) := pure (.ok none)
  /-- At-use history reads (entries by height, node rows by version). -/
  history : HistoryRequest → IO (Except String HistoryRead) :=
    fun _ => pure (.error "this transport serves no history reads")
  /-- The latest stored checkpoint at or below a height. -/
  checkpointAt : Nat → IO (Except String (Option StoredCheckpoint)) :=
    fun _ => pure (.error "this transport serves no checkpoint reads")
  /-- The light open's read under the head anchor: the seed, the latest
  checkpoint, and the entries from the checkpoint's height (inclusive; from 1
  when there is none) to the head. -/
  readFromCheckpoint : IO (Except String (Option Stored)) :=
    pure (.error "this transport serves no read from the checkpoint")

structure NativeConfig where
  binary : System.FilePath
  root : System.FilePath
  /-- The Store's 32-byte MAC key file (mode 0600, generated at bootstrap). -/
  key : System.FilePath
  checkpointEvery : Nat := 64
  /-- Opaque deployment/genesis identity for the physical rollback anchor. -/
  anchorIdentity : String := ""

/-- One Store call, through the binary's long-lived `serve` helper
(`NativeCoprocess.output`: the one-shot call's exact output, no fork of the Host). -/
def runNative (config : NativeConfig) (arguments : Array String) : IO IO.Process.Output :=
  NativeCoprocess.output config.binary.toString
    (if config.anchorIdentity.isEmpty then arguments
      else #["--anchor-identity", config.anchorIdentity] ++ arguments)

def parseCasOutput (output : IO.Process.Output) : CasObservation :=
  if output.exitCode == 0 && output.stderr == "" then
    match output.stdout with
    | "Installed\n" => .installed
    | "AlreadyPresent\n" => .alreadyPresent
    | _ => .uncertain "malformed native success response"
  else if output.exitCode == 4 && output.stdout == "" then
    .conflict
  else
    .uncertain s!"native response lost or failed (exit {output.exitCode}): {output.stderr}"

/-! ## The read file: big-endian u64 lengths, no interpretation -/

private def u64At (bytes : ByteArray) (position : Nat) : Option Nat :=
  if position + 8 ≤ bytes.size then
    some <| (List.range 8).foldl (fun value index => value * 256 + (bytes.get! (position + index)).toNat) 0
  else none

private def blobAt (bytes : ByteArray) (position : Nat) : Option (List UInt8 × Nat) := do
  let length ← u64At bytes position
  let start := position + 8
  if start + length ≤ bytes.size then
    some ((bytes.extract start (start + length)).toList, start + length)
  else none

private def entriesAt (bytes : ByteArray) : Nat → Nat → Nat → List Entry → Option (List Entry)
  | 0, position, _, acc => if position = bytes.size then some acc.reverse else none
  | count + 1, position, expected, acc => do
      let height ← u64At bytes position
      if height ≠ expected then none else
      let (record, afterRecord) ← blobAt bytes (position + 8)
      let (tag, afterTag) ← blobAt bytes afterRecord
      entriesAt bytes count afterTag (expected + 1) (⟨record, tag⟩ :: acc)

/-- `head`, a base flag (seed blob, checkpoint flag, checkpoint height and
blob), an entry count, then `(height, record, tag)` per entry, heights
consecutive from `fromHeight`. -/
def parseStored (fromHeight : Nat) (withBase : Bool) (bytes : ByteArray) : Option Stored := do
  let head ← u64At bytes 0
  let flag ← u64At bytes 8
  let (seed, checkpoint, position) ←
    if flag = 0 then
      if withBase then none else some (none, none, 16)
    else if flag = 1 ∧ withBase then do
      let (seed, afterSeed) ← blobAt bytes 16
      let hasCheckpoint ← u64At bytes afterSeed
      if hasCheckpoint = 0 then some (some seed, none, afterSeed + 8)
      else if hasCheckpoint = 1 then do
        let height ← u64At bytes (afterSeed + 8)
        let (checkpoint, afterCheckpoint) ← blobAt bytes (afterSeed + 16)
        some (some seed, some ⟨height, checkpoint⟩, afterCheckpoint)
      else none
    else none
  let count ← u64At bytes position
  let entries ← entriesAt bytes count (position + 8) fromHeight []
  if fromHeight + count = head + 1 ∨ (count = 0 ∧ head < fromHeight) then
    some ⟨head, seed, checkpoint, entries⟩
  else none

def NativeConfig.read (config : NativeConfig) (fromHeight : Nat) (withBase : Bool) :
    IO (Except String (Option Stored)) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "read.bin"
      let output ← runNative config #["durable-read", config.root.toString,
        toString fromHeight, if withBase then "1" else "0", path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        match parseStored fromHeight withBase (← IO.FS.readBinFile path) with
        | some stored => return .ok (some stored)
        | none => return .error "native durable read malformed"
      else if output.exitCode == 3 && output.stdout == "" then
        return .ok none
      else
        return .error s!"native durable read failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native durable read unavailable: {error}")

/-- `crashAt` is a lifecycle-test hook implemented by process exit inside the
native append transaction. Production `transport` always supplies `none`. -/
private def u64Bytes (value : Nat) : List UInt8 :=
  (List.range 8).reverse.map fun index => (value / 256 ^ index % 256).toUInt8

private def blobBytes (bytes : List UInt8) : List UInt8 := u64Bytes bytes.length ++ bytes

/-- The NODES file: u64 count, then u64 space, key blob, value blob per node. -/
def encodeNodes (nodes : List NodeWrite) : List UInt8 :=
  u64Bytes nodes.length ++ nodes.flatMap fun node =>
    u64Bytes node.space ++ blobBytes node.key ++ blobBytes node.value

def NativeConfig.append (config : NativeConfig) (height : Nat) (entry : Entry)
    (nodes : List NodeWrite) (crashAt : Option String := none) : IO CasObservation :=
  try
    IO.FS.withTempDir fun directory => do
      let recordPath := directory / "record.bin"
      let tagPath := directory / "tag.bin"
      let nodesPath := directory / "nodes.bin"
      IO.FS.writeBinFile recordPath entry.record.toByteArray
      IO.FS.writeBinFile tagPath entry.tag.toByteArray
      IO.FS.writeBinFile nodesPath (encodeNodes nodes).toByteArray
      let arguments := match crashAt with
        | none => #["durable-append", config.root.toString, toString height,
            recordPath.toString, tagPath.toString, nodesPath.toString]
        | some phase => #["durable-append-crash", config.root.toString, toString height,
            recordPath.toString, tagPath.toString, nodesPath.toString, phase]
      return parseCasOutput (← runNative config arguments)
  catch error => pure (.uncertain s!"native append unavailable: {error}")

def NativeConfig.putCheckpoint (config : NativeConfig) (height : Nat) (bytes : List UInt8) :
    IO (Except String Unit) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "checkpoint.bin"
      IO.FS.writeBinFile path bytes.toByteArray
      let output ← runNative config #["durable-checkpoint", config.root.toString,
        toString height, path.toString]
      if output.exitCode == 0 && output.stderr == "" then return .ok ()
      else return .error s!"native checkpoint write failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native checkpoint unavailable: {error}")

def NativeConfig.initialize (config : NativeConfig) (seedBytes : List UInt8) : IO CasObservation :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "seed.bin"
      IO.FS.writeBinFile path seedBytes.toByteArray
      return parseCasOutput (← runNative config #["durable-init", config.root.toString,
        path.toString])
  catch error => pure (.uncertain s!"native initialize unavailable: {error}")

/-- The key file must hold exactly 32 bytes. Its 0600 mode is checked by the
bootstrap that created it and by the operator; Lean reads, never writes it. -/
def NativeConfig.readKey (config : NativeConfig) : IO (Except String MacKey) :=
  try
    let bytes := (← IO.FS.readBinFile config.key).toList
    match MacKey.ofBytes? bytes with
    | some key => return .ok key
    | none => return .error "checkpoint MAC key must be exactly 32 bytes"
  catch error => pure (.error s!"checkpoint MAC key unavailable: {error}")

/-- The seed bytes alone, without the head anchor (read-only; the Store
installs a seed once and never replaces it). -/
def NativeConfig.peekSeed (config : NativeConfig) : IO (Except String (Option (List UInt8))) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "seed.bin"
      let output ← runNative config #["durable-seed", config.root.toString, path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        return .ok (some (← IO.FS.readBinFile path).toList)
      else if output.exitCode == 3 && output.stdout == "" then
        return .ok none
      else
        return .error s!"native durable seed read failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native durable seed read unavailable: {error}")

private def historyEntriesAt (bytes : ByteArray) : Nat → Nat → List (Nat × Entry) →
    Option (List (Nat × Entry) × Nat)
  | 0, position, acc => some (acc.reverse, position)
  | count + 1, position, acc => do
      let height ← u64At bytes position
      let (record, afterRecord) ← blobAt bytes (position + 8)
      let (tag, afterTag) ← blobAt bytes afterRecord
      historyEntriesAt bytes count afterTag ((height, ⟨record, tag⟩) :: acc)

private def historyNodesAt (bytes : ByteArray) :
    Nat → Nat → List (Nat × List UInt8 × Option (Nat × List UInt8)) →
    Option (List (Nat × List UInt8 × Option (Nat × List UInt8)))
  | 0, position, acc => if position = bytes.size then some acc.reverse else none
  | count + 1, position, acc => do
      let space ← u64At bytes position
      let (key, afterKey) ← blobAt bytes (position + 8)
      let flag ← u64At bytes afterKey
      if flag = 0 then historyNodesAt bytes count (afterKey + 8) ((space, key, none) :: acc)
      else if flag = 1 then do
        let height ← u64At bytes (afterKey + 8)
        let (value, afterValue) ← blobAt bytes (afterKey + 16)
        historyNodesAt bytes count afterValue ((space, key, some (height, value)) :: acc)
      else none

/-- The `durable-history` output: u64 head; entries; nodes (see the helper). -/
def parseHistory (bytes : ByteArray) : Option HistoryRead := do
  let head ← u64At bytes 0
  let entryCount ← u64At bytes 8
  let (entries, afterEntries) ← historyEntriesAt bytes entryCount 16 []
  let nodeCount ← u64At bytes afterEntries
  let nodes ← historyNodesAt bytes nodeCount (afterEntries + 8) []
  some ⟨head, entries, nodes⟩

def encodeHistoryRequest (request : HistoryRequest) : List UInt8 :=
  u64Bytes request.atHeight ++ u64Bytes request.heights.length ++
    request.heights.flatMap u64Bytes ++ u64Bytes request.nodes.length ++
    request.nodes.flatMap fun node => u64Bytes node.1 ++ blobBytes node.2

def NativeConfig.history (config : NativeConfig) (request : HistoryRequest) :
    IO (Except String HistoryRead) :=
  try
    IO.FS.withTempDir fun directory => do
      let requestPath := directory / "request.bin"
      let path := directory / "history.bin"
      IO.FS.writeBinFile requestPath (encodeHistoryRequest request).toByteArray
      let output ← runNative config #["durable-history", config.root.toString,
        requestPath.toString, path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        match parseHistory (← IO.FS.readBinFile path) with
        | some read => return .ok read
        | none => return .error "native durable history read malformed"
      else return .error s!"native durable history read failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native durable history read unavailable: {error}")

/-- The checkpoint height a base read names (`none`: no checkpoint). -/
def checkpointHeightOf (bytes : ByteArray) : Option (Option Nat) := do
  let flag ← u64At bytes 8
  if flag ≠ 1 then none
  let (_, afterSeed) ← blobAt bytes 16
  let hasCheckpoint ← u64At bytes afterSeed
  if hasCheckpoint = 0 then some none
  else if hasCheckpoint = 1 then some (some (← u64At bytes (afterSeed + 8)))
  else none

def NativeConfig.readFromCheckpoint (config : NativeConfig) : IO (Except String (Option Stored)) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "read.bin"
      let output ← runNative config #["durable-read", config.root.toString, "1", "2", path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        let bytes ← IO.FS.readBinFile path
        match checkpointHeightOf bytes with
        | none => return .error "native durable read malformed"
        | some checkpoint =>
            match parseStored ((checkpoint.getD 1).max 1) true bytes with
            | some stored => return .ok (some stored)
            | none => return .error "native durable read malformed"
      else if output.exitCode == 3 && output.stdout == "" then
        return .ok none
      else
        return .error s!"native durable read failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native durable read unavailable: {error}")

def NativeConfig.checkpointAt (config : NativeConfig) (height : Nat) :
    IO (Except String (Option StoredCheckpoint)) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "checkpoint.bin"
      let output ← runNative config #["durable-checkpoint-at", config.root.toString,
        toString height, path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        let bytes ← IO.FS.readBinFile path
        match u64At bytes 0 with
        | some 0 => if bytes.size = 8 then return .ok none else return .error "native checkpoint read malformed"
        | some 1 =>
            match u64At bytes 8, blobAt bytes 16 with
            | some found, some (checkpoint, after) =>
                if after = bytes.size then return .ok (some ⟨found, checkpoint⟩)
                else return .error "native checkpoint read malformed"
            | _, _ => return .error "native checkpoint read malformed"
        | _ => return .error "native checkpoint read malformed"
      else return .error s!"native checkpoint read failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native checkpoint read unavailable: {error}")

def NativeConfig.transport (config : NativeConfig) (logStart : Seed → Digest)
    (systemCell : CellId) : Transport :=
  ⟨config.read, fun height entry nodes => config.append height entry nodes, config.putCheckpoint,
    config.initialize, config.readKey, config.checkpointEvery, logStart, some systemCell, fun _ _ => .ok (),
    config.peekSeed, config.history, config.checkpointAt, config.readFromCheckpoint⟩

/-- ByteArray's derived equality compares every byte, with no digest premise. -/
theorem byteArray_beq_exact (left right : List UInt8) :
    (left.toByteArray == right.toByteArray) = true ↔ left = right := by
  have byteArrayBEq (a b : ByteArray) : (a == b) = true ↔ a = b := by
    cases a with
    | mk data =>
      cases b with
      | mk other =>
        unfold BEq.beq ByteArray.instBEq
        unfold ByteArray.instBEq.beq
        simp only [ByteArray.mk.injEq, beq_iff_eq]
  rw [byteArrayBEq]
  constructor
  · intro exact
    have lists := congrArg (fun bytes : ByteArray => bytes.data.toList) exact
    simpa using lists
  · intro exact
    subst right
    rfl

/-- Images compare by their canonical encoding (the ten-lane charge is a
function, so there is no structural equality to derive). -/
instance : DecidableEq Image := fun left right =>
  decidable_of_iff ((DurableReceiverCodec.encode left).toByteArray ==
      (DurableReceiverCodec.encode right).toByteArray)
    ((byteArray_beq_exact _ _).trans
      ⟨fun same => DurableReceiverCodec.encode_injective same, congrArg _⟩)

/-! ## The world root, cached -/

open Minidregg.Theory.AuthMap (write)
open Minidregg.Kernel.WorldRoot (Key deployed deployedRoot slotsOf)
open Minidregg.Kernel.WorldRootCache

/-- The world root, cached. `entries` lists the slot writes since the tree was
built, in order; the tree is good for their slot map, so its digest is C1's
`deployedRoot entries` (`RootCache.root_eq`). A write rehashes one path. -/
structure RootCache where
  entries : List (Key × Digest)
  tree : DeployedTree
  good : Good deployed deployedEmpties (slotsOf deployed.ix entries) deployed.depth [] tree

def RootCache.ofEntries (entries : List (Key × Digest)) : RootCache :=
  ⟨entries, deployedOf entries, ofEntries_good deployed deployedEmpties entries⟩

def RootCache.write (cache : RootCache) (key : Key) (value : Digest) : RootCache :=
  ⟨cache.entries ++ [(key, value)], deployedWrite cache.tree key (some value), by
    rw [slotsOf_snoc]
    exact insertWrite_good deployed deployedEmpties cache.good key (some value)⟩

def RootCache.root (cache : RootCache) : Digest := deployedDigest cache.tree

/-- The cached root is the specification root of the cache's entries. -/
theorem RootCache.root_eq (cache : RootCache) : cache.root = deployedRoot cache.entries := by
  rw [Kernel.WorldRoot.deployedRoot_eq]
  exact digest_eq deployed deployedEmpties deployedEmpties_eq _ _ _ _ cache.good

/-- The world-root entries of a served state: the system slot (height, log
root), then every enumerable cell's current root — C1's `worldEntries`, read
off the resumed snapshot (whose roots need no rehash) instead of the image. -/
def entriesOf {rootBytes : List UInt8 → Digest} (image : Image) (snapshot : DataSnapshot rootBytes)
    (chain : Digest) : List (Key × Digest) :=
  (.system, systemLeaf image.accepted.length chain) ::
    image.cellIds.map fun cellId => (.cell cellId.value, snapshot.model.roots cellId)

/-- The slot writes one accepted record makes: the system slot, then each
written cell's exact post root. -/
def recordSlots (height : Nat) (chain : Digest) (record : IntentRecord) : List (Key × Digest) :=
  (.system, systemLeaf height chain) ::
    record.writes.map fun write => (.cell write.cellId.value, write.exactPost)

/-- The slot the cache holds at `k`'s index path, read down the tree (no hashing). -/
def RootCache.occupant (cache : RootCache) (k : Key) : Option (Key × Digest) :=
  cache.tree.find deployed.depth (deployed.ix k)

theorem RootCache.occupant_eq (cache : RootCache) (k : Key) :
    cache.occupant k = slotsOf deployed.ix cache.entries (deployed.ix k) := by
  have := find_good deployed deployedEmpties _ deployed.depth (deployed.ix k) [] cache.tree
    (deployed.ix_length k) cache.good
  simpa [RootCache.occupant] using this

/-- Writing `k` evicts no other key: its index path is empty or already holds `k`. -/
def RootCache.fresh (cache : RootCache) (k : Key) : Bool :=
  match cache.occupant k with
  | none => true
  | some x => decide (x.1 = k)

theorem RootCache.fresh_sound {cache : RootCache} {k : Key} (fresh : cache.fresh k = true) :
    ∀ x, slotsOf deployed.ix cache.entries (deployed.ix k) = some x → x.1 = k := by
  intro x hx
  unfold RootCache.fresh at fresh
  rw [cache.occupant_eq, hx] at fresh
  simpa using fresh

/-- Every key of the cache is found at its own index path: no two keys share one. -/
def RootCache.injectiveCheck (cache : RootCache) : Bool :=
  cache.entries.all fun e => match cache.occupant e.1 with
    | some x => decide (x.1 = e.1)
    | none => false

theorem RootCache.injectiveCheck_sound {cache : RootCache} (checked : cache.injectiveCheck = true) :
    KeysInjective deployed.ix cache.entries := by
  apply keysInjective_of_occupants
  intro e he
  have found := List.all_eq_true.mp checked e he
  rw [cache.occupant_eq] at found
  cases hx : slotsOf deployed.ix cache.entries (deployed.ix e.1) with
  | none => simp [hx] at found
  | some x => exact ⟨x, rfl, by simpa [hx] using found⟩

/-- Write the slots while none evicts another key: the advanced cache, or
`none` at the first slot whose index path holds a different key. -/
def RootCache.writeAllFresh? (cache : RootCache) : List (Key × Digest) → Option RootCache
  | [] => some cache
  | slot :: slots =>
      if cache.fresh slot.1 then (cache.write slot.1 slot.2).writeAllFresh? slots else none

theorem RootCache.writeAllFresh?_sound :
    ∀ (cache : RootCache) (slots : List (Key × Digest)) (next : RootCache),
      cache.writeAllFresh? slots = some next → KeysInjective deployed.ix cache.entries →
      next.entries = cache.entries ++ slots ∧ KeysInjective deployed.ix next.entries
  | cache, [], next, wrote, inj => by
      simp only [writeAllFresh?, Option.some.injEq] at wrote
      subst wrote
      exact ⟨by simp, inj⟩
  | cache, slot :: slots, next, wrote, inj => by
      simp only [writeAllFresh?] at wrote
      split at wrote
      next fresh =>
        have inj' : KeysInjective deployed.ix (cache.write slot.1 slot.2).entries :=
          keysInjective_snoc deployed.ix inj slot (RootCache.fresh_sound fresh)
        obtain ⟨entries, inj''⟩ := writeAllFresh?_sound _ slots next wrote inj'
        refine ⟨?_, inj''⟩
        rw [entries]
        simp [RootCache.write]
      next => cases wrote

/-- **The cache holds the served entries `es`**: it gives every key the value
`es` last gives it, and a checked flag says whether no two of its keys share an
index path. Under the flag the cached root is the root of `es`
(`RootsExact.root_eq`), though the cache was written in log order and `es` is
in enumeration order. -/
structure RootsExact (cache : RootCache) (es : List (Key × Digest)) where
  agree : ∀ k, lastVal cache.entries k = lastVal es k
  injective : Bool
  injectiveSound : injective = true → KeysInjective deployed.ix cache.entries

def RootsExact.ofEntries (es : List (Key × Digest)) : RootsExact (RootCache.ofEntries es) es :=
  ⟨fun _ => rfl, (RootCache.ofEntries es).injectiveCheck, RootCache.injectiveCheck_sound⟩

theorem RootsExact.root_eq {cache : RootCache} {es : List (Key × Digest)}
    (exact : RootsExact cache es) (injective : exact.injective = true) :
    cache.root = deployedRoot es := by
  rw [cache.root_eq, Kernel.WorldRoot.deployedRoot_eq, Kernel.WorldRoot.deployedRoot_eq,
    slotsOf_eq_of_lastVal deployed.ix (exact.injectiveSound injective) exact.agree]

/-- Advance a cache holding `es` by the slot writes that take `es` to `es'`:
one path per slot while no slot evicts another key; on an index collision (a
collision of the deployed hash) a full rebuild of `es'`. -/
def RootsExact.advance {cache : RootCache} {es es' : List (Key × Digest)}
    (exact : RootsExact cache es) (slots : List (Key × Digest))
    (step : ∀ k, lastVal es' k = (lastVal slots k).or (lastVal es k)) :
    (next : RootCache) × RootsExact next es' :=
  if injective : exact.injective = true then
    match wrote : cache.writeAllFresh? slots with
    | some next =>
        let sound := RootCache.writeAllFresh?_sound cache slots next wrote
          (exact.injectiveSound injective)
        ⟨next, ⟨fun k => by rw [sound.1, lastVal_append, exact.agree, step], true,
          fun _ => sound.2⟩⟩
    | none => ⟨RootCache.ofEntries es', RootsExact.ofEntries es'⟩
  else ⟨RootCache.ofEntries es', RootsExact.ofEntries es'⟩

/-! ## The served entries, step by step -/

theorem lastVal_cells_system {α : Type} (ids : List α) (key : α → Nat) (root : α → Digest) :
    lastVal (ids.map fun id => (Key.cell (key id), root id)) Key.system = none := by
  simp [lastVal, List.filter_map, Function.comp_def]

/-- An enumeration without repeats gives a cell key its id's root, or nothing. -/
theorem lastVal_cellIds (ids : List CellId) (nodup : ids.Nodup) (root : CellId → Digest) (n : Nat) :
    lastVal (ids.map fun id => (Key.cell id.value, root id)) (Key.cell n) =
      if (⟨n⟩ : CellId) ∈ ids then some (root ⟨n⟩) else none := by
  induction ids with
  | nil => simp [lastVal]
  | cons a rest ih =>
      rw [List.map_cons, lastVal_cons, ih (List.nodup_cons.mp nodup).2]
      have fresh := (List.nodup_cons.mp nodup).1
      by_cases same : a = ⟨n⟩
      · subst same
        simp [fresh]
      · have ne : a.value ≠ n := fun h => same (by cases a; simp_all)
        by_cases member : (⟨n⟩ : CellId) ∈ rest
        · simp [member, ne]
        · simp [member, ne, Ne.symm same]

theorem lookupPost_member (writes : List DataWrite) (cellId : CellId) {post : Digest}
    (found : DurableCommitProtocol.Snapshot.lookupPost cellId
      (writes.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId)) = some post) :
    cellId ∈ writes.map DataWrite.cellId := by
  induction writes with
  | nil => simp [DurableCommitProtocol.Snapshot.lookupPost] at found
  | cons write rest ih =>
      simp only [List.map_cons, DurableCommitProtocol.Snapshot.lookupPost] at found
      split at found
      next same => simp [same]
      next => exact List.mem_cons_of_mem _ (ih found)

theorem lookupPost_isSome (writes : List DataWrite) (cellId : CellId)
    (member : cellId ∈ writes.map DataWrite.cellId) :
    (DurableCommitProtocol.Snapshot.lookupPost cellId
      (writes.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId))).isSome := by
  induction writes with
  | nil => cases member
  | cons write rest ih =>
      simp only [List.map_cons, DurableCommitProtocol.Snapshot.lookupPost]
      split
      · rfl
      · rename_i differs
        rcases List.mem_cons.mp member with same | inRest
        · exact absurd same.symm differs
        · exact ih inRest

/-- Distinct written cells: a written cell key's last slot value is the
executor's first-match post root. -/
theorem lastVal_writes (writes : List DataWrite) (nodup : (writes.map DataWrite.cellId).Nodup)
    (n : Nat) :
    lastVal (writes.map fun write => (Key.cell write.cellId.value, write.exactPost)) (Key.cell n) =
      DurableCommitProtocol.Snapshot.lookupPost ⟨n⟩
        (writes.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId)) := by
  induction writes with
  | nil => simp [lastVal, DurableCommitProtocol.Snapshot.lookupPost]
  | cons write rest ih =>
      rw [List.map_cons, lastVal_cons, ih (List.nodup_cons.mp nodup).2]
      simp only [List.map_cons, DurableCommitProtocol.Snapshot.lookupPost]
      have fresh := (List.nodup_cons.mp nodup).1
      by_cases same : write.cellId = ⟨n⟩
      · rw [if_pos same]
        cases later : DurableCommitProtocol.Snapshot.lookupPost (⟨n⟩ : CellId)
            (rest.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId)) with
        | none => simp [same]
        | some post =>
            exact absurd (same ▸ lookupPost_member rest ⟨n⟩ later) fresh
      · have ne : write.cellId.value ≠ n := fun h => same (by cases h; rfl)
        rw [if_neg same]
        simp [ne]

/-- **The served entries after an accepted intent** are the served entries
before it overwritten by the intent's slot writes (`recordSlots`): the system
slot's new leaf, and each written cell's post root. -/
theorem entriesOf_step {rootBytes : List UInt8 → Digest} (image : Image)
    (before next : DataSnapshot rootBytes) (intent : DataIntent rootBytes) (chain chain' : Digest)
    (executed : DurableDataIntent.execute .complete before intent = .accepted next) (k : Key) :
    lastVal (entriesOf (image.append intent) next chain') k =
      (lastVal (recordSlots (image.accepted.length + 1) chain' (IntentRecord.ofIntent intent)) k).or
        (lastVal (entriesOf image before chain) k) := by
  have accepted : next = DataSnapshot.install before intent ∧
      (intent.writes.map DataWrite.cellId).Nodup := by
    unfold DurableDataIntent.execute at executed
    split at executed
    · split at executed <;> cases executed
    · split at executed
      · cases executed
      · rename_i passed
        cases executed
        refine ⟨rfl, ?_⟩
        unfold DataIntent.preflight at passed
        split at passed
        · cases passed
        split at passed
        · cases passed
        split at passed
        · cases passed
        rename_i lower
        unfold DurableCommitProtocol.Intent.preflight at lower
        by_contra repeated
        have mapped : ¬ (intent.erase.rootWrites.map DurableCommitProtocol.RootWrite.cellId).Nodup := by
          simpa [DataIntent.erase, List.map_map, Function.comp_def] using repeated
        simp only [mapped, decide_false, Bool.not_false, if_true] at lower
        split at lower <;> cases lower
  obtain ⟨installed, nodup⟩ := accepted
  subst installed
  cases k with
  | system =>
      simp only [entriesOf, recordSlots, lastVal_cons, lastVal_cells_system, lastVal_cells_system,
        IntentRecord.ofIntent]
      simp [Image.append]
  | cell n =>
      have newIds : ∀ id : CellId, id ∈ (image.append intent).cellIds ↔
          id ∈ image.cellIds ∨ id ∈ intent.writes.map DataWrite.cellId := by
        intro id
        simp only [Image.cellIds, Image.append, List.mem_eraseDups, List.flatMap_append,
          List.mem_append, List.flatMap_singleton, IntentRecord.ofIntent]
        tauto
      simp only [entriesOf, recordSlots, lastVal_cons, IntentRecord.ofIntent, reduceCtorEq,
        if_false, Option.or_none]
      have enumerated : ∀ img : Image, img.cellIds.Nodup := fun _ => nodup_eraseDups _
      rw [lastVal_cellIds _ (enumerated _), lastVal_cellIds _ (enumerated _),
        lastVal_writes _ nodup]
      have roots : (DataSnapshot.install before intent).model.roots ⟨n⟩ =
          (DurableCommitProtocol.Snapshot.lookupPost ⟨n⟩ intent.erase.rootWrites).getD
            (before.model.roots ⟨n⟩) := rfl
      rw [roots]
      simp only [DataIntent.erase]
      cases found : DurableCommitProtocol.Snapshot.lookupPost (⟨n⟩ : CellId)
          (intent.writes.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId)) with
      | some post =>
          have member := lookupPost_member _ _ found
          simp [(newIds ⟨n⟩).mpr (Or.inr member)]
      | none =>
          have unwritten : (⟨n⟩ : CellId) ∉ intent.writes.map DataWrite.cellId := by
            intro member
            have := lookupPost_isSome _ _ member
            rw [found] at this
            cases this
          by_cases old : (⟨n⟩ : CellId) ∈ image.cellIds
          · simp [(newIds ⟨n⟩).mpr (Or.inl old), old]
          · have absent : (⟨n⟩ : CellId) ∉ (image.append intent).cellIds := by
              rw [newIds]; tauto
            simp [absent, old]

/-- A cell list read back by `Seed.lookup` gives each listed id its own bytes. -/
theorem seedLookup_map (ids : List CellId) (bytes : CellId → List UInt8) (id : CellId)
    (member : id ∈ ids) : Seed.lookup (ids.map fun i => (i, bytes i)) id = some (bytes id) := by
  induction ids with
  | nil => cases member
  | cons a rest ih =>
      simp only [List.map_cons, Seed.lookup]
      split
      next same => subst same; rfl
      next differs =>
        rcases List.mem_cons.mp member with rfl | inRest
        · exact absurd rfl differs
        · exact ih inRest

/-- Materializing the head and resuming from it with nothing to replay serves
the same entries. -/
theorem entriesOf_rebase {rootBytes : List UInt8 → Digest} (image : Image)
    (snapshot rebased : DataSnapshot rootBytes) (chain : Digest)
    (resumed : resume rootBytes image image.accepted.length (State.ofSnapshot image snapshot) =
      some rebased) :
    entriesOf image rebased chain = entriesOf image snapshot chain := by
  unfold resume at resumed
  split at resumed
  · simp only [List.drop_length, replay, Option.some.injEq] at resumed
    subst resumed
    unfold entriesOf
    congr 1
    apply List.map_congr_left
    intro id member
    rw [← (State.snapshot rootBytes _ _).coherent id, ← snapshot.coherent id]
    show (_, rootBytes ((Seed.lookup (State.ofSnapshot image snapshot).cells id).getD _)) = _
    simp only [State.ofSnapshot]
    rw [seedLookup_map _ _ _ member]
    rfl
  · cases resumed

/-! ## The loaded, resumed image -/

structure Loaded (rootBytes : List UInt8 → Digest) where
  image : Image
  baseHeight : Nat
  base : State
  snapshot : DataSnapshot rootBytes
  withinLog : baseHeight ≤ image.accepted.length
  resumed : resume rootBytes image baseHeight base = some snapshot
  /-- The log chain's start and its value after the last accepted record. -/
  logStart : Digest
  chain : Digest
  chainExact : chain = chainAfter logStart image.accepted
  /-- The world root, cached; `worldRoot_eq` below. -/
  roots : RootCache
  /-- The cache holds the served entries (`Loaded.worldRoot_eq`). -/
  rootsExact : RootsExact roots (entriesOf image snapshot chain)
  /-- The presence index of the accepted log, cached and advanced by one
  `admit` per append. It is a function of the log, never stored. -/
  index : PresenceIndex.Index
  indexExact : index = PresenceIndex.ofRecords image.accepted
  /-- The link index (forward links and backlinks) of the accepted log, cached
  beside the presence index and advanced the same way (K-DOC-INDEX). -/
  links : LinkIndex.Index
  linksExact : links = LinkIndex.ofRecords image.accepted
  /-- Every enumerable cell id (`Image.cellIds`), cached in that order with a
  membership set and advanced by one record per append (`SessionIndex.CellIds`):
  no `eraseDups` over the log on a request. -/
  ids : SessionIndex.CellIds
  idsExact : ids.Exact (SessionIndex.rawIds image)
  /-- Transaction id ↦ first accepted index (`SessionIndex.TxIndex`): no
  `findIdx?` over the log on a receipt lookup. -/
  txs : SessionIndex.TxIndex
  txsExact : txs.Exact image.accepted
  /-- The receipt root after each accepted record, oldest first: read from each
  entry's verified tag on open (`DurableLogTags.verifyTags_root`), pushed at
  every append (`Loaded.extend`). `none` where this image never saw the root
  (a log replayed from genesis in memory, `loadImage`): the receipt lookup
  evaluates that prefix instead. -/
  rootLog : Array (Option Digest)
  rootLogSize : rootLog.size = image.accepted.length
  /-- The log accumulator's peaks after the last accepted record
  (`DurableHistory`): checked against the tags on open, advanced by every
  `extend`. `none` for an in-memory image cut whose roots were never seen. -/
  frontier : Option (List (Nat × Digest))
  /-- The exact tag of the head entry when this image was read from (or
  appended to) the Store: its MAC was verified, so what it carries (the spent
  root after the head) is authenticated. `none` for in-memory images. -/
  headTag : Option (List UInt8)

def Loaded.height {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Nat :=
  loaded.image.accepted.length

/-- The served world root: read off the cache, not recomputed, while no two
cached keys share an index path; after an index collision (a collision of the
deployed hash) evaluated in full. -/
def Loaded.worldRoot {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Digest :=
  if loaded.rootsExact.injective then loaded.roots.root
  else deployedRoot (entriesOf loaded.image loaded.snapshot loaded.chain)

/-- **The served root is C1's root of the served entries**, either way. -/
theorem Loaded.worldRoot_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.worldRoot = deployedRoot (entriesOf loaded.image loaded.snapshot loaded.chain) := by
  unfold Loaded.worldRoot
  split
  next injective => exact loaded.rootsExact.root_eq injective
  next => rfl

/-- Reuse the already resumed snapshot when a controller reconstructs its
typed directory; this performs no second replay or cell update. -/
def Loaded.cells {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    List (CellId × List UInt8) :=
  loaded.image.cellIds.map fun cellId => (cellId, loaded.snapshot.canonicalBytes cellId)

/-- The enumeration read off the cache (`Loaded.ids`), in `Image.cellIds` order. -/
def Loaded.cellIds {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : List CellId :=
  loaded.ids.order.toList

/-- **Refinement**: the cached enumeration is the image's. -/
theorem Loaded.cellIds_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.cellIds = loaded.image.cellIds :=
  SessionIndex.CellIds.toList_eq loaded.idsExact

/-- `Loaded.cells` over the cached enumeration. -/
def Loaded.cellsCached {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    List (CellId × List UInt8) :=
  loaded.cellIds.map fun cellId => (cellId, loaded.snapshot.canonicalBytes cellId)

/-- **Refinement, compiled**: the host runs `cellsCached` wherever it runs
`cells`; the replacement is this theorem, not a trusted `implemented_by`. -/
@[csimp] theorem Loaded.cells_eq_cellsCached :
    @Loaded.cells = @Loaded.cellsCached := by
  funext rootBytes loaded
  unfold Loaded.cells Loaded.cellsCached
  rw [Loaded.cellIds_eq]

/-- A transaction id's first accepted index, read off the cache. -/
def Loaded.firstIndex {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (transactionId : TransactionId) : Option Nat :=
  loaded.txs[transactionId]?

/-- **Refinement**: the cached lookup is the log's `findIdx?`. -/
theorem Loaded.firstIndex_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (transactionId : TransactionId) :
    loaded.firstIndex transactionId =
      loaded.image.accepted.findIdx? (fun record => record.transactionId == transactionId) :=
  SessionIndex.TxIndex.lookup_eq loaded.txsExact transactionId

#assert_axioms Loaded.cellIds_eq
#assert_axioms Loaded.cells_eq_cellsCached
#assert_axioms Loaded.firstIndex_eq

/-- The log chain after appending this intent's record. -/
def Loaded.chainAfterIntent {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) : Digest :=
  chainStep loaded.chain (IntentRecord.ofIntent intent)

/-- Build a loaded image from an in-memory image by the genesis replay (the
seed as the height-0 checkpoint). History selection and the audit walk use
this; the request path never does. -/
def loadImage (rootBytes : List UInt8 → Digest) (logStart : Digest) (image : Image) :
    Except String (Loaded rootBytes) :=
  match resumed : resume rootBytes image 0 (State.ofSeed image.seed) with
  | none => .error "durable image journal does not replay through the canonical executor"
  | some snapshot =>
      let chain := chainAfter logStart image.accepted
      .ok ⟨image, 0, State.ofSeed image.seed, snapshot, Nat.zero_le _, resumed, logStart, chain,
        rfl, RootCache.ofEntries (entriesOf image snapshot chain),
        RootsExact.ofEntries (entriesOf image snapshot chain),
        PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
        SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
        SessionIndex.TxIndex.ofRecords image.accepted,
        SessionIndex.TxIndex.ofRecords_exact image.accepted,
        Array.replicate image.accepted.length none, Array.size_replicate,
        if image.accepted.isEmpty then some [] else none, none⟩

theorem loadImage_image {rootBytes : List UInt8 → Digest} {logStart : Digest} {image : Image}
    {loaded : Loaded rootBytes} (built : loadImage rootBytes logStart image = .ok loaded) :
    loaded.image = image := by
  unfold loadImage at built
  split at built
  · simp at built
  · cases built
    rfl

/-- The loaded genesis image of a seed. -/
def loadSeed (rootBytes : List UInt8 → Digest) (logStart : Digest) (seed : Seed) :
    Except String (Loaded rootBytes) :=
  loadImage rootBytes logStart ⟨seed, []⟩

/-- A whole image carried as portable evidence bytes (never the Store): exact
decode, then the genesis replay. -/
def loadBytes (rootBytes : List UInt8 → Digest) (logStart : Seed → Digest) (bytes : List UInt8) :
    Except String (Loaded rootBytes) :=
  match DurableReceiverCodec.decode bytes with
  | none => .error "noncanonical or unsupported durable image"
  | some image => loadImage rootBytes (logStart image.seed) image

private def decodeRecordsFrom : Nat → List Entry → Except String (List IntentRecord)
  | _, [] => .ok []
  | height, entry :: rest => do
      let some record := recordFrame.decode entry.record
        | throw s!"noncanonical durable log record at height {height}"
      return record :: (← decodeRecordsFrom (height + 1) rest)

/-- Every record the open decodes is what its stored bytes decode to. -/
private theorem decodeRecordsFrom_forall₂ :
    ∀ (height : Nat) (entries : List Entry) (records : List IntentRecord),
      decodeRecordsFrom height entries = .ok records →
        List.Forall₂ (fun bytes record => recordFrame.decode bytes = some record)
          (entries.map (·.record)) records
  | _, [], records, decoded => by
      simp only [decodeRecordsFrom, Except.ok.injEq] at decoded
      subst decoded; exact .nil
  | height, entry :: rest, records, decoded => by
      simp only [decodeRecordsFrom] at decoded
      cases found : recordFrame.decode entry.record with
      | none => simp [found] at decoded
      | some record =>
          simp only [found] at decoded
          cases tail : decodeRecordsFrom (height + 1) rest with
          | error message => simp [tail] at decoded
          | ok more =>
              simp [tail] at decoded
              subst decoded
              exact .cons found (decodeRecordsFrom_forall₂ (height + 1) rest more tail)

/-- Advance the accumulator frontier over stored entries `height + 1, …`
(each with the chain after it), checking that every tag carries the frontier
digest the accumulator reaches there. The tags' MACs are verified separately
(`verifyTags`); this binds what they carry to the records. -/
def walkFrontier : Nat → List (Nat × Digest) → List (Entry × Digest) →
    Except String (List (Nat × Digest))
  | _, frontier, [] => .ok frontier
  | height, frontier, (entry, chain) :: rest =>
      match trailerCarried entry.tag with
      | none => .error (DurableHistory.Refusal.message (.malformedTrailer (height + 1)))
      | some carried =>
          let next := DurableHistory.Frontier.push frontier
            (leafDigest (height + 1) entry.record chain carried.root)
          if carried.frontier ≠ frontierDigest (height + 1) next then
            .error s!"durable log tag at height {height + 1} carries a frontier the accumulator does not reach"
          else walkFrontier (height + 1) next rest

/-- The single open path, keeping the chain value after every stored record
(`chainPrefixes`, which the open computes to check the tags) for a caller that
cuts the image at a past height (`Loaded.prefixAt`). Every check refuses;
nothing reinterprets. -/
def loadChained (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String ((loaded : Loaded rootBytes) ×'
      {chains : List Digest // chains = chainPrefixes loaded.logStart loaded.image.accepted})) := do
  -- The Store's epoch, from its seed alone and before the head anchor or any
  -- other check: a Store of another epoch refuses by naming it.
  if let .ok (some seedBytes) := ← transport.peekSeed then
    if let some refusal := (SeedEpoch.ofBytes seedBytes).refusal then
      return .error s!"durable store refused: {refusal}"
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  match ← transport.read 1 true with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      let some seedBytes := stored.seed | return .error "durable seed missing"
      if let some refusal := (SeedEpoch.ofBytes seedBytes).refusal then
        return .error s!"durable store refused: {refusal}"
      let some seed := seedFrame.decode seedBytes | return .error "noncanonical durable seed"
      let ⟨records, decoded⟩ ← match found : decodeRecordsFrom 1 stored.entries with
        | .error message => return .error message
        | .ok records => pure (⟨records, decodeRecordsFrom_forall₂ 1 _ _ found⟩ :
            {records : List IntentRecord // List.Forall₂
              (fun bytes record => recordFrame.decode bytes = some record)
              (stored.entries.map (·.record)) records})
      let logStart := transport.logStart seed
      -- The chain over the STORED bytes (no re-encode), equal to the
      -- specification chain over the decoded records (`chainPrefixesStored_eq`).
      let chains := DurableLogTags.chainPrefixesStored logStart (stored.entries.map (·.record))
      have chainsEq : chains = chainPrefixes logStart records :=
        DurableLogTags.chainPrefixesStored_eq logStart _ _ decoded
      let headChain := chains.getLast?.getD logStart
      let (baseHeight, base, baseFrontier, baseSpent) ← match stored.checkpoint with
        | none => pure (0, State.ofSeed seed, [], DurableIndex.emptyDigest)
        | some checkpoint =>
            match openSealed key rootBytes checkpoint.bytes with
            | .error reason => return .error s!"checkpoint refused: {repr reason}"
            | .ok body =>
                if body.height ≠ checkpoint.height ∨ body.height > stored.head then
                  return .error "checkpoint height does not match the log"
                if body.chain ≠ chains.getD body.height ⟨0⟩ then
                  return .error "checkpoint does not match the log chain"
                pure (body.height, body.state, body.frontier, body.indexRoot)
      if stored.entries.length ≠ stored.head then
        return .error "durable log head does not match its entries"
      if let .error message := verifyTags key 0 chains (stored.entries.map (·.tag)) then
        return .error message
      -- The checkpoint's accumulator frontier and index root are the ones the
      -- (MAC-verified) tag of the entry at its height carries.
      if baseHeight > 0 then
        match stored.entries[baseHeight - 1]?.bind (trailerCarried ·.tag) with
        | some carried =>
            if carried.frontier ≠ frontierDigest baseHeight baseFrontier ∨
                carried.indexRoot ≠ baseSpent then
              return .error "checkpoint accumulator differs from its log entry's tag"
        | none => return .error "checkpoint height has no log entry"
      let frontier ← match walkFrontier baseHeight baseFrontier
          ((stored.entries.drop baseHeight).zip (chains.drop (baseHeight + 1))) with
        | .error message => return .error message
        | .ok frontier => pure frontier
      let image : Image := ⟨seed, records⟩
      -- Every entry's verified tag carries the receipt root after it
      -- (`DurableLogTags.verifyTags_carried`).
      let rootLog : Array (Option Digest) :=
        (stored.entries.map fun entry =>
          some ((trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩)).toArray
      if sized : rootLog.size ≠ image.accepted.length then
        return .error "durable log entries and records differ in number"
      else if within : baseHeight ≤ image.accepted.length then
        match resumed : resume rootBytes image baseHeight base with
        | none => return .error "durable log suffix does not replay through the canonical executor"
        | some snapshot =>
            let loaded : Loaded rootBytes :=
              ⟨image, baseHeight, base, snapshot, within, resumed, logStart, headChain,
              (by show chains.getLast?.getD logStart = _; rw [chainsEq]
                  exact DurableLogTags.chainPrefixes_getLast? logStart records),
              RootCache.ofEntries (entriesOf image snapshot headChain),
              RootsExact.ofEntries (entriesOf image snapshot headChain),
              PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
              SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
              SessionIndex.TxIndex.ofRecords image.accepted,
              SessionIndex.TxIndex.ofRecords_exact image.accepted,
              rootLog, Decidable.of_not_not sized, some frontier,
              stored.entries.getLast?.map (·.tag)⟩
            -- The head's stored root is the root this open just served: a
            -- rewritten head root refuses here, not at a later receipt.
            match rootLog.back? with
            | some (some stored) =>
                if stored ≠ loaded.worldRoot then
                  return .error "durable log head root differs from the replayed root"
            | _ => pure ()
            return .ok ⟨loaded, chains, chainsEq⟩
      else return .error "checkpoint beyond the log head"

/-- The open path (`loadChained` without the chain prefixes). -/
def load (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Loaded rootBytes)) := do
  return (← loadChained transport rootBytes).map (·.1)

inductive Confirmation where
  | installed
  | recoveredAfterUncertainResponse
  | replayed
  deriving Repr, DecidableEq

inductive Result (rootBytes : List UInt8 → Digest) where
  /-- The entry was read back, or the intent was already journaled. -/
  | confirmed (kind : Confirmation) (snapshot : DataSnapshot rootBytes)
  | rejected (reason : RejectReason)
  | contention
  | unavailable (detail : String)
  /-- An append was attempted; durable success could not be established. -/
  | uncertain (detail : String)

/-- `next` is the loaded image after exactly this intent, read back as the
entry this attempt appended. -/
structure Appended (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) where
  next : Loaded rootBytes
  image : next.image = loaded.image.append intent
  entry : Entry
  entryExact : entry.record = recordFrame.encode (IntentRecord.ofIntent intent)

/-- Only the read-back-equal branch constructs `exact`. -/
inductive DetailedResult (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) where
  | exact (kind : Confirmation) (appended : Appended rootBytes loaded intent)
  | ordinary (result : Result rootBytes)

def DetailedResult.toResult {rootBytes : List UInt8 → Digest}
    {loaded : Loaded rootBytes} {intent : DataIntent rootBytes} :
    DetailedResult rootBytes loaded intent → Result rootBytes
  | .exact kind appended => .confirmed kind appended.next.snapshot
  | .ordinary result => result

/-- The prepared successor: same checkpoint base, one more record, the chain
advanced by it, and the root cache advanced by its slot writes (one path each). -/
def Loaded.extend {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent) :
    Loaded rootBytes :=
  let record := IntentRecord.ofIntent intent
  let chain := chainStep loaded.chain record
  let roots := loaded.rootsExact.advance (recordSlots (loaded.image.accepted.length + 1) chain record)
    (entriesOf_step loaded.image loaded.snapshot ready.next intent loaded.chain chain ready.executed)
  -- The served root after this record (`Loaded.worldRoot` of the result), kept
  -- as its receipt root.
  let served := if roots.2.injective then roots.1.root
    else deployedRoot (entriesOf (loaded.image.append intent) ready.next chain)
  ⟨loaded.image.append intent, loaded.baseHeight, loaded.base, ready.next,
    by simp only [Image.append, List.length_append]; exact Nat.le_add_right_of_le loaded.withinLog,
    ready.resumed, loaded.logStart, chain,
    by show chainStep loaded.chain record = _
       rw [loaded.chainExact]; simp [chainAfter, Image.append, List.foldl_append, record],
    roots.1, roots.2,
    loaded.index.admit (loaded.image.accepted.length + 1) record,
    by rw [loaded.indexExact]
       exact (PresenceIndex.ofRecords_snoc loaded.image.accepted record).symm,
    loaded.links.admit (loaded.image.accepted.length + 1) record,
    by rw [loaded.linksExact]
       exact (LinkIndex.ofRecords_snoc loaded.image.accepted record).symm,
    loaded.ids.admit record,
    by unfold Image.append
       exact SessionIndex.CellIds.admit_exact loaded.idsExact record,
    loaded.txs.admitAt loaded.image.accepted.length record,
    by unfold Image.append
       exact SessionIndex.TxIndex.admitAt_exact loaded.txsExact record,
    loaded.rootLog.push (some served),
    by simp [Image.append, loaded.rootLogSize],
    loaded.frontier.map fun frontier => DurableHistory.Frontier.push frontier
      (leafDigest (loaded.image.accepted.length + 1) (recordFrame.encode record) chain served),
    none⟩

/-- **The root log keeps the served root**: after an append, the newest stored
receipt root is the root the extended image serves. -/
theorem Loaded.extend_rootLog_back {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent) :
    (loaded.extend ready).rootLog.back? = some (some (loaded.extend ready).worldRoot) := by
  simp only [Loaded.extend, Loaded.worldRoot, Array.back?_push]

/-- An append keeps every earlier stored root. -/
theorem Loaded.extend_rootLog_prefix {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent)
    (index : Nat) (earlier : index < loaded.image.accepted.length) :
    (loaded.extend ready).rootLog[index]? = loaded.rootLog[index]? := by
  simp only [Loaded.extend, Array.getElem?_push, loaded.rootLogSize]
  rw [if_neg (Nat.ne_of_lt earlier)]

#assert_axioms Loaded.extend_rootLog_back
#assert_axioms Loaded.extend_rootLog_prefix

/-- Materialize the head as a fresh base (no replayed suffix), as a cold
open of a checkpoint at the head would. The root cache carries over: the
rebased snapshot serves the same entries (`entriesOf_rebase`). -/
def Loaded.rebase {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Option (Loaded rootBytes) :=
  let state := State.ofSnapshot loaded.image loaded.snapshot
  let height := loaded.image.accepted.length
  match resumed : resume rootBytes loaded.image height state with
  | none => none
  | some snapshot =>
      have same := entriesOf_rebase loaded.image loaded.snapshot snapshot loaded.chain resumed
      some ⟨loaded.image, height, state, snapshot, Nat.le_refl _, resumed, loaded.logStart,
        loaded.chain, loaded.chainExact, loaded.roots,
        ⟨fun k => by rw [same]; exact loaded.rootsExact.agree k, loaded.rootsExact.injective,
          loaded.rootsExact.injectiveSound⟩,
        loaded.index, loaded.indexExact, loaded.links, loaded.linksExact,
        loaded.ids, loaded.idsExact, loaded.txs, loaded.txsExact,
        loaded.rootLog, loaded.rootLogSize, loaded.frontier, loaded.headTag⟩

def Loaded.rebaseD {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Loaded rootBytes :=
  loaded.rebase.getD loaded

theorem Loaded.rebaseD_image {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.rebaseD.image = loaded.image := by
  unfold rebaseD rebase
  dsimp only
  split <;> rfl

/-- **The index is the replay's index**: the cached index is the fold of the
whole log, and equally the fold of the checkpoint's prefix advanced by the
replayed suffix, which is the shape a resumed open computes. -/
theorem Loaded.index_from_replay {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.index = PresenceIndex.ofRecords loaded.image.accepted ∧
      loaded.index = (PresenceIndex.ofRecords (loaded.image.accepted.take loaded.baseHeight)).extend
        loaded.baseHeight (loaded.image.accepted.drop loaded.baseHeight) := by
  refine ⟨loaded.indexExact, ?_⟩
  have prefixLength : (loaded.image.accepted.take loaded.baseHeight).length = loaded.baseHeight := by
    rw [List.length_take]; exact Nat.min_eq_left loaded.withinLog
  rw [loaded.indexExact]
  conv => lhs; rw [← List.take_append_drop loaded.baseHeight loaded.image.accepted]
  rw [PresenceIndex.ofRecords_append, prefixLength]

/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.index_from_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverIO.Loaded.index_from_replay

/-- **The link index is the replay's link index**: the cached index is the fold
of the whole log, and equally the fold of the checkpoint's prefix advanced by
the replayed suffix, which is the shape a resumed open computes. -/
theorem Loaded.linkIndex_from_replay {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.links = LinkIndex.ofRecords loaded.image.accepted ∧
      loaded.links = (LinkIndex.ofRecords (loaded.image.accepted.take loaded.baseHeight)).extend
        loaded.baseHeight (loaded.image.accepted.drop loaded.baseHeight) := by
  refine ⟨loaded.linksExact, ?_⟩
  have prefixLength : (loaded.image.accepted.take loaded.baseHeight).length = loaded.baseHeight := by
    rw [List.length_take]; exact Nat.min_eq_left loaded.withinLog
  rw [loaded.linksExact]
  conv => lhs; rw [← List.take_append_drop loaded.baseHeight loaded.image.accepted]
  rw [LinkIndex.ofRecords_append, prefixLength]

/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.linkIndex_from_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverIO.Loaded.linkIndex_from_replay

/-! ## A past height (K-HISTORY-READ) -/

/-- The image cut at log height `height`: the seed and the first `height` records. -/
def Loaded.prefixImage {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (height : Nat) : Image :=
  ⟨loaded.image.seed, loaded.image.accepted.take height⟩

/-- A loaded image from its parts: the resumed snapshot, a full root cache and
every index built over the image. The physical checks (chain, tags, seal) are
the caller's; `chainExact` and `rootLogSize` carry what they established. -/
def Loaded.build {rootBytes : List UInt8 → Digest} (image : Image) (baseHeight : Nat)
    (base : State) (withinLog : baseHeight ≤ image.accepted.length) (logStart chain : Digest)
    (chainExact : chain = chainAfter logStart image.accepted)
    (rootLog : Array (Option Digest)) (rootLogSize : rootLog.size = image.accepted.length) :
    Except String {built : Loaded rootBytes // built.image = image ∧ built.logStart = logStart} :=
  match resumed : resume rootBytes image baseHeight base with
  | none => .error "durable image journal does not replay through the canonical executor"
  | some snapshot =>
      .ok ⟨⟨image, baseHeight, base, snapshot, withinLog, resumed, logStart, chain, chainExact,
        RootCache.ofEntries (entriesOf image snapshot chain),
        RootsExact.ofEntries (entriesOf image snapshot chain),
        PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
        SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
        SessionIndex.TxIndex.ofRecords image.accepted,
        SessionIndex.TxIndex.ofRecords_exact image.accepted,
        rootLog, rootLogSize, none, none⟩, rfl, rfl⟩

/-- **The loaded image cut at log height `height`**, from an open that kept its
chain prefixes (`loadChained`): the chain after `height` records is read off
the prefixes, the state is the checkpoint's resume when the checkpoint is at or
below `height` (otherwise the genesis fold of the cut), and the stored roots are
the verified tags' roots up to `height`. Nothing is re-read or re-hashed. -/
def Loaded.prefixAt {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) (height : Nat)
    (chains : List Digest) (chainsExact : chains = chainPrefixes loaded.logStart loaded.image.accepted) :
    Except String {cut : Loaded rootBytes //
      cut.image = ⟨loaded.image.seed, loaded.image.accepted.take height⟩ ∧
        cut.logStart = loaded.logStart} :=
  if within : height ≤ loaded.image.accepted.length then
    match found : chains[height]? with
    | none => .error "durable chain prefix unavailable at the requested height"
    | some chain =>
        have chainExact : chain = chainAfter loaded.logStart (loaded.image.accepted.take height) := by
          rw [chainsExact, DurableLogTags.chainPrefixes_getElem? _ _ _ within] at found
          exact (Option.some.inj found).symm
        have sized : (loaded.rootLog.extract 0 height).size =
            (loaded.image.accepted.take height).length := by
          simp [Array.size_extract, loaded.rootLogSize, List.length_take, Nat.min_eq_left within]
        if based : loaded.baseHeight ≤ height then
          Loaded.build ⟨loaded.image.seed, loaded.image.accepted.take height⟩ loaded.baseHeight
            loaded.base (by simpa [List.length_take, Nat.min_eq_left within] using based)
            loaded.logStart chain chainExact (loaded.rootLog.extract 0 height) sized
        else
          Loaded.build ⟨loaded.image.seed, loaded.image.accepted.take height⟩ 0
            (State.ofSeed loaded.image.seed) (Nat.zero_le _)
            loaded.logStart chain chainExact (loaded.rootLog.extract 0 height) sized
  else .error "durable log is shorter than the requested height"

/-- The state at log height `height`: the loaded checkpoint plus the records
after it up to `height` (D2's resume, on the cut image) when the checkpoint is
at or below `height`; otherwise the genesis fold of the prefix. The Store keeps
every record since the seed (the audit walk needs them), so the retention floor
is height 0. -/
def Loaded.atPrefix {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (height : Nat) : Option (DataSnapshot rootBytes) :=
  if loaded.baseHeight ≤ height then
    resume rootBytes (loaded.prefixImage height) loaded.baseHeight loaded.base
  else
    resume rootBytes (loaded.prefixImage height) 0 (State.ofSeed loaded.image.seed)

theorem Loaded.prefixImage_current {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.prefixImage loaded.height = loaded.image := by
  unfold prefixImage height
  rw [List.take_length]

/-- **At the current height the past read is the current state**: the same
snapshot every current read decodes. -/
theorem Loaded.atPrefix_current {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.atPrefix loaded.height = some loaded.snapshot := by
  unfold atPrefix
  rw [if_pos (show loaded.baseHeight ≤ loaded.height from loaded.withinLog), loaded.prefixImage_current]
  exact loaded.resumed

/-- **Below the checkpoint the past read is the genesis fold of the prefix.** -/
theorem Loaded.atPrefix_below {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {height : Nat} (below : height < loaded.baseHeight) :
    loaded.atPrefix height = (loaded.prefixImage height).restore rootBytes := by
  unfold atPrefix
  rw [if_neg (by omega)]
  exact resume_genesis rootBytes (loaded.prefixImage height)

/-- **At or above the checkpoint the past read is the checkpoint plus the
suffix fold** — and, for an honest checkpoint (`resume_sound`'s premises), the
genesis fold of the prefix. -/
theorem Loaded.atPrefix_from_checkpoint {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) {height : Nat} (above : loaded.baseHeight ≤ height)
    (atBase : DataSnapshot rootBytes)
    (seedValid : (loaded.image.seed.cells.map Prod.fst).Nodup)
    (stateValid : loaded.base.Admissible (loaded.prefixImage height))
    (prefixReplay : replay rootBytes (loaded.image.seed.snapshot rootBytes)
      ((loaded.image.accepted.take height).take loaded.baseHeight) = some atBase)
    (honest : loaded.base.snapshot rootBytes
      ((loaded.image.accepted.take height).take loaded.baseHeight) = atBase) :
    loaded.atPrefix height = (loaded.prefixImage height).restore rootBytes := by
  unfold atPrefix
  rw [if_pos above]
  exact resume_sound rootBytes (loaded.prefixImage height) loaded.baseHeight loaded.base atBase
    seedValid stateValid prefixReplay honest

/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_current
/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_below
/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_from_checkpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverIO.Loaded.atPrefix_from_checkpoint

/-- The checkpoint state's world-root entries are the served entries. -/
theorem stateEntries_ofSnapshot {rootBytes : List UInt8 → Digest} (image : Image)
    (snapshot : DataSnapshot rootBytes) (chain : Digest) :
    stateEntries rootBytes image.accepted.length chain (State.ofSnapshot image snapshot) =
      entriesOf image snapshot chain := by
  simp only [stateEntries, entriesOf, State.ofSnapshot, List.map_map]
  congr 1
  apply List.map_congr_left
  intro id _
  simp [snapshot.coherent id]

/-- **A checkpoint sealed from the cached root is the specification seal**,
byte for byte: the served root is the world root of the checkpoint body. -/
theorem sealCheckpoint_uses_cached_root {rootBytes : List UInt8 → Digest} (key : MacKey)
    (loaded : Loaded rootBytes) (frontier : List (Nat × Digest)) (indexRoot : Digest) :
    sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot =
      sealCheckpoint key rootBytes loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) := by
  apply sealAt_eq_sealCheckpoint
  rw [loaded.worldRoot_eq, DurableCheckpointCodec.worldRoot, stateEntries_ofSnapshot]

/-- The sealed root is `Kernel.WorldRoot`'s deployed root of the sealed body. -/
theorem cachedSeal_root {rootBytes : List UInt8 → Digest} (key : MacKey)
    (loaded : Loaded rootBytes) (frontier : List (Nat × Digest)) (indexRoot : Digest) :
    (sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot).root =
      DurableCheckpointCodec.worldRoot rootBytes
        (sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
          (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot).body := by
  rw [sealCheckpoint_uses_cached_root]
  rfl

/-- info: 'Minidregg.Compiler.DurableReceiverIO.sealCheckpoint_uses_cached_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealCheckpoint_uses_cached_root
/-- info: 'Minidregg.Compiler.DurableReceiverIO.Loaded.worldRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Loaded.worldRoot_eq
/-- info: 'Minidregg.Compiler.DurableReceiverIO.entriesOf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entriesOf_step
/-- info: 'Minidregg.Compiler.DurableReceiverIO.cachedSeal_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cachedSeal_root
/-- info: 'Minidregg.Compiler.DurableReceiverIO.RootsExact.root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootsExact.root_eq
/-- info: 'Minidregg.Compiler.DurableReceiverIO.entriesOf_rebase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entriesOf_rebase
/-- info: 'Minidregg.Compiler.DurableReceiverIO.RootCache.writeAllFresh?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootCache.writeAllFresh?_sound
/-- info: 'Minidregg.Compiler.DurableReceiverIO.RootCache.injectiveCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RootCache.injectiveCheck_sound
/-- info: 'Minidregg.Compiler.DurableReceiverIO.stateEntries_ofSnapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateEntries_ofSnapshot

/-- Seal and store a checkpoint of the head. A failed write loses nothing (the
log is complete); the caller then keeps its old base. -/
def storeCheckpoint (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (indexRoot : Digest) : IO Bool := do
  let .ok key ← transport.key | return false
  let some frontier := loaded.frontier | return false
  let sealed := sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
    (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot
  match ← transport.putCheckpoint loaded.image.accepted.length (checkpointFrame.encode sealed) with
  | .error _ => return false
  | .ok () => return true

/-- A checkpoint is due at every height that is a multiple of
`checkpointEvery`: a function of the height alone, so any process (a
long-lived session that re-derives its tip from the store, or a one-shot
receiver) seals at the same heights and never again in between.  A failed
seal loses nothing; the next multiple seals. -/
def checkpointDue {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) : Bool :=
  transport.checkpointEvery > 0 &&
    loaded.image.accepted.length % transport.checkpointEvery == 0

/-- After a stored checkpoint, rebase on it; otherwise keep the base. -/
def afterCheckpoint {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (stored : Bool) : Loaded rootBytes :=
  if stored then loaded.rebaseD else loaded

theorem afterCheckpoint_image {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (stored : Bool) : (afterCheckpoint loaded stored).image = loaded.image := by
  unfold afterCheckpoint
  split
  · exact Loaded.rebaseD_image _
  · rfl

/-- **The checkpoint differential** (operator diagnostic): rebuild the stored
log's state at `height` the way the live host does (from the seed, one
`extend` per record through the shared executor, a rebase at every due
checkpoint), then seal it twice: from the cached root, as `storeCheckpoint`
does, and from the root evaluated in full (`sealCheckpoint`). Returns both
encodings and the stored checkpoint's bytes when it sits at `height`. -/
def checkpointDifferential (transport : Transport) (rootBytes : List UInt8 → Digest) (height : Nat) :
    IO (Except String (List UInt8 × List UInt8 × Option (List UInt8))) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  match ← transport.read 1 true with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      let some seedBytes := stored.seed | return .error "durable seed missing"
      let some seed := seedFrame.decode seedBytes | return .error "noncanonical durable seed"
      let records ← match decodeRecordsFrom 1 stored.entries with
        | .error message => return .error message
        | .ok records => pure records
      if height > records.length then return .error "height beyond the log head"
      let initial ← match loadSeed rootBytes (transport.logStart seed) seed with
        | .error message => return .error message
        | .ok loaded => pure loaded
      let mut current := initial
      for record in records.take height do
        let some intent := record.bind? rootBytes
          | return .error "durable log record does not bind its roots"
        match prepare current.image current.baseHeight current.base current.snapshot
            current.withinLog current.resumed intent with
        | .inl ready =>
            let extended := current.extend ready
            current := afterCheckpoint extended (checkpointDue transport extended)
        | .inr _ => return .error "durable log does not replay through the canonical executor"
      let state := State.ofSnapshot current.image current.snapshot
      let frontier := current.frontier.getD []
      let indexRoot := if height = 0 then DurableIndex.emptyDigest else
        ((stored.entries[height - 1]?).bind (trailerCarried ·.tag)).map (·.indexRoot)
          |>.getD DurableIndex.emptyDigest
      let cached := checkpointFrame.encode
        (sealAt key height current.chain frontier indexRoot state current.worldRoot)
      let full := checkpointFrame.encode
        (sealCheckpoint key rootBytes height current.chain frontier indexRoot state)
      let atHeight := stored.checkpoint.bind fun checkpoint =>
        if checkpoint.height = height then some checkpoint.bytes else none
      return .ok (cached, full, atHeight)

/-- Read back the entry at `height`; exact equality with what this attempt
proposed is the only confirmation. -/
private def readBackEntry (transport : Transport) (height : Nat) :
    IO (Except String (Option Entry)) := do
  match ← transport.read height false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) => return .ok stored.entries.head?

/-- **The tail law on a new commit** (`Kernel.TailBound.gate`): the record
takes height `loaded.height + 1`, after the chain value `loaded.chain`, and is
judged on the loaded snapshot.  The receiving loop and the replay walk
(`NativeHostReplay.advance`) both call exactly this. -/
def Loaded.judge {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) : Except RejectReason Unit :=
  do
    transport.sourceGate loaded.snapshot intent
    match transport.systemCell with
    | none => .ok ()
    | some systemId =>
        Kernel.TailBound.gate systemId (loaded.height + 1) loaded.chain loaded.snapshot intent

/-- Adding a reservation gate cannot erase the existing tail-law obligation. -/
theorem Loaded.judge_tail {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) (systemId : CellId)
    (pinned : transport.systemCell = some systemId)
    (accepted : loaded.judge transport intent = .ok ()) :
    Kernel.TailBound.gate systemId (loaded.height + 1) loaded.chain loaded.snapshot intent = .ok () := by
  simp only [Loaded.judge, pinned] at accepted
  cases checked : transport.sourceGate loaded.snapshot intent with
  | error reason => simp [checked, bind, Except.bind] at accepted
  | ok value => cases value; simpa [checked, Except.bind] using accepted

/-- The index root after this image's head: carried by the head entry's tag,
whose MAC is verified for the head's height, chain and accumulator frontier
(`DurableHistory.Head.verify`). The empty log's is the empty map's. -/
def Loaded.headIndexRoot {rootBytes : List UInt8 → Digest} (transport : Transport) (key : MacKey)
    (loaded : Loaded rootBytes) : IO (Except String Digest) := do
  let height := loaded.image.accepted.length
  if height = 0 then return .ok DurableIndex.emptyDigest
  let some frontier := loaded.frontier
    | return .error "this opening carries no accumulator frontier (it was not read from the Store)"
  let tag ← match loaded.headTag with
    | some tag => pure tag
    | none =>
        match ← transport.read height false with
        | .ok (some stored) =>
            match stored.entries.head? with
            | some entry => pure entry.tag
            | none => return .error "durable head entry missing"
        | .ok none => return .error "durable store is not initialized"
        | .error message => return .error message
  match DurableHistory.Head.verify (DurableHistory.StoreIdentity.ofOpen key loaded.logStart) height tag
      loaded.chain frontier with
  | .ok head => return .ok head.indexRoot
  | .error refusal => return .error refusal.message

/-- Read index rows by prefix at or below `height`, in chunks (the Store answers
at most 65536 node keys per request); undecodable rows are dropped (untrusted
anyway: every use is verified against the root). -/
def readIndexRows (transport : Transport) (height : Nat) (paths : List (List Bool)) :
    IO (Except String (Std.HashMap (List Bool) DurableIndex.Row)) := do
  let mut seen : Std.HashSet (List UInt8) := {}
  let mut requested : Array (Nat × List UInt8) := #[]
  let mut byKey : Std.HashMap (List UInt8) (List Bool) := {}
  for path in paths do
    let rowKey := DurableIndex.rowKey path
    unless seen.contains rowKey do
      seen := seen.insert rowKey
      byKey := byKey.insert rowKey path
      requested := requested.push (DurableIndex.indexSpace, rowKey)
  let mut found : Std.HashMap (List Bool) DurableIndex.Row := {}
  for chunk in requested.toList.toChunks 60000 do
    match ← transport.history ⟨height, [], chunk⟩ with
    | .error message => return .error message
    | .ok read =>
        found := read.nodes.foldl (init := found) fun map node =>
          match node.2.2, byKey.get? node.2.1 with
          | some (_, value), some path =>
              match DurableIndex.rowStream.toLawful.decode value with
              | some row => map.insert path row
              | none => map
          | _, _ => map
  return .ok found

/-- The index rows on the paths of `keys` and beside them (each prefix's
sibling, which a delete's collapse reads), at or below `height`, down to `depth`
bits (520: every prefix). Untrusted: every opening built from them is verified
against the authenticated index root, so a path cut short opens to nothing and
refuses. -/
def indexRows (transport : Transport) (height : Nat) (keys : List DurableIndex.IndexKey)
    (depth : Nat := 520) : IO (Except String (List Bool → Option DurableIndex.Row)) := do
  match ← readIndexRows transport height (keys.flatMap fun k => DurableIndex.readPrefixes k depth) with
  | .error message => return .error message
  | .ok rows => return .ok fun path => rows.get? path

/-- Use the index rows of `keys`: first down to 48 bits (the family byte, then a
compressed trie over far fewer than 2^40 keys of a family rarely reaches
deeper), and when what they give does not verify, every prefix. Every answer is
verified by `use`. -/
def withIndexRows {α : Type} (transport : Transport) (height : Nat) (keys : List DurableIndex.IndexKey)
    (use : (List Bool → Option DurableIndex.Row) → Except String α) : IO (Except String α) := do
  match ← indexRows transport height keys 48 with
  | .error message => return .error message
  | .ok rows =>
      match use rows with
      | .ok value => return .ok value
      | .error _ =>
          match ← indexRows transport height keys with
          | .error message => return .error message
          | .ok rows => return use rows

/-- The most subtree rows a prefix read takes before it refuses by name. -/
def subtreeRowsMax : Nat := 1 <<< 16

/-- The subtrees below `frontier`, level by level: the children of every branch
row at this level (one Store request), then theirs; `taken` counts the subtree
rows read so far, refused by name past `subtreeRowsMax`. `levels` bounds the
depth: what is left of the 520-bit key path below the prefixes. -/
def readSubtrees (transport : Transport) (height : Nat) :
    Nat → List (List Bool) → Std.HashMap (List Bool) DurableIndex.Row → Nat →
      IO (Except String (Std.HashMap (List Bool) DurableIndex.Row))
  | 0, _, found, _ => return .ok found
  | levels + 1, frontier, found, taken => do
      let children := frontier.flatMap fun here =>
        match found.get? here with
        | some (.branch left right) =>
            (if left = DurableIndex.emptyDigest then [] else [here ++ [false]]) ++
              (if right = DurableIndex.emptyDigest then [] else [here ++ [true]])
        | _ => []
      if children.isEmpty then return .ok found
      if taken + children.length > subtreeRowsMax then
        return .error s!"index subtree over {subtreeRowsMax} rows: refused"
      match ← readIndexRows transport height children with
      | .error message => return .error message
      | .ok level =>
          readSubtrees transport height levels children
            (level.fold (init := found) fun map path row => map.insert path row) (taken + children.length)

/-- The subtree read reaches the Store only through `history`: two transports
that read alike read the same subtrees. -/
theorem readSubtrees_history {t t' : Transport} (same : t.history = t'.history) :
    readSubtrees t = readSubtrees t' := by
  have rows : readIndexRows t = readIndexRows t' := by
    funext height paths; unfold readIndexRows; rw [same]
  funext height levels
  induction levels with
  | zero => rfl
  | succ levels ih =>
      funext frontier found taken
      simp only [readSubtrees, rows, ih]

/-- The rows of `keys` (paths down to `depth`) and of `prefixes`: every prefix of
each one's path with its sibling, then the subtree BELOW it, level by level
(`readSubtrees`: one Store request per level). More than `subtreeRowsMax` subtree
rows is refused by name. Untrusted: reveals built from them are verified
against the root. -/
def indexRowsFor (transport : Transport) (height : Nat) (keys : List DurableIndex.IndexKey)
    (prefixes : List (List Bool)) (depth : Nat := 520) :
    IO (Except String (List Bool → Option DurableIndex.Row)) := do
  let paths := keys.flatMap (fun k => DurableIndex.readPrefixes k depth) ++
    prefixes.flatMap fun p => DurableIndex.pathPrefixes p p.length
  let pathRows ← match ← readIndexRows transport height paths with
    | .error message => return .error message
    | .ok rows => pure rows
  -- A key path is 520 bits: below the shortest prefix there are at most 520 minus its length levels.
  let levels := 520 - (prefixes.map List.length).foldl min 520
  match ← readSubtrees transport height levels prefixes pathRows 0 with
  | .error message => return .error message
  | .ok rows => return .ok fun path => rows.get? path

/-- **The index rows of a batch of records**, applied in order from `root` (the
index after height `readHeight`, the record at position `i` taking height
`readHeight + 1 + i`): each record's `IndexRows.apply` over the Store's rows at
`readHeight` with every earlier record's written rows laid over them. The rows
are read in two passes: the reads of every record (its family-0/1 and payer keys,
the family-4 prefix of each cell it writes, with the subtree below), then the
paths of the keys the changes may touch (`IndexRows.plannedKeys`, planned from
the verified start members). Point paths are read down to 48 bits first (the
family byte, then a compressed trie over far fewer than 2^40 keys of a family
rarely reaches deeper), and every prefix when that does not verify. -/
def applyRecords (transport : Transport) (readHeight : Nat) (root : Digest)
    (records : List IntentRecord) :
    IO (Except String (List (Digest × List (List Bool × DurableIndex.Row)))) := do
  let reads := records.map DurableIndex.IndexRows.reads
  let points := reads.flatMap (·.1)
  let prefixes := (reads.flatMap (·.2)).dedup
  let attempt (depth : Nat) : IO (Except String (List (Digest × List (List Bool × DurableIndex.Row)))) := do
    let first ← match ← indexRowsFor transport readHeight points prefixes depth with
      | .error message => return .error message
      | .ok rows => pure rows
    let mut startMembers : List (List Bool × List (DurableIndex.IndexKey × List UInt8)) := []
    for p in prefixes do
      match DurableIndex.revealRows first root p with
      | .error message => return .error s!"index rows at height {readHeight}: {message}"
      | .ok revealed => startMembers := (p, revealed.members) :: startMembers
    let members := fun p => ((startMembers.find? (·.1 = p)).map (·.2)).getD []
    let planned := DurableIndex.IndexRows.plannedKeys readHeight records members
    let second ← match ← indexRows transport readHeight planned depth with
      | .error message => return .error message
      | .ok rows => pure rows
    let stored := fun path => (first path).or (second path)
    let mut written : Std.HashMap (List Bool) DurableIndex.Row := {}
    let mut current := root
    let mut results : Array (Digest × List (List Bool × DurableIndex.Row)) := #[]
    for (record, height) in records.zipIdx (readHeight + 1) do
      let overlaid := written
      let rows := fun path => (overlaid.get? path).or (stored path)
      match DurableIndex.IndexRows.apply rows current height record with
      | .error message => return .error s!"durable log record at height {height}: {message}"
      | .ok (next, writes) =>
          written := writes.foldl (fun map row => map.insert row.1 row.2) written
          current := next
          results := results.push (next, writes)
    return .ok results.toList
  match ← attempt 48 with
  | .ok results => return .ok results
  | .error _ => attempt 520

/-- The node rows an append writes: the accumulator nodes it completes
(space 1) and the index rows its changes write (space 3). -/
def appendNodes (accumulator : List ((Nat × Nat) × Digest))
    (index : List (List Bool × DurableIndex.Row)) : List NodeWrite :=
  accumulator.map (fun node => ⟨DurableIndex.accumulatorSpace,
      DurableHistory.nodeKey node.1.1 node.1.2, Tower256ConcreteBackend.digestStream.encode node.2⟩) ++
    index.map fun row => ⟨DurableIndex.indexSpace, DurableIndex.rowKey row.1,
      DurableIndex.rowStream.encode row.2⟩

/-- What an append writes, prepared from the loaded image and the Store's
reads (the head tag's index root, the index rows): the entry (record and v4
trailer), the node rows, the extended image and the index root after it. -/
structure PreparedAppend {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) where
  entry : Entry
  entryExact : entry.record = recordFrame.encode (IntentRecord.ofIntent intent)
  nodes : List NodeWrite
  extended : Loaded rootBytes
  extendedImage : extended.image = loaded.image.append intent
  indexAfter : Digest

def prepareAppend (transport : Transport) {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent)
    (key : MacKey) : IO (Except String (PreparedAppend loaded intent)) := do
  let height := loaded.image.accepted.length + 1
  let recordBytes := recordFrame.encode (IntentRecord.ofIntent intent)
  let chain := loaded.chainAfterIntent intent
  let some frontier := loaded.frontier
    | return .error "this opening carries no accumulator frontier (it was not read from the Store)"
  -- The index after the head (MAC-verified), then this record's rows (IndexRows.changes) applied.
  let indexBefore ← match ← loaded.headIndexRoot transport key with
    | .ok root => pure root
    | .error message => return .error message
  let (indexAfter, indexWrites) ←
    match ← applyRecords transport loaded.image.accepted.length indexBefore [IntentRecord.ofIntent intent] with
    | .ok [result] => pure result
    | .ok _ => return .error "the index applied a different number of records than it was given"
    | .error message => return .error message
  -- The tag keeps this record's receipt root, the root the extended image
  -- serves, the accumulator frontier after it and the index root after it.
  let extended := loaded.extend ready
  let leaf := leafDigest height recordBytes chain extended.worldRoot
  let frontierAfter := DurableHistory.Frontier.push frontier leaf
  let nodes := appendNodes (DurableHistory.completedNodes frontier height leaf) indexWrites
  let entry : Entry := ⟨recordBytes, trailer key height
    ⟨extended.worldRoot, chain, frontierDigest height frontierAfter, indexAfter⟩⟩
  return .ok ⟨entry, rfl, nodes, extended, rfl, indexAfter⟩

/-- What the receiving loop does after the append's observation: confirm by
exact readback (seal a due checkpoint), or report contention. -/
def publishAfter (transport : Transport) (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) (prepared : PreparedAppend loaded intent)
    (observation : CasObservation) : IO (Bool × DetailedResult rootBytes loaded intent) := do
  let height := loaded.image.accepted.length + 1
  let entry := prepared.entry
  let extended := prepared.extended
  let indexAfter := prepared.indexAfter
  let confirm := fun (installed : Bool) (kind : Confirmation) => do
    match ← readBackEntry transport height with
    | .error message =>
        return (false, DetailedResult.ordinary (.uncertain s!"append attempted; readback unavailable: {message}"))
    | .ok none =>
        return (false, .ordinary (.uncertain "append attempted; entry absent on readback"))
    | .ok (some stored) =>
        if stored = entry then
          let tagged := { extended with headTag := some entry.tag }
          let checkpointStored ←
            if checkpointDue transport tagged then storeCheckpoint transport rootBytes tagged indexAfter
            else pure false
          return (installed, .exact kind
            ⟨afterCheckpoint tagged checkpointStored,
              (afterCheckpoint_image tagged checkpointStored).trans prepared.extendedImage, entry,
              prepared.entryExact⟩)
        else return (false, .ordinary .contention)
  match observation with
  | .installed => confirm true .installed
  | .alreadyPresent => confirm false .installed
  | .conflict => return (false, .ordinary .contention)
  | .uncertain _ => confirm false .recoveredAfterUncertainResponse

/-- Append a prepared entry at `loaded.height + 1` (the receiving loop's only
Store write), then `publishAfter`. -/
def publish (transport : Transport) (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) (prepared : PreparedAppend loaded intent) :
    IO (Bool × DetailedResult rootBytes loaded intent) :=
  transport.append (loaded.image.accepted.length + 1) prepared.entry prepared.nodes >>=
    publishAfter transport rootBytes loaded intent prepared

/-- A conflicting append is contention, and nothing else is read or written. -/
theorem publishAfter_conflict (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) (prepared : PreparedAppend loaded intent) :
    publishAfter transport rootBytes loaded intent prepared .conflict =
      pure (false, .ordinary .contention) := rfl

/-- Publish against the exact image on which the controller admitted the
operation: append entry `h + 1` only while the head is `h`. One attempt, no
rebase; a lost response never becomes a refusal. The Bool is whether this
call installed the entry. -/
def receiveLoadedDetailedWithFresh (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (Bool × DetailedResult rootBytes loaded intent) := do
  match prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot loaded.withinLog
      loaded.resumed intent with
  | .inr (.replayed _) => return (false, .ordinary (.confirmed .replayed loaded.snapshot))
  | .inr (.rejected reason) => return (false, .ordinary (.rejected reason))
  | .inr _ => return (false, .ordinary (.unavailable "unexpected complete-schedule outcome"))
  | .inl ready =>
      if let .error reason := loaded.judge transport intent then
        return (false, .ordinary (.rejected reason))
      let .ok key ← transport.key
        | return (false, .ordinary (.unavailable "checkpoint MAC key unavailable"))
      match ← prepareAppend transport loaded ready key with
      | .error message => return (false, .ordinary (.unavailable message))
      | .ok prepared => publish transport rootBytes loaded intent prepared

def receiveLoadedDetailed (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (DetailedResult rootBytes loaded intent) := do
  return (← receiveLoadedDetailedWithFresh transport rootBytes loaded intent).2

def receiveLoaded (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (Result rootBytes) := do
  return (← receiveLoadedDetailed transport rootBytes loaded intent).toResult

/-- Whether the store's head is still exactly this entry at this height — a
point-in-time check, not a lease. -/
def tipIs (transport : Transport) (height : Nat) (entry : Entry) : IO (Except String Bool) := do
  match ← transport.read height false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) => return .ok (stored.head = height && stored.entries == [entry])

/-- Bounded contention retry for an internal intent whose admission does not
depend on a journal-wide clock. Each retry reloads. -/
def receive (transport : Transport) (rootBytes : List UInt8 → Digest)
    (intent : DataIntent rootBytes) : Nat → IO (Result rootBytes)
  | 0 => pure .contention
  | attempts + 1 => do
      match ← load transport rootBytes with
      | .error message => return .unavailable message
      | .ok loaded =>
          match ← receiveLoaded transport rootBytes loaded intent with
          | .contention => receive transport rootBytes intent attempts
          | result => return result

/-- Rebasing at the head keeps the image and the log start. -/
theorem Loaded.rebase_image {rootBytes : List UInt8 → Digest} {loaded rebased : Loaded rootBytes}
    (done : loaded.rebase = some rebased) :
    rebased.image = loaded.image ∧ rebased.logStart = loaded.logStart := by
  unfold Loaded.rebase at done
  dsimp only at done
  split at done
  · cases done
  · cases done
    exact ⟨rfl, rfl⟩

/-- Replay stored records onto a loaded image through the shared executor, one
`Loaded.extend` each. The result's image is the given one followed by exactly
these records. -/
def Loaded.replay {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    (records : List IntentRecord) →
    Except String {next : Loaded rootBytes //
      next.image = ⟨loaded.image.seed, loaded.image.accepted ++ records⟩ ∧
        next.logStart = loaded.logStart}
  | [] => .ok ⟨loaded, by rw [List.append_nil], rfl⟩
  | record :: rest =>
      match bound : record.bind? rootBytes with
      | none => .error "durable log record does not bind its roots"
      | some intent =>
          match prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot
              loaded.withinLog loaded.resumed intent with
          | .inl ready =>
              match (loaded.extend ready).replay rest with
              | .error message => .error message
              | .ok ⟨next, imaged, started⟩ =>
                  .ok ⟨next, by
                    rw [imaged]
                    show (⟨loaded.image.seed, (loaded.image.accepted ++
                      [IntentRecord.ofIntent intent]) ++ rest⟩ : Image) = _
                    rw [IntentRecord.bind_exact bound, List.append_assoc, List.singleton_append],
                    started⟩
          | .inr _ => .error "durable log suffix does not replay through the canonical executor"

/-- Extend a live loaded image by entries a concurrent writer appended after
it: the chain must continue, every new entry's tag must verify, and every new
record must be accepted by the shared executor in order. The result is the
given image followed by exactly the new records (by construction, so a
verified history over the old image extends without comparing prefixes:
`NativeHostReplay.extendVerifiedAppended`). -/
def extendFrom (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) : IO (Except String {next : Loaded rootBytes //
      next.image.seed = loaded.image.seed ∧
        next.image.accepted = loaded.image.accepted ++
          next.image.accepted.drop loaded.image.accepted.length ∧
        next.logStart = loaded.logStart}) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let height := loaded.image.accepted.length
  match ← transport.read (height + 1) false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      if stored.head = height then return .ok ⟨loaded, rfl, by simp, rfl⟩
      if stored.head < height then return .error "durable log shrank beneath the session"
      let records ← match decodeRecordsFrom (height + 1) stored.entries with
        | .error message => return .error message
        | .ok records => pure records
      let chain := chainAfter loaded.chain records
      if height + stored.entries.length ≠ stored.head then
        return .error "durable log head does not match its entries"
      if let .error message := verifyTags key height (chainPrefixes loaded.chain records)
          (stored.entries.map (·.tag)) then
        return .error message
      -- Every new tag carries the frontier the accumulator reaches at its height.
      if let some frontier := loaded.frontier then
        if let .error message := walkFrontier height frontier
            (stored.entries.zip ((chainPrefixes loaded.chain records).drop 1)) then
          return .error message
      match loaded.replay records with
      | .error message => return .error message
      | .ok ⟨current, imaged, started⟩ =>
        have extended : current.image.seed = loaded.image.seed ∧
            current.image.accepted = loaded.image.accepted ++
              current.image.accepted.drop loaded.image.accepted.length ∧
            current.logStart = loaded.logStart := by
          rw [imaged]
          exact ⟨rfl, by simp, started⟩
        if current.chain ≠ chain then return .error "durable log chain mismatch"
        -- Every new entry's stored root is the root its replay served.
        let replayed := (current.rootLog.extract height current.rootLog.size).toList
        if replayed ≠ stored.entries.map (fun entry =>
            some ((trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩)) then
          return .error "durable log root tag differs from the replayed root"
        let current := { current with headTag := stored.entries.getLast?.map (·.tag) }
        if current.image.accepted.length ≥ current.baseHeight + 2 * max 1 transport.checkpointEvery then
          match rebased : current.rebase with
          | some next =>
              have kept := Loaded.rebase_image rebased
              return .ok ⟨next, by rw [kept.1]; exact extended.1,
                by rw [kept.1]; exact extended.2.1, by rw [kept.2]; exact extended.2.2⟩
          | none => return .error "rebase at the head does not resume through the canonical executor"
        return .ok ⟨current, extended⟩

/-- Explicit bootstrap, separate from receipt acceptance. An existing different
seed is never replaced; initialization is confirmed by a full `load`. -/
def bootstrap (transport : Transport) (rootBytes : List UInt8 → Digest)
    (seed : Seed) : IO (Except String Unit) := do
  if (loadSeed rootBytes (transport.logStart seed) seed).toOption.isNone then
    return .error "invalid bootstrap seed"
  let observation ← transport.initializeSeed (seedFrame.encode seed)
  match ← load transport rootBytes with
  | .ok loaded =>
      if loaded.image.accepted.isEmpty ∧ seedFrame.encode loaded.image.seed = seedFrame.encode seed then
        return .ok ()
      else return .error s!"bootstrap did not install exact seed: {repr observation}"
  | .error message => return .error s!"bootstrap outcome uncertain: {message}"

/-- Write an accepted image into an EMPTY Store through `transport`: its seed
bootstrapped, then each record bound (`IntentRecord.bind?`) and appended in order
through the one receive path (`receiveLoadedDetailed`), each read back exactly, the
opening advanced by the appended entry (no re-open per record). The result is the
Store's opening at the image's height, so a history `Reader` of a portable image
(a foreign accepted prefix) is a Reader of a real Store, never an in-memory one.
Refuses, naming the height, a record that does not bind, does not re-encode to
itself, or is not appended exactly; and a Store whose final image is not `image`. -/
def writeImage (transport : Transport) (rootBytes : List UInt8 → Digest) (image : Image) :
    IO (Except String (Loaded rootBytes)) := do
  match ← bootstrap transport rootBytes image.seed with
  | .error detail => return .error s!"scratch Store: {detail}"
  | .ok () => pure ()
  let genesis ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => return .error s!"scratch Store: genesis open: {detail}"
  let rec go (height : Nat) (loaded : Loaded rootBytes) :
      List IntentRecord → IO (Except String (Loaded rootBytes))
    | [] => return .ok loaded
    | record :: rest => do
        let some intent := record.bind? rootBytes
          | return .error s!"scratch Store: record {height + 1} does not bind its roots"
        if recordFrame.encode (IntentRecord.ofIntent intent) != recordFrame.encode record then
          return .error s!"scratch Store: record {height + 1} does not re-encode to itself"
        match ← receiveLoadedDetailed transport rootBytes loaded intent with
        | .exact _ appended => go (height + 1) appended.next rest
        | .ordinary _ => return .error s!"scratch Store: record {height + 1} was not appended exactly"
  match ← go 0 genesis image.accepted with
  | .error detail => return .error detail
  | .ok loaded =>
      if (loaded.image.accepted.map fun record => recordFrame.encode record) =
          image.accepted.map (fun record => recordFrame.encode record) then
        return .ok loaded
      else return .error "scratch Store: the written image is not the image"

end Minidregg.Compiler.DurableReceiverIO
