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
  engine (`Loaded.prepare`, which IS `DurableCheckpoint.prepare` at its snapshot:
  `Loaded.prepare_eq`), append one entry, read that one entry back. Every `checkpointEvery` records the receiver seals a checkpoint of the
  new head and rebases its in-memory state on it.
* A store holding the retired whole-image record refuses (the helper reports
  it); there is no migration: re-genesis.

The physical assumptions are SQLite transaction integrity, honest byte
transport and the OS durability floor; no Lean theorem proves those systems.
The MAC key file's custody is the operator's (`DurableCheckpointCodec`).
-/
module

public import Compiler.DurableCheckpointCodec
public import Compiler.NativeCoprocess
public import Compiler.DurableLogTags
public import Compiler.DurableHistory
public import Compiler.DurableIndex
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Kernel.PresenceIndex
public import Kernel.TailBound
public import Kernel.LinkIndex
public import Kernel.SessionIndex
public import Kernel.DeployedRepresentsCheck
public import Kernel.DeployedCharge
public import Kernel.TurnLog
public import Kernel.DurableEngine
public import Kernel.DurableEngineSuffix
public import Compiler.WorldCompact

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

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

/-- `runNative` with the call's files as blobs (`mem:NAME` arguments,
`NativeCoprocess.outputMemory`): no temporary directory, no file round trip. -/
def runNativeMemory (config : NativeConfig) (arguments : Array String)
    (inputs : List (String × ByteArray)) : IO (IO.Process.Output × List (String × ByteArray)) :=
  NativeCoprocess.outputMemory config.binary.toString
    (if config.anchorIdentity.isEmpty then arguments
      else #["--anchor-identity", config.anchorIdentity] ++ arguments) inputs

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

/-- A length-prefixed blob, sliced straight out of the read buffer into a list
(`Tower256ConcreteBackend.sliceOnto`: one cell per octet, no intermediate copy). -/
private def blobAt (bytes : ByteArray) (position : Nat) : Option (List UInt8 × Nat) := do
  let length ← u64At bytes position
  let start := position + 8
  if fits : start + length ≤ bytes.size then
    some (Minidregg.Compiler.Tower256ConcreteBackend.sliceOnto bytes start length fits [], start + length)
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
    let (output, written) ← runNativeMemory config #["durable-read", config.root.toString,
      toString fromHeight, if withBase then "1" else "0", "mem:read"] []
    if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
      match (written.lookup "read").bind (parseStored fromHeight withBase) with
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
    let arguments := match crashAt with
      | none => #["durable-append", config.root.toString, toString height,
          "mem:record", "mem:tag", "mem:nodes"]
      | some phase => #["durable-append-crash", config.root.toString, toString height,
          "mem:record", "mem:tag", "mem:nodes", phase]
    let (output, _) ← runNativeMemory config arguments
      [("record", entry.record.toByteArray), ("tag", entry.tag.toByteArray),
        ("nodes", (encodeNodes nodes).toByteArray)]
    return parseCasOutput output
  catch error => pure (.uncertain s!"native append unavailable: {error}")

def NativeConfig.putCheckpoint (config : NativeConfig) (height : Nat) (bytes : List UInt8) :
    IO (Except String Unit) :=
  try
    let (output, _) ← runNativeMemory config #["durable-checkpoint", config.root.toString,
      toString height, "mem:checkpoint"] [("checkpoint", bytes.toByteArray)]
    if output.exitCode == 0 && output.stderr == "" then return .ok ()
    else return .error s!"native checkpoint write failed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native checkpoint unavailable: {error}")

def NativeConfig.initialize (config : NativeConfig) (seedBytes : List UInt8) : IO CasObservation :=
  try
    let (output, _) ← runNativeMemory config #["durable-init", config.root.toString, "mem:seed"]
      [("seed", seedBytes.toByteArray)]
    return parseCasOutput output
  catch error => pure (.uncertain s!"native initialize unavailable: {error}")

/-- The MAC keys this process has read, by file: a Store's key is written once at bootstrap,
so it is read once per process, not on every Store call. -/
initialize macKeys : IO.Ref (List (System.FilePath × MacKey)) ← IO.mkRef []

/-- The key file must hold exactly 32 bytes. Its 0600 mode is checked by the
bootstrap that created it and by the operator; Lean reads, never writes it. -/
def NativeConfig.readKey (config : NativeConfig) : IO (Except String MacKey) :=
  try
    if let some key := (← macKeys.get).lookup config.key then return .ok key
    let bytes := (← IO.FS.readBinFile config.key).toList
    match MacKey.ofBytes? bytes with
    | some key =>
        macKeys.modify ((config.key, key) :: ·)
        return .ok key
    | none => return .error "checkpoint MAC key must be exactly 32 bytes"
  catch error => pure (.error s!"checkpoint MAC key unavailable: {error}")

/-- The seed bytes alone, without the head anchor (read-only; the Store
installs a seed once and never replaces it). -/
def NativeConfig.peekSeed (config : NativeConfig) : IO (Except String (Option (List UInt8))) :=
  try
    do
      let (output, written) ← runNativeMemory config #["durable-seed", config.root.toString,
        "mem:seed"] []
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        match written.lookup "seed" with
        | some bytes => return .ok (some bytes.toList)
        | none => return .error "native durable seed read malformed"
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
    do
      let (output, written) ← runNativeMemory config #["durable-history", config.root.toString,
        "mem:request", "mem:history"] [("request", (encodeHistoryRequest request).toByteArray)]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        match (written.lookup "history").bind parseHistory with
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
    do
      let (output, written) ← runNativeMemory config #["durable-read", config.root.toString, "1", "2",
        "mem:read"] []
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        let bytes := (written.lookup "read").getD ByteArray.empty
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
    do
      let (output, written) ← runNativeMemory config #["durable-checkpoint-at", config.root.toString,
        toString height, "mem:checkpoint"] []
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        let bytes := (written.lookup "checkpoint").getD ByteArray.empty
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
        show ByteArray.beq _ _ = true ↔ _
        simp [ByteArray.beq]
  rw [byteArrayBEq]
  constructor
  · intro exact
    have lists := congrArg (fun bytes : ByteArray => bytes.data.toList) exact
    simpa using lists
  · intro exact
    subst right
    rfl

/-- Images compare by their canonical encoding (the ten-lane charge is a
function, so there is no structural equality to derive), after object identity:
a session comparing its image with the one a submit started from holds the
same object, and the encoding of the whole history is never built for that. -/
instance : DecidableEq Image := fun left right =>
  withPtrEqDecEq left right fun _ =>
    decidable_of_iff ((DurableReceiverCodec.encode left).toByteArray ==
        (DurableReceiverCodec.encode right).toByteArray)
      ((byteArray_beq_exact _ _).trans
        ⟨fun same => DurableReceiverCodec.encode_injective same, congrArg _⟩)

/-! ## The world root, kept

The cache and its exactness live in `Kernel.WorldRootCache` (`RootCache`,
`RootsExact`): a compressed trie, exact for the served entries with no
injectivity flag and no fallback rebuild. -/

open Minidregg.Kernel.WorldRoot (Key deployedRoot)
open Minidregg.Kernel.WorldRootCache

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

/-- An accepted execution installs the intent, whose writes name distinct cells. -/
theorem execute_accepted_install {rootBytes : List UInt8 → Digest} {before next : DataSnapshot rootBytes}
    {intent : DataIntent rootBytes}
    (executed : DurableDataIntent.execute .complete before intent = .accepted next) :
    next = DataSnapshot.install before intent ∧ (intent.writes.map DataWrite.cellId).Nodup := by
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

/-- **The served entries after an accepted intent** are the served entries
before it overwritten by the intent's slot writes (`recordSlots`): the system
slot's new leaf, and each written cell's post root. -/
theorem entriesOf_step {rootBytes : List UInt8 → Digest} (image : Image)
    (before next : DataSnapshot rootBytes) (intent : DataIntent rootBytes) (chain chain' : Digest)
    (executed : DurableDataIntent.execute .complete before intent = .accepted next) (k : Key) :
    lastVal (entriesOf (image.append intent) next chain') k =
      (lastVal (recordSlots (image.accepted.length + 1) chain' (IntentRecord.ofIntent intent)) k).or
        (lastVal (entriesOf image before chain) k) := by
  obtain ⟨installed, nodup⟩ := execute_accepted_install executed
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
        simp only [Image.cellIds, Image.accepted_append, List.mem_eraseDups, List.flatMap_append,
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

/-- A checkpoint body's world-root tree, evaluated once by its open
(`DurableCheckpointCodec.openSealedWith`); the full open and the light open
both advance it to the head. -/
abbrev CheckpointRoots (rootBytes : List UInt8 → Digest) (body : DurableCheckpointCodec.Body) : Type :=
  (cache : RootCache) ×' RootsExact cache
    (DurableCheckpointCodec.stateEntries rootBytes body.height body.chain body.state)

/-- A suffix changes one system slot and the cells it actually writes. The
system leaf is the final height/chain; intermediate system leaves are not
needed when advancing directly to the verified head. -/
def suffixSlots (height : Nat) (chain : Digest) (records : List IntentRecord) :
    List (Key × Digest) :=
  (.system, systemLeaf height chain) ::
    records.flatMap fun record => record.writes.map fun write =>
      (.cell write.cellId.value, write.exactPost)

theorem lastVal_writeSlots_system (records : List IntentRecord) :
    lastVal (records.flatMap fun record => record.writes.map fun write =>
      (Key.cell write.cellId.value, write.exactPost)) Key.system = none := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      rw [List.flatMap_cons, lastVal_append, ih, lastVal_cells_system]
      rfl

/-- **Replay moves a cell's root to its last written post**, and leaves every
other cell's root where it was. -/
theorem replay_roots {rootBytes : List UInt8 → Digest} :
    ∀ (before after : DataSnapshot rootBytes) (records : List IntentRecord),
      replay rootBytes before records = some after → ∀ n : Nat,
        after.model.roots ⟨n⟩ =
          (lastVal (records.flatMap fun record => record.writes.map fun write =>
            (Key.cell write.cellId.value, write.exactPost)) (Key.cell n)).getD (before.model.roots ⟨n⟩)
  | before, after, [], replayed, n => by
      simp only [replay, Option.some.injEq] at replayed
      subst replayed
      simp [lastVal]
  | before, after, record :: records, replayed, n => by
      unfold replay at replayed
      cases bound : record.bind? rootBytes with
      | none => simp [bound] at replayed
      | some intent =>
          simp only [bound, bind, Option.bind] at replayed
          cases executed : DurableDataIntent.execute .complete before intent with
          | accepted next =>
              simp only [executed] at replayed
              obtain ⟨installed, nodup⟩ := execute_accepted_install executed
              have recordExact := IntentRecord.bind_exact bound
              rw [replay_roots next after records replayed n, List.flatMap_cons, lastVal_append]
              cases (lastVal (records.flatMap fun record => record.writes.map fun write =>
                  (Key.cell write.cellId.value, write.exactPost)) (Key.cell n)) with
              | some post => rfl
              | none =>
                  subst installed
                  subst recordExact
                  simp only [Option.none_or, IntentRecord.ofIntent]
                  rw [lastVal_writes _ nodup]
                  rfl
          | replayed recorded => simp [executed] at replayed
          | rejected reason => simp [executed] at replayed
          | crashed point next => simp [executed] at replayed

theorem lookup_of_mem_nodup : ∀ (cells : List (CellId × List UInt8)), (cells.map Prod.fst).Nodup →
    ∀ cell ∈ cells, Seed.lookup cells cell.1 = some cell.2
  | [], _, _, member => by simp at member
  | head :: rest, nodup, cell, member => by
      rw [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp member with same | later
      · subst same
        simp [Seed.lookup]
      · have distinct : head.1 ≠ cell.1 := fun same =>
          nodup.1 (same ▸ List.mem_map_of_mem (f := Prod.fst) later)
        simp only [Seed.lookup, distinct, if_false]
        exact lookup_of_mem_nodup rest nodup.2 cell later

theorem lookup_of_not_mem : ∀ (cells : List (CellId × List UInt8)) (cellId : CellId),
    cellId ∉ cells.map Prod.fst → Seed.lookup cells cellId = none
  | [], _, _ => rfl
  | head :: rest, cellId, missing => by
      rw [List.map_cons, List.mem_cons, not_or] at missing
      simp only [Seed.lookup, Ne.symm missing.1, if_false]
      exact lookup_of_not_mem rest cellId missing.2

/-- The cell ids a checkpoint state holds, as a hashed set. -/
def baseSet (base : State) : Std.HashSet CellId :=
  (SessionIndex.CellIds.empty.addAll (base.cells.map Prod.fst)).seen

theorem baseSet_contains (base : State) (cellId : CellId) :
    (baseSet base).contains cellId = true ↔ cellId ∈ base.cells.map Prod.fst := by
  have := (SessionIndex.CellIds.addAll_exact SessionIndex.CellIds.empty_exact
    (base.cells.map Prod.fst)).seen cellId
  simpa [baseSet] using this

/-- What advances a checkpoint's tree (`stateEntries` at its height) to the
served entries at the head: every enumerable cell the checkpoint does not hold,
at the absent root (none, for a checkpoint the host sealed), then the suffix's
slot writes. -/
def checkpointSlots {rootBytes : List UInt8 → Digest} (image : Image) (base : State)
    (records : List IntentRecord) (height : Nat) (chain : Digest) : List (Key × Digest) :=
  ((image.cellIds.filter fun cellId => !(baseSet base).contains cellId).map fun cellId =>
      (Key.cell cellId.value, rootBytes base.absentBytes)) ++
    suffixSlots height chain records

/-- **A checkpoint's tree advances to the head**: the served entries after a
resume from a checkpoint state are the checkpoint's world-root entries
overwritten by `checkpointSlots` (whatever chain the checkpoint's system slot
carries: the suffix rewrites it). What lets the full open evaluate the root once
— at its checkpoint — and advance it by one path per slot. -/
theorem entriesOf_checkpoint_step {rootBytes : List UInt8 → Digest} (image : Image) (base : State)
    (height : Nat) (snapshot : DataSnapshot rootBytes)
    (resumed : resume rootBytes image height base = some snapshot) (baseChain headChain : Digest)
    (k : Key) :
    lastVal (entriesOf image snapshot headChain) k =
      (lastVal (checkpointSlots (rootBytes := rootBytes) image base (image.accepted.drop height)
          image.accepted.length headChain) k).or
        (lastVal (DurableCheckpointCodec.stateEntries rootBytes height baseChain base) k) := by
  unfold resume at resumed
  have admissible : base.Admissible image := by
    by_cases holds : base.Admissible image
    · exact holds
    · rw [if_neg holds] at resumed
      cases resumed
  rw [if_pos admissible] at resumed
  obtain ⟨baseNodup, _, baseSub⟩ := admissible
  have enumerated : image.cellIds.Nodup := nodup_eraseDups _
  cases k with
  | system =>
      simp only [entriesOf, checkpointSlots, suffixSlots, lastVal_append, lastVal_cons,
        lastVal_cells_system, lastVal_writeSlots_system, DurableCheckpointCodec.stateEntries]
      simp
  | cell n =>
      -- the written post, if the suffix writes the cell
      have written : ∀ post, lastVal ((image.accepted.drop height).flatMap fun record =>
          record.writes.map fun write => (Key.cell write.cellId.value, write.exactPost)) (Key.cell n) =
            some post → (⟨n⟩ : CellId) ∈ image.cellIds := by
        intro post found
        have some : (lastVal ((image.accepted.drop height).flatMap fun record =>
            record.writes.map fun write => (Key.cell write.cellId.value, write.exactPost))
              (Key.cell n)).isSome := by rw [found]; rfl
        obtain ⟨entry, member, key⟩ := lastVal_isSome.mp some
        obtain ⟨record, inSuffix, inWrites⟩ := List.mem_flatMap.mp member
        obtain ⟨write, writeIn, rfl⟩ := List.mem_map.mp inWrites
        have value : write.cellId.value = n := Key.cell.inj key
        have cell : write.cellId = ⟨n⟩ := by rw [← value]
        unfold Image.cellIds
        rw [List.mem_eraseDups, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨record, List.mem_of_mem_drop inSuffix,
          List.mem_map.mpr ⟨write, writeIn, cell⟩⟩)
      have roots := replay_roots _ _ _ resumed n
      -- the checkpoint's cell part, as its snapshot's roots
      have stateCells : (base.cells.map fun cell => (Key.cell cell.1.value, rootBytes cell.2)) =
          (base.cells.map Prod.fst).map fun cellId =>
            (Key.cell cellId.value, (base.snapshot rootBytes (image.accepted.take height)).model.roots cellId) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro cell member
        simp [State.snapshot, tableLookup_rootTable, lookup_of_mem_nodup base.cells baseNodup cell member]
      have filtered : (image.cellIds.filter fun cellId => !(baseSet base).contains cellId).Nodup :=
        enumerated.filter _
      simp only [entriesOf, checkpointSlots, suffixSlots, DurableCheckpointCodec.stateEntries,
        lastVal_append, lastVal_cons, reduceCtorEq, if_false, Option.or_none]
      rw [stateCells, lastVal_cellIds _ enumerated, lastVal_cellIds _ baseNodup,
        lastVal_cellIds _ filtered, roots]
      have notContains : (baseSet base).contains ⟨n⟩ = false ↔ (⟨n⟩ : CellId) ∉ base.cells.map Prod.fst := by
        rw [← Bool.not_eq_true, baseSet_contains]
      cases hw : lastVal ((image.accepted.drop height).flatMap fun record =>
          record.writes.map fun write => (Key.cell write.cellId.value, write.exactPost)) (Key.cell n) with
      | some post =>
          simp [written post hw, List.mem_filter, notContains]
      | none =>
          by_cases inBase : (⟨n⟩ : CellId) ∈ base.cells.map Prod.fst
          · simp [inBase, baseSub _ inBase, List.mem_filter, notContains]
          · have absent : (base.snapshot rootBytes (image.accepted.take height)).model.roots ⟨n⟩ =
                rootBytes base.absentBytes := by
              simp [State.snapshot, tableLookup_rootTable, lookup_of_not_mem base.cells ⟨n⟩ inBase]
            by_cases inImage : (⟨n⟩ : CellId) ∈ image.cellIds
            · simp [inBase, inImage, absent, List.mem_filter, notContains]
            · simp [inBase, inImage, List.mem_filter, notContains]

#assert_axioms entriesOf_checkpoint_step

/-- The base a full open resumes from: its height and state, the accumulator
frontier and index root there, and the tree its checkpoint's open evaluated (none
for the seed at height 0). -/
private abbrev OpenBase (rootBytes : List UInt8 → Digest) : Type :=
  (height : Nat) × (state : State) × List (Nat × Digest) × Digest ×
    Option ((chain : Digest) × (cache : RootCache) ×' RootsExact cache
      (DurableCheckpointCodec.stateEntries rootBytes height chain state))
/-! ## The World a loaded image holds (FD-1 4a)

A `Loaded` carries the deployed World its snapshot represents, or the reason its
log is not a turn log.  An append advances it by `World.admit` of the derived turn
(`WorldTrack.advance`, representation by `represents_of_admitted`); an open folds the
log's turns from the seed's genesis World and DECIDES the representation
(`representsCheck_sound`); the append path refuses an intent whose turn the World
does not admit (`prepareAppend`), so no `lost` image reaches the Store. -/

/-- The World a snapshot at a height represents, or why there is none. -/
inductive WorldTrack {rootBytes : List UInt8 → Digest} (snapshot : DataSnapshot rootBytes)
    (height : Nat) : Type where
  | held (world : HostRefinesWorld.DWorld)
      (represents : HostRefinesWorld.SnapRepresents DeployedBridge.bridge snapshot height world)
  | lost (reason : String)

/-- The held World, if any. -/
def WorldTrack.world? {rootBytes : List UInt8 → Digest} {snapshot : DataSnapshot rootBytes}
    {height : Nat} : WorldTrack snapshot height → Option HostRefinesWorld.DWorld
  | .held w _ => some w
  | .lost _ => none

/-- The deployed judge of a pin, read from the snapshot a held World represents: the
cell retired, or its canonical bytes (which the executor already holds) not hashing
to the asserted digest. It agrees with `World.pinFails` at a represented World
(`snapPinFails_eq`), which re-encodes the World's own copy of the cell instead. -/
def snapPinFails {rootBytes : List UInt8 → Digest} (snapshot : DataSnapshot rootBytes)
    (w : HostRefinesWorld.DWorld) (p : Minidregg.Kernel.World.CellId × Digest) : Bool :=
  (w.retired p.1).isSome || decide (ResourceBirthCodec.rootBytes (snapshot.canonicalBytes ⟨p.1⟩) ≠ p.2)

/-- At a World the snapshot represents, the snapshot's judge is the World's. -/
theorem snapPinFails_eq {rootBytes : List UInt8 → Digest} {snapshot : DataSnapshot rootBytes}
    {height : Nat} {w : HostRefinesWorld.DWorld}
    (rep : HostRefinesWorld.SnapRepresents DeployedBridge.bridge snapshot height w)
    (p : Minidregg.Kernel.World.CellId × Digest) :
    snapPinFails snapshot w p = Minidregg.Kernel.World.pinFails DeployedHistory.history w p := by
  cases hr : w.retired p.1 with
  | some _ =>
      have fails : Minidregg.Kernel.World.pinFails DeployedHistory.history w p = true := by
        cases hp : Minidregg.Kernel.World.pinFails DeployedHistory.history w p
        · have := ((Minidregg.Kernel.World.pinFails_eq_false_iff DeployedHistory.history).1 hp).1
          rw [hr] at this; cases this
        · rfl
      rw [fails]
      simp [snapPinFails, hr]
  | none =>
      have live : DeployedBridge.bridge.codec.retires (snapshot.canonicalBytes ⟨p.1⟩) = false := by
        have retired := rep.retired p.1
        rw [hr] at retired
        exact retired.symm
      have root := DeployedHistory.deployed_pinCoherent _ _ (rep.cells p.1) live
      rw [DeployedBridge.bridge_pin] at root
      have holds : Minidregg.Kernel.World.pinFails DeployedHistory.history w p = false ↔
          ResourceBirthCodec.rootBytes (snapshot.canonicalBytes ⟨p.1⟩) = p.2 := by
        rw [Minidregg.Kernel.World.pinFails_eq_false_iff DeployedHistory.history, root]
        simp [hr]
      cases hp : Minidregg.Kernel.World.pinFails DeployedHistory.history w p
      · simp [snapPinFails, hr, holds.1 hp]
      · have differs : ResourceBirthCodec.rootBytes (snapshot.canonicalBytes ⟨p.1⟩) ≠ p.2 :=
          fun same => by have := holds.2 same; rw [hp] at this; cases this
        simp [snapPinFails, hr, differs]

/-- **One accepted execution, one admitted turn.**  From a held World, derive the
intent's turn against it, refuse it unless its charge is the intent's on every
lane (the Host debits what the World debits), and admit it; the result
represents the executed snapshot one height up. -/
def WorldTrack.advance {rootBytes : List UInt8 → Digest} {snapshot next : DataSnapshot rootBytes}
    {height height' : Nat} {intent : DataIntent rootBytes}
    (executed : DurableDataIntent.execute .complete snapshot intent = .accepted next)
    (up : height' = height + 1) : WorldTrack snapshot height → WorldTrack next height'
  | .lost reason => .lost reason
  | .held w rep =>
      match derived : TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent with
      | .error refusal => .lost s!"height {height'}: the intent is not a turn: {repr refusal}"
      | .ok t =>
          match charged : DeployedCharge.mismatch t.charge intent.exactCharge with
          | some lane => .lost s!"height {height'}: the intent's charge is not its turn's: {repr lane}"
          | none =>
          -- The pins are judged from the snapshot's own bytes (`snapPinFails_eq`): the World's
          -- copy of each pinned cell is never re-encoded for its digest.
          match admitted : Minidregg.Kernel.World.World.admitPinned DeployedHistory.history
              (Minidregg.Kernel.World.pinCheckFromBy (snapPinFails snapshot w) 0 t.pins) w t with
          | .error reason => .lost s!"height {height'}: the World refuses the turn: {repr reason}"
          | .ok w' => .held (WorldCompact.compactEvery height' w') (by
              have admit := (Minidregg.Kernel.World.admitPinned_by_eq DeployedHistory.history w t
                (fun p _ => snapPinFails_eq rep p)).symm.trans admitted
              rw [WorldCompact.compactEvery_eq, up]
              exact HostRefinesWorld.represents_of_admitted DeployedBridge.bridge
                DeployedHistory.history rep derived (DeployedCharge.mismatch_none charged) executed
                admit)

/-- **The append path refuses an intent charged other than its turn.**  From a
held World, an intent whose derived turn's charge differs from its exact charge
on any lane leaves the World lost: `prepareAppend` refuses it before a byte is
written. -/
theorem WorldTrack.advance_refuses_mismatch {rootBytes : List UInt8 → Digest}
    {snapshot next : DataSnapshot rootBytes} {height height' : Nat} {intent : DataIntent rootBytes}
    (executed : DurableDataIntent.execute .complete snapshot intent = .accepted next)
    (up : height' = height + 1) {w : HostRefinesWorld.DWorld}
    (rep : HostRefinesWorld.SnapRepresents DeployedBridge.bridge snapshot height w)
    {t : TurnOfIntent.DTurn DeployedBridge.deployedR Digest}
    (derived : TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent = .ok t)
    (differs : t.charge ≠ intent.exactCharge) :
    ∃ reason, WorldTrack.advance executed up (.held w rep) = .lost reason := by
  cases hm : DeployedCharge.mismatch t.charge intent.exactCharge with
  | none => exact absurd (DeployedCharge.mismatch_none hm) differs
  | some lane =>
    unfold WorldTrack.advance
    split
    · rename_i h; cases h
    · rename_i h; cases h
      split
      · rename_i r h; rw [derived] at h; cases h
      · rename_i t' h
        rw [derived] at h
        cases h
        split
        · exact ⟨_, rfl⟩
        · rename_i h
          rw [hm] at h
          cases h

/-- **The plant: a receiver that archives its event but charges none of it is
refused.**  An intent whose storage lane is only its turn's legs and born images
-- omitting the bytes its event retains -- while its event retains some, is not
appended: the World charges the event (`DeployedHistory.eventBytes`), so the
charges differ and the append path loses the World. -/
theorem WorldTrack.advance_refuses_unretained {rootBytes : List UInt8 → Digest}
    {snapshot next : DataSnapshot rootBytes} {height height' : Nat} {intent : DataIntent rootBytes}
    (executed : DurableDataIntent.execute .complete snapshot intent = .accepted next)
    (up : height' = height + 1) {w : HostRefinesWorld.DWorld}
    (rep : HostRefinesWorld.SnapRepresents DeployedBridge.bridge snapshot height w)
    {t : TurnOfIntent.DTurn DeployedBridge.deployedR Digest}
    (derived : TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent = .ok t)
    (retains : intent.event.canonicalBytes ≠ [])
    (omits : intent.exactCharge .storageBytes =
      (t.legs.map DeployedHistory.legBytes).sum +
        (t.creates.map fun c => DeployedHistory.imageBytes c.2.1).sum) :
    ∃ reason, WorldTrack.advance executed up (.held w rep) = .lost reason := by
  refine WorldTrack.advance_refuses_mismatch executed up rep derived fun same => ?_
  have lane := congrFun same .storageBytes
  have d := (TurnOfIntent.ofCells_ok derived).eq
  have event : t.event = intent.event := by rw [d]; rfl
  have charged : t.charge .storageBytes =
      TurnOfIntent.storageOf DeployedHistory.history t.creates t.legs t.event := by
    rw [d]; simp [TurnOfIntent.turnOf, TurnOfIntent.chargeOf]
  rw [charged, omits, event] at lane
  have positive : 0 < intent.event.canonicalBytes.length := List.length_pos_iff.mpr retains
  simp only [TurnOfIntent.storageOf, DeployedHistory.history, WorldRoot.cshakeHistory,
    DeployedHistory.eventBytes] at lane
  omega

#assert_axioms WorldTrack.advance_refuses_mismatch
#assert_axioms WorldTrack.advance_refuses_unretained

/-- Fold a log's records as turns from a World: bind, derive, compare the
charge, admit; refuse by height. -/
def foldRecords (rootBytes : List UInt8 → Digest) :
    HostRefinesWorld.DWorld → Nat → List IntentRecord → Except String HostRefinesWorld.DWorld
  | w, _, [] => .ok w
  | w, height, record :: rest =>
      match record.bind? rootBytes with
      | none => .error s!"height {height + 1}: the record does not bind its roots"
      | some intent =>
          match TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history w intent with
          | .error refusal => .error s!"height {height + 1}: the record is not a turn: {repr refusal}"
          | .ok t =>
              match DeployedCharge.mismatch t.charge intent.exactCharge with
              | some lane =>
                  .error s!"height {height + 1}: the record's charge is not its turn's: {repr lane}"
              | none =>
              match Minidregg.Kernel.World.World.admit DeployedHistory.history w t with
              | .error reason => .error s!"height {height + 1}: the World refuses the turn: {repr reason}"
              | .ok w' => foldRecords rootBytes (WorldCompact.compactEvery (height + 1) w') (height + 1) rest

/-- The seed's genesis World (`TurnLog.genesisOfSeed`), or why it has none. -/
def genesisWorld (seed : Seed) : Except String HostRefinesWorld.DWorld :=
  match TurnLog.genesisOfSeed seed with
  | .error refusal => .error s!"the seed has no genesis World: {repr refusal}"
  | .ok genesis => .ok genesis

/-- The World a resumed snapshot holds, from a World the open folded (or why it has none): the
representation DECIDED against the snapshot (`representsCheck_sound`). -/
def trackOfWorld (rootBytes : List UInt8 → Digest) (image : Image) {height : Nat} {state : State}
    {snapshot : DataSnapshot rootBytes} (resumed : resume rootBytes image height state = some snapshot)
    (world : Except String HostRefinesWorld.DWorld) : WorldTrack snapshot image.accepted.length :=
  match world with
  | .error message => .lost message
  | .ok w =>
      if ok : HostRefinesWorld.representsCheck image snapshot w = true then
        .held w (HostRefinesWorld.representsCheck_sound resumed ok)
      else .lost "the folded World does not represent the resumed snapshot"

/-- **The World of a resumed image**: the seed's genesis World, the whole log folded as turns, and
the representation decided against the resumed snapshot. The genesis replay (`loadImage`, the
audit) uses it; the open folds only the records after its checkpoint (`openState`). -/
def trackOf (rootBytes : List UInt8 → Digest) (image : Image) {height : Nat} {state : State}
    {snapshot : DataSnapshot rootBytes} (resumed : resume rootBytes image height state = some snapshot) :
    WorldTrack snapshot image.accepted.length :=
  trackOfWorld rootBytes image resumed
    ((genesisWorld image.seed).bind fun genesis => foldRecords rootBytes genesis 0 image.accepted)

/-- A checkpoint's World: its state's cells decoded as genesis decodes the seed's
(`TurnLog.genesisOfSeed`), beside the system store the v4 body carries. -/
def worldOfCheckpoint (state : State)
    (system : Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys) :
    Option HostRefinesWorld.DWorld :=
  (state.cells.foldlM (fun (cells : Minidregg.Kernel.World.Cells DeployedBridge.deployedR) entry =>
      (DeployedBridge.decodeCell entry.2).map fun slot => DFinsupp.update cells entry.1.value slot)
    0).map fun cells => ⟨cells, system⟩

/-- A v4 checkpoint body's World: its system store beside its state's cells. -/
def _root_.Minidregg.Compiler.DurableCheckpointCodec.Body.world (body : Body) :
    Option HostRefinesWorld.DWorld :=
  body.system.bind (worldOfCheckpoint body.state)

/-- Re-decide a held World against a re-materialized snapshot of the same image. -/
def WorldTrack.recheck {rootBytes : List UInt8 → Digest} {snapshot snapshot' : DataSnapshot rootBytes}
    (image : Image) {height : Nat} {state : State}
    (resumed : resume rootBytes image height state = some snapshot') :
    WorldTrack snapshot image.accepted.length → WorldTrack snapshot' image.accepted.length
  | .lost reason => .lost reason
  | .held w _ =>
      if ok : HostRefinesWorld.representsCheck image snapshot' w = true then
        .held w (HostRefinesWorld.representsCheck_sound resumed ok)
      else .lost "the re-materialized snapshot does not represent the held World"

/-! ## The loaded, resumed image -/

structure Loaded (rootBytes : List UInt8 → Digest) where
  image : Image
  baseHeight : Nat
  base : State
  /-- The state at the head, as data (`DurableEngine.Engine`): the one
  representation a session holds. `Loaded.snapshot` is its view. -/
  engine : DurableEngine.Engine rootBytes
  /-- The engine's view (`snapshotExact`), kept beside it: O(1) to build, and
  an opaque field to every consumer that reasons about the snapshot (unfolding
  the view into its closures makes defeq checks evaluate the root hash). -/
  snapshot : DataSnapshot rootBytes
  snapshotExact : snapshot = engine.view rootBytes
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
  /-- Nullifier ↦ the first accepted index consuming it: a past read's consumed
  set is this index against the read's base height (`KeyIndex.below_eq`). -/
  spentAt : SessionIndex.KeyIndex StableNullifier
  spentAtExact : spentAt.Exact IntentRecord.nullifiers image.accepted
  /-- Written cell id ↦ the first accepted index writing it: a past read's
  admissibility check (`Loaded.admissibleAt`). -/
  writesAt : SessionIndex.KeyIndex CellId
  writesAtExact : writesAt.Exact (fun record => record.writes.map DataWrite.cellId) image.accepted
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
  /-- The World the snapshot represents (FD-1 4a). -/
  track : WorldTrack snapshot image.accepted.length
  /-- The chain log: element `h` is the chain after the first `h` accepted records, the log
  start first and `chain` last (`chainPrefixes`). The certify rule reads past heights from it
  (`Kernel.ChainHistory`, the instance below); pushed at every append. -/
  chainLog : Array Digest
  chainLogExact : chainLog.toList = chainPrefixes logStart image.accepted

/-- The same image carrying no World (its `track` lost). Only the append (which refuses a lost
track, `prepareAppend`) and the checkpoint seal (`Loaded.system`) read the World. A consent
provider's anchored suffix walk (`ConsentAnchor.resume`) re-derives and re-executes every record
but never appends or seals from it: started untracked, each of its `extend`s skips
`WorldTrack.advance` (the record's turn derived and admitted), which the provider's replay of the
same records from the Store (`DurableReceiverIO.extendStored`) has already judged. The Host's
walks stay tracked (`NativeHostReplay.verifyFrom`, `verifyLoaded`, `extendVerified`): receivers
append from a verified walk's image (`receiveLoadedDetailedWithFresh` from `old.opened.durable`)
and the Host session adopts a readback built from it, and the append refuses a lost track. -/
def Loaded.untracked {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Loaded rootBytes :=
  { loaded with track := .lost "a verification walk carries no World" }

@[simp] theorem Loaded.untracked_image {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.untracked.image = loaded.image := rfl

@[simp] theorem Loaded.untracked_logStart {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) : loaded.untracked.logStart = loaded.logStart := rfl

/-- The head height is the chronological journal's length. -/
def Loaded.height {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Nat :=
  loaded.image.accepted.length

/-- The head height, read off the array already carried beside the log. -/
def Loaded.heightFast {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Nat :=
  loaded.rootLog.size

/-- Every compiled height read is the array size; the logical journal remains
height's defining semantics. -/
@[csimp] theorem Loaded.height_eq_heightFast : @Loaded.height = @Loaded.heightFast := by
  funext rootBytes loaded
  exact loaded.rootLogSize.symm

/-- The cached height is exactly the chronological journal's length. -/
@[simp] theorem Loaded.height_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.height = loaded.image.accepted.length :=
  rfl

/-- The snapshot's history has one event per accepted record. -/
theorem Loaded.history_length_eq_height {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) : loaded.snapshot.model.history.length = loaded.height := by
  rw [DurableEngine.resume_history loaded.resumed, List.length_reverse, List.length_map,
    Loaded.height_eq]

/-- **The durable chain history**: the loaded image's chain log behind the kernel's
`ChainHistory` interface. Its head is the image's height, the same head the tail gate
judges a record at (`Kernel.TailBound.recordHeight`). -/
instance {rootBytes : List UInt8 → Digest} : Kernel.ChainHistory (Loaded rootBytes) where
  head loaded := loaded.height
  chainAt loaded height := loaded.chainLog[height]?
  chainAt_le_head loaded height digest held := by
    have listed : loaded.chainLog.toList[height]? = some digest := by
      rw [Array.getElem?_toList]; exact held
    rw [loaded.chainLogExact] at listed
    have lt := (List.getElem?_eq_some_iff.mp listed).1
    rw [DurableLogTags.chainPrefixes_length] at lt
    show height ≤ loaded.image.accepted.length
    exact Nat.lt_succ_iff.mp lt

/-- **The chain log is faithful to the log**: every value it holds is the chain after
that prefix of the accepted records (`chainAfter`), and it holds the head. -/
theorem Loaded.faithful {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Kernel.ChainHistory.Faithful loaded
      (fun height => chainAfter loaded.logStart (loaded.image.accepted.take height)) := by
  have at_ : ∀ height, height ≤ loaded.height →
      Kernel.ChainHistory.chainAt loaded height =
        some (chainAfter loaded.logStart (loaded.image.accepted.take height)) := by
    intro height within
    show loaded.chainLog[height]? = _
    rw [← Array.getElem?_toList, loaded.chainLogExact]
    exact DurableLogTags.chainPrefixes_getElem? _ _ _ within
  refine ⟨?_, ?_⟩
  · intro height digest held
    have within := Kernel.ChainHistory.chainAt_le_head loaded height digest held
    rw [at_ height within] at held
    exact (Option.some.inj held).symm
  · exact at_ _ (Nat.le_refl _)

/-- The served world root: read off the cache, never recomputed. -/
def Loaded.worldRoot {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Digest :=
  loaded.roots.root

/-- **The served root is C1's root of the served entries.** -/
theorem Loaded.worldRoot_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.worldRoot = deployedRoot (entriesOf loaded.image loaded.snapshot loaded.chain) :=
  loaded.rootsExact.root_eq

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
  match found : DurableEngine.resumeEngine rootBytes image 0 (State.ofSeed image.seed) with
  | none => .error "durable image journal does not replay through the canonical executor"
  | some engine =>
      let chains := chainPrefixes logStart image.accepted
      let chain := chains.getLast?.getD logStart
      let built := RootCache.build (entriesOf image (engine.view rootBytes) chain)
      match trackOf rootBytes image (DurableEngine.resume_of_resumeEngine found) with
      | .lost reason => .error s!"durable image is not a turn log: {reason}"
      | track@(.held _ _) =>
      .ok ⟨image, 0, State.ofSeed image.seed, engine, engine.view rootBytes, rfl, Nat.zero_le _,
        DurableEngine.resume_of_resumeEngine found, logStart, chain,
        DurableLogTags.chainPrefixes_getLast? logStart image.accepted, built.1, built.2,
        PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
        SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
        SessionIndex.TxIndex.ofRecords image.accepted,
        SessionIndex.TxIndex.ofRecords_exact image.accepted,
        SessionIndex.KeyIndex.ofRecords IntentRecord.nullifiers image.accepted,
        SessionIndex.KeyIndex.ofRecords_exact IntentRecord.nullifiers image.accepted,
        SessionIndex.KeyIndex.ofRecords (fun record => record.writes.map DataWrite.cellId) image.accepted,
        SessionIndex.KeyIndex.ofRecords_exact (fun record => record.writes.map DataWrite.cellId)
          image.accepted,
        Array.replicate image.accepted.length none, Array.size_replicate,
        if image.accepted.isEmpty then some [] else none, none, track,
        chains.toArray, List.toList_toArray⟩

theorem loadImage_image {rootBytes : List UInt8 → Digest} {logStart : Digest} {image : Image}
    {loaded : Loaded rootBytes} (built : loadImage rootBytes logStart image = .ok loaded) :
    loaded.image = image := by
  unfold loadImage at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · cases built
      rfl

theorem loadImage_baseHeight {rootBytes : List UInt8 → Digest} {logStart : Digest} {image : Image}
    {loaded : Loaded rootBytes} (built : loadImage rootBytes logStart image = .ok loaded) :
    loaded.baseHeight = 0 := by
  unfold loadImage at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · cases built
      rfl

/-- The loaded genesis image of a seed. -/
def loadSeed (rootBytes : List UInt8 → Digest) (logStart : Digest) (seed : Seed) :
    Except String (Loaded rootBytes) :=
  loadImage rootBytes logStart (Image.ofAccepted seed [])

/-- A whole image carried as portable evidence bytes (never the Store): exact
decode, then the genesis replay. -/
def loadBytes (rootBytes : List UInt8 → Digest) (logStart : Seed → Digest) (bytes : List UInt8) :
    Except String (Loaded rootBytes) :=
  match DurableReceiverCodec.decode bytes with
  | none => .error "noncanonical or unsupported durable image"
  | some image => loadImage rootBytes (logStart image.seed) image

def decodeRecordsFrom : Nat → List Entry → Except String (List IntentRecord)
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

/-- **The executing part of the open** (HOT-PATH §2(h); `DurableFastForwardSpec.Impl.ffState`): what
the checkpoint and the entries after it determine. Nothing below the checkpoint is among its
inputs: the suffix's tags verify chained from the checkpoint's chain, the accumulator walks on from
the checkpoint's frontier, the suffix is replayed with no prefix nullifier or transaction id known
(`DurableEngine.resume_suffix` says when that is the resume), and its turns fold from the
checkpoint's World. -/
structure OpenState (rootBytes : List UInt8 → Digest) (suffix : List Entry) where
  base : OpenBase rootBytes
  /-- The chain at the base: the checkpoint's, or the seed's log start. -/
  baseChain : Digest
  records : List IntentRecord
  decoded : List.Forall₂ (fun bytes record => recordFrame.decode bytes = some record)
    (suffix.map (·.record)) records
  /-- The chain before and after each suffix record, from `baseChain`. -/
  chains : List Digest
  chainsEq : chains = DurableLogTags.chainPrefixesStored baseChain (suffix.map (·.record))
  frontier : List (Nat × Digest)
  /-- The suffix replayed from the checkpoint state alone. -/
  engine : DurableEngine.Engine rootBytes
  replayed : (DurableEngine.Engine.ofState rootBytes base.2.1 []).replay rootBytes records = some engine
  /-- The checkpoint's World (the seed's genesis World at height 0), before the suffix. -/
  baseWorld : Except String HostRefinesWorld.DWorld
  /-- The checkpoint's World with the suffix folded as turns (or why there is none). -/
  world : Except String HostRefinesWorld.DWorld

/-- The executing part of the open, from the checkpoint's bytes (none: the seed at height 0), the
stored entries after it and the Store's head height. -/
def openState (key : MacKey) (rootBytes : List UInt8 → Digest) (logStart : Digest) (seed : Seed)
    (checkpoint : Option (List UInt8)) (suffix : List Entry) (head : Nat) :
    Except String (OpenState rootBytes suffix) := do
  let ⟨base, baseChain, start⟩ ← match checkpoint with
    | none =>
        pure (⟨⟨0, State.ofSeed seed, [], DurableIndex.emptyDigest, none⟩, logStart, genesisWorld seed⟩ :
          OpenBase rootBytes × Digest × Except String HostRefinesWorld.DWorld)
    | some bytes =>
        match openSealedWith (α := CheckpointRoots rootBytes) key rootBytes bytes
            (fun _ => RootCache.build _) (fun _ built => built.1.root)
            (fun _ => RootCache.ofEntries_root _) with
        | .error reason => throw s!"checkpoint refused: {repr reason}"
        | .ok ⟨body, built⟩ =>
            pure (⟨⟨body.height, body.state, body.frontier, body.indexRoot, some ⟨body.chain, built⟩⟩,
              body.chain,
              match body.world with
              | none => .error "the checkpoint carries no World its cells decode into"
              | some w => .ok w⟩ : OpenBase rootBytes × Digest × Except String HostRefinesWorld.DWorld)
  if base.1 + suffix.length ≠ head then
    throw "the checkpoint and the entries after it do not reach the log head"
  let chains := DurableLogTags.chainPrefixesStored baseChain (suffix.map (·.record))
  verifyTags key base.1 chains (suffix.map (·.tag))
  let ⟨records, decoded⟩ ← match found : decodeRecordsFrom (base.1 + 1) suffix with
    | .error message => throw message
    | .ok records => pure (⟨records, decodeRecordsFrom_forall₂ _ _ _ found⟩ :
        {records : List IntentRecord // List.Forall₂
          (fun bytes record => recordFrame.decode bytes = some record) (suffix.map (·.record)) records})
  let frontier ← walkFrontier base.1 base.2.2.1 (suffix.zip chains.tail)
  let ⟨engine, replayed⟩ ← match found : (DurableEngine.Engine.ofState rootBytes base.2.1 []).replay rootBytes records with
    | none => throw "durable log suffix does not replay through the canonical executor"
    | some engine => pure (⟨engine, found⟩ : {engine : DurableEngine.Engine rootBytes //
        (DurableEngine.Engine.ofState rootBytes base.2.1 []).replay rootBytes records = some engine})
  return ⟨base, baseChain, records, decoded, chains, rfl, frontier, engine, replayed, start,
    start.bind fun w => foldRecords rootBytes w base.1 records⟩

/-- A decided fact as a value, or the refusal naming it. -/
private def require (fact : Prop) [Decidable fact] (message : String) : Except String (PLift fact) :=
  if holds : fact then .ok ⟨holds⟩ else .error message

/-- **The gate, then the session build** (`DurableFastForwardSpec.Impl.ff`'s gate, then `ofOpened`).
The entries below the checkpoint number its height, every tag among them verifies chained from the
seed's log start, and their chain is the checkpoint's. Nothing below is executed: the records are
decoded, the six indexes and the root log rebuilt from them and the tags, and two facts decided
over the decoded records, the checkpoint state's admissibility for the whole log and that no
record after it carries a nullifier or transaction id below it: then the executing part's replay
is the resume (`DurableEngine.resume_suffix`), the session's resume proof. -/
def openLoaded (key : MacKey) (rootBytes : List UInt8 → Digest) (logStart : Digest) (seed : Seed)
    (below suffix : List Entry) (opened : OpenState rootBytes suffix) :
    Except String ((loaded : Loaded rootBytes) ×'
      {chains : List Digest // chains = chainPrefixes loaded.logStart loaded.image.accepted}) := do
  let baseHeight := opened.base.1
  let base := opened.base.2.1
  let ⟨count⟩ ← require (below.length = baseHeight)
    "the entries below the checkpoint do not number its height"
  let prefixChains := DurableLogTags.chainPrefixesStored logStart (below.map (·.record))
  verifyTags key 0 prefixChains (below.map (·.tag))
  let ⟨chained⟩ ← require (prefixChains.getLastD logStart = opened.baseChain)
    "checkpoint does not match the log chain"
  -- The checkpoint's accumulator frontier and index root are the ones the (MAC-verified) tag of
  -- the entry at its height carries.
  if 0 < baseHeight then
    match below.getLast?.bind (trailerCarried ·.tag) with
    | some carried =>
        if carried.frontier ≠ frontierDigest baseHeight opened.base.2.2.1 ∨
            carried.indexRoot ≠ opened.base.2.2.2.1 then
          throw "checkpoint accumulator differs from its log entry's tag"
    | none => throw "checkpoint height has no log entry"
  let ⟨prefixRecords, prefixDecoded⟩ ← match found : decodeRecordsFrom 1 below with
    | .error message => throw message
    | .ok records => pure (⟨records, decodeRecordsFrom_forall₂ _ _ _ found⟩ :
        {records : List IntentRecord // List.Forall₂
          (fun bytes record => recordFrame.decode bytes = some record) (below.map (·.record)) records})
  let image : Image := Image.ofAccepted seed (prefixRecords ++ opened.records)
  let ⟨admissible⟩ ← require (DurableEngine.admissibleFast image base = true)
    "the checkpoint state is not admissible for the log"
  let ⟨disjoint⟩ ← require (DurableEngine.disjointFast prefixRecords opened.records = true)
    "a record after the checkpoint carries a nullifier or transaction id below it"
  have height : prefixRecords.length = baseHeight := by
    rw [← prefixDecoded.length_eq, List.length_map]; exact count
  -- The session's engine: the replayed head state over every record (journal, history and the
  -- consumed and recorded sets from the records; no record executed).
  let engine := DurableEngine.Engine.ofState rootBytes (DurableEngine.Engine.headState opened.engine) image.accepted
  have resumed : resume rootBytes image baseHeight base = some (engine.view rootBytes) := by
    rw [DurableEngine.Engine.view_ofState, ← height]
    simpa only [image, Image.accepted_ofAccepted] using
      (DurableEngine.resume_suffix rootBytes
        ((DurableEngine.admissibleFast_iff _ _).mp admissible)
        ((DurableEngine.disjointFast_iff _ _).mp disjoint) opened.replayed)
  let chains := prefixChains ++ opened.chains.tail
  have chainsEq : chains = chainPrefixes logStart image.accepted := by
    simp only [image, Image.accepted_ofAccepted]
    have pre := DurableLogTags.chainPrefixesStored_eq logStart _ _ prefixDecoded
    have suf := DurableLogTags.chainPrefixesStored_eq opened.baseChain _ _ opened.decoded
    have baseChain : opened.baseChain = chainAfter logStart prefixRecords := by
      have last := DurableLogTags.chainPrefixes_getLast? logStart prefixRecords
      rw [← pre, ← List.getLastD_eq_getLast?] at last
      rw [← last]; exact chained.symm
    show DurableLogTags.chainPrefixesStored logStart (below.map (·.record)) ++ opened.chains.tail =
      chainPrefixes logStart (prefixRecords ++ opened.records)
    rw [opened.chainsEq, suf, pre, baseChain]
    simp only [DurableLogTags.chainPrefixes, List.scanl_append]
    rfl
  let headChain := chains.getLast?.getD logStart
  have within : baseHeight ≤ image.accepted.length := by
    simp only [image, Image.accepted_ofAccepted]
    show baseHeight ≤ (prefixRecords ++ opened.records).length
    rw [List.length_append, height]; exact Nat.le_add_right _ _
  let built : (cache : RootCache) ×'
      RootsExact cache (entriesOf image (engine.view rootBytes) headChain) :=
    match opened.base.2.2.2.2 with
    | none => RootCache.build (entriesOf image (engine.view rootBytes) headChain)
    | some ⟨baseChain, cache, exact⟩ =>
        exact.advance (checkpointSlots (rootBytes := rootBytes) image base (image.accepted.drop baseHeight)
            image.accepted.length headChain)
          (entriesOf_checkpoint_step image base baseHeight (engine.view rootBytes) resumed
            baseChain headChain)
  let entries := below ++ suffix
  -- Every entry's verified tag carries the receipt root after it (`DurableLogTags.verifyTags_carried`).
  let rootLog : Array (Option Digest) :=
    (entries.map fun entry => some ((trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩)).toArray
  let ⟨sized⟩ ← require (rootLog.size = image.accepted.length)
    "durable log entries and records differ in number"
  let loaded : Loaded rootBytes :=
    ⟨image, baseHeight, base, engine, engine.view rootBytes, rfl, within, resumed, logStart,
    headChain,
    (by show chains.getLast?.getD logStart = _; rw [chainsEq]
        exact DurableLogTags.chainPrefixes_getLast? logStart image.accepted),
    built.1, built.2,
    PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
    SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
    SessionIndex.TxIndex.ofRecords image.accepted, SessionIndex.TxIndex.ofRecords_exact image.accepted,
    SessionIndex.KeyIndex.ofRecords IntentRecord.nullifiers image.accepted,
    SessionIndex.KeyIndex.ofRecords_exact IntentRecord.nullifiers image.accepted,
    SessionIndex.KeyIndex.ofRecords (fun record => record.writes.map DataWrite.cellId) image.accepted,
    SessionIndex.KeyIndex.ofRecords_exact (fun record => record.writes.map DataWrite.cellId)
      image.accepted,
    rootLog, sized, some opened.frontier,
    entries.getLast?.map (·.tag), trackOfWorld rootBytes image resumed opened.world,
    chains.toArray, by rw [List.toList_toArray]; exact chainsEq⟩
  if let .lost reason := loaded.track then
    throw s!"durable log is not a turn log: {reason}"
  -- The head's stored root is the root this open just served: a rewritten head root refuses
  -- here, not at a later receipt.
  match rootLog.back? with
  | some (some stored) =>
      if stored ≠ loaded.worldRoot then
        throw "durable log head root differs from the replayed root"
  | _ => pure ()
  return ⟨loaded, chains, chainsEq⟩

/-- A full open with what a cut at or above its base needs (`Loaded.cutAbove`): the chain value
after every stored record (`chainPrefixes`) and the World at the base, the checkpoint's (or the
seed's genesis World), before any record after it is folded. -/
structure Chained (rootBytes : List UInt8 → Digest) where
  loaded : Loaded rootBytes
  chains : List Digest
  chainsExact : chains = chainPrefixes loaded.logStart loaded.image.accepted
  baseWorld : Except String HostRefinesWorld.DWorld

/-- The single open path, keeping what a cut above the base needs (`Chained`): the executing part
(`openState`) over the checkpoint and the entries after it, then the gate and the session build
(`openLoaded`) over the entries below it. Every check refuses; nothing reinterprets. -/
def loadChained (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Chained rootBytes)) := do
  -- Operator measurement control (as `DurableServed.openHead`): MINI_OPEN_TIMING=1 prints each
  -- stage's elapsed time to stderr.
  let timing := (← IO.getEnv "MINI_OPEN_TIMING") == some "1"
  let started ← IO.monoMsNow
  let lap := fun (label : String) => do
    if timing then IO.eprintln s!"full open {label}: {(← IO.monoMsNow) - started} ms"
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
      lap s!"read ({stored.entries.length} entries)"
      let some seedBytes := stored.seed | return .error "durable seed missing"
      if let some refusal := (SeedEpoch.ofBytes seedBytes).refusal then
        return .error s!"durable store refused: {refusal}"
      let some seed := seedFrame.decode seedBytes | return .error "noncanonical durable seed"
      if stored.entries.length ≠ stored.head then
        return .error "durable log head does not match its entries"
      let logStart := transport.logStart seed
      -- The split the transport names; `openState` binds it (the checkpoint's own height plus
      -- the entries after it must reach the head) and `openLoaded` checks the count below it.
      let height := (stored.checkpoint.map (·.height)).getD 0
      let suffix := stored.entries.drop height
      match openState key rootBytes logStart seed (stored.checkpoint.map (·.bytes)) suffix stored.head with
      | .error message => return .error message
      | .ok opened =>
          lap s!"fast-forward (checkpoint {opened.base.1}, {suffix.length} entries after it)"
          match openLoaded key rootBytes logStart seed (stored.entries.take height) suffix opened with
          | .error message => return .error message
          | .ok ⟨loaded, chains, chainsExact⟩ =>
              lap "gate and rebuild"
              return .ok ⟨loaded, chains, chainsExact, opened.baseWorld⟩

/-- The open path (`loadChained` without the chain prefixes or the base World). -/
def load (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Loaded rootBytes)) := do
  return (← loadChained transport rootBytes).map (·.loaded)

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
  /-- The image after an append carries the tag the append wrote: its MAC is the
  one the append computed under the key, so the head's authentication is not
  lost (`Loaded.headTag`). -/
  headTagExact : next.headTag = some entry.tag

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

/-- The executor at the loaded engine, as `DurableCheckpoint.prepare` reads it
(`Loaded.prepare_eq`): the journal guard off the engine's index, preflight off
its tables. -/
def Loaded.prepare {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) :
    Sum (Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent)
      (Outcome rootBytes) :=
  match intent.checkBounds with
  | .error reason => .inr (.rejected reason)
  | .ok () =>
    match executed : loaded.engine.execute rootBytes intent with
    | .accepted next =>
        have spec : DurableDataIntent.execute .complete loaded.snapshot intent = .accepted next := by
          rw [loaded.snapshotExact, ← DurableEngine.Engine.execute_eq]; exact executed
        .inl ⟨next, spec, resume_append rootBytes loaded.image loaded.baseHeight loaded.base
          loaded.snapshot next intent loaded.withinLog loaded.resumed spec⟩
    | outcome => .inr outcome

/-- **Refinement**: the engine's prepare is the protocol's at the loaded snapshot. -/
theorem Loaded.prepare_eq {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) :
    loaded.prepare intent = DurableCheckpoint.prepare loaded.image loaded.baseHeight loaded.base
      loaded.snapshot
      loaded.withinLog loaded.resumed intent := by
  have same := DurableEngine.Engine.execute_eq rootBytes loaded.engine intent
  rw [← loaded.snapshotExact] at same
  unfold Loaded.prepare DurableCheckpoint.prepare
  generalize intent.checkBounds = bounds
  cases bounds with
  | error reason => rfl
  | ok unit =>
      cases unit
      dsimp only
      split <;> split <;> simp_all <;> rename_i notAccepted <;> exact notAccepted _ same.symm

/-- The prepared successor: same checkpoint base, one more record installed
into the engine, the chain advanced by it, and the root cache advanced by its
slot writes (one path each). -/
def Loaded.extend {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent) :
    Loaded rootBytes :=
  let record := IntentRecord.ofIntent intent
  let chain := chainStep loaded.chain record
  let engine := loaded.engine.install rootBytes intent
  have nextEq : ready.next = engine.view rootBytes := by
    rw [DurableReceiver.execute_accepted_install _ _ _ ready.executed, loaded.snapshotExact,
      DurableEngine.Engine.view_install]
  let roots := loaded.rootsExact.advance (recordSlots (loaded.height + 1) chain record)
    (by
      simpa only [Loaded.height_eq] using
        (entriesOf_step loaded.image loaded.snapshot (engine.view rootBytes) intent loaded.chain chain
          (nextEq ▸ ready.executed)))
  -- The served root after this record (`Loaded.worldRoot` of the result), kept
  -- as its receipt root.
  let served := roots.1.root
  ⟨loaded.image.append intent, loaded.baseHeight, loaded.base, engine, engine.view rootBytes, rfl,
    by simp only [Image.accepted_append, List.length_append]
       exact Nat.le_add_right_of_le loaded.withinLog,
    nextEq ▸ ready.resumed, loaded.logStart, chain,
    by show chainStep loaded.chain record = _
       rw [loaded.chainExact]; simp [chainAfter, Image.accepted_append, List.foldl_append, record],
    roots.1, roots.2,
    loaded.index.admit (loaded.height + 1) record,
    by rw [loaded.indexExact]
       simpa only [Loaded.height_eq, Image.accepted_append] using
         (PresenceIndex.ofRecords_snoc loaded.image.accepted record).symm,
    loaded.links.admit (loaded.height + 1) record,
    by rw [loaded.linksExact]
       simpa only [Loaded.height_eq, Image.accepted_append] using
         (LinkIndex.ofRecords_snoc loaded.image.accepted record).symm,
    loaded.ids.admit record,
    by unfold Image.append
       exact SessionIndex.CellIds.admit_exact loaded.idsExact record,
    loaded.txs.admitAt loaded.height record,
    by simpa only [Loaded.height_eq, Image.accepted_append] using
         SessionIndex.TxIndex.admitAt_exact loaded.txsExact record,
    loaded.spentAt.admitAt IntentRecord.nullifiers loaded.height record,
    by simpa only [Loaded.height_eq, Image.accepted_append] using
         SessionIndex.KeyIndex.admitAt_exact loaded.spentAtExact record,
    loaded.writesAt.admitAt (fun record => record.writes.map DataWrite.cellId)
      loaded.height record,
    by simpa only [Loaded.height_eq, Image.accepted_append] using
         SessionIndex.KeyIndex.admitAt_exact loaded.writesAtExact record,
    loaded.rootLog.push (some served),
    by simp [Image.append, loaded.rootLogSize],
    loaded.frontier.map fun frontier => DurableHistory.Frontier.push frontier
      (leafDigest (loaded.height + 1) (recordFrame.encode record) chain served),
    none,
    loaded.track.advance (nextEq ▸ ready.executed) (by simp [Image.append]),
    loaded.chainLog.push chain,
    by rw [Array.toList_push, loaded.chainLogExact, Image.accepted_append,
         DurableLogTags.chainPrefixes_snoc, ← loaded.chainExact]⟩

/-- **The extended snapshot is the executor's next snapshot.** -/
theorem Loaded.extend_snapshot {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent) :
    (loaded.extend ready).snapshot = ready.next := by
  show (loaded.engine.install rootBytes intent).view rootBytes = ready.next
  rw [DurableReceiver.execute_accepted_install _ _ _ ready.executed, loaded.snapshotExact,
    DurableEngine.Engine.view_install]

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
#assert_axioms Loaded.extend_snapshot
#assert_axioms Loaded.prepare_eq
#assert_axioms Loaded.extend_rootLog_prefix

/-- Materialize the head as a fresh base (no replayed suffix), as a cold
open of a checkpoint at the head would. The engine and the root cache carry
over unchanged: resuming the head's own state at the head IS the head's
snapshot (`DurableEngine.resume_rebase`), so nothing is replayed or rebuilt. -/
def Loaded.rebase {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Loaded rootBytes :=
  ⟨loaded.image, loaded.height,
    ⟨loaded.image.seed.absentBytes, loaded.cells, loaded.snapshot.model.available⟩,
    loaded.engine, loaded.snapshot, loaded.snapshotExact, by rw [Loaded.height_eq],
    by exact DurableEngine.resume_rebase loaded.resumed,
    loaded.logStart,
    loaded.chain, loaded.chainExact, loaded.roots, loaded.rootsExact,
    loaded.index, loaded.indexExact, loaded.links, loaded.linksExact,
    loaded.ids, loaded.idsExact, loaded.txs, loaded.txsExact,
    loaded.spentAt, loaded.spentAtExact, loaded.writesAt, loaded.writesAtExact,
    loaded.rootLog, loaded.rootLogSize, loaded.frontier, loaded.headTag, loaded.track,
    loaded.chainLog, loaded.chainLogExact⟩

/-- The rebased base is the head's state (`State.ofSnapshot`). -/
theorem Loaded.rebase_base {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.rebase.base = State.ofSnapshot loaded.image loaded.snapshot := rfl

/-- Rebasing keeps the image, the log start and the snapshot. -/
theorem Loaded.rebase_image {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.rebase.image = loaded.image ∧ loaded.rebase.logStart = loaded.logStart ∧
      loaded.rebase.snapshot = loaded.snapshot :=
  ⟨rfl, rfl, rfl⟩

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
  Image.ofAccepted loaded.image.seed (loaded.image.accepted.take height)

/-- A loaded image from its parts: the resumed snapshot, a full root cache, every
index built over the image, and the World at the head (`world`, decided against the
resumed snapshot). The physical checks (chain, tags, seal) are the caller's;
`chainExact` and `rootLogSize` carry what they established. -/
def Loaded.build {rootBytes : List UInt8 → Digest} (image : Image) (baseHeight : Nat)
    (base : State) (withinLog : baseHeight ≤ image.accepted.length) (logStart chain : Digest)
    (chainExact : chain = chainAfter logStart image.accepted)
    (rootLog : Array (Option Digest)) (rootLogSize : rootLog.size = image.accepted.length)
    (chainLog : Array Digest) (chainLogExact : chainLog.toList = chainPrefixes logStart image.accepted)
    (world : Except String HostRefinesWorld.DWorld) :
    Except String {built : Loaded rootBytes // built.image = image ∧ built.logStart = logStart ∧
      built.baseHeight = baseHeight ∧ built.base = base} :=
  match found : DurableEngine.resumeEngine rootBytes image baseHeight base with
  | none => .error "durable image journal does not replay through the canonical executor"
  | some engine =>
      let built := RootCache.build (entriesOf image (engine.view rootBytes) chain)
      .ok ⟨⟨image, baseHeight, base, engine, engine.view rootBytes, rfl, withinLog,
        DurableEngine.resume_of_resumeEngine found,
        logStart, chain, chainExact,
        built.1, built.2,
        PresenceIndex.ofRecords image.accepted, rfl, LinkIndex.ofRecords image.accepted, rfl,
        SessionIndex.CellIds.ofImage image, SessionIndex.CellIds.ofImage_exact image,
        SessionIndex.TxIndex.ofRecords image.accepted,
        SessionIndex.TxIndex.ofRecords_exact image.accepted,
        SessionIndex.KeyIndex.ofRecords IntentRecord.nullifiers image.accepted,
        SessionIndex.KeyIndex.ofRecords_exact IntentRecord.nullifiers image.accepted,
        SessionIndex.KeyIndex.ofRecords (fun record => record.writes.map DataWrite.cellId) image.accepted,
        SessionIndex.KeyIndex.ofRecords_exact (fun record => record.writes.map DataWrite.cellId)
          image.accepted,
        rootLog, rootLogSize, none, none,
        trackOfWorld rootBytes image (DurableEngine.resume_of_resumeEngine found) world,
        chainLog, chainLogExact⟩, rfl, rfl, rfl, rfl⟩

/-- **The opening cut at `height`, at or above its own base** (CONSENT-STORE): the
base the Store's open used (its MAC-verified checkpoint, or the seed) is kept, the
records from the base to `height` are replayed through the executor and folded as
turns from the base's World (`Chained.baseWorld`), the chain is read off the open's
verified prefixes and the stored roots are the verified tags'. Nothing below the base
is executed or folded: the cost is the records between the base and `height`, at most
the checkpoint interval when `height` is the head's checkpoint or an anchor above it. -/
def Chained.cutAbove {rootBytes : List UInt8 → Digest} (opened : Chained rootBytes) (height : Nat) :
    Except String {cut : Loaded rootBytes //
      cut.image = Image.ofAccepted opened.loaded.image.seed (opened.loaded.image.accepted.take height) ∧
        cut.logStart = opened.loaded.logStart ∧ cut.baseHeight = opened.loaded.baseHeight ∧
        cut.base = opened.loaded.base} :=
  let loaded := opened.loaded
  if within : height ≤ loaded.height then
    have withinAccepted : height ≤ loaded.image.accepted.length := by
      simpa only [Loaded.height_eq] using within
    if based : loaded.baseHeight ≤ height then
      match found : opened.chains[height]? with
      | none => .error "durable chain prefix unavailable at the requested height"
      | some chain =>
          have chainExact : chain = chainAfter loaded.logStart (loaded.image.accepted.take height) := by
            rw [opened.chainsExact, DurableLogTags.chainPrefixes_getElem? _ _ _ withinAccepted] at found
            exact (Option.some.inj found).symm
          have sized : (loaded.rootLog.extract 0 height).size =
              (loaded.image.accepted.take height).length := by
            simp [Array.size_extract, loaded.rootLogSize, List.length_take, Nat.min_eq_left withinAccepted]
          have cutLog : (loaded.chainLog.toList.take (height + 1)).toArray.toList =
              chainPrefixes loaded.logStart (loaded.image.accepted.take height) := by
            rw [List.toList_toArray, loaded.chainLogExact,
              DurableLogTags.chainPrefixes_take _ _ _ withinAccepted]
          let between := (loaded.image.accepted.take height).drop loaded.baseHeight
          Loaded.build (Image.ofAccepted loaded.image.seed (loaded.image.accepted.take height)) loaded.baseHeight
            loaded.base (by simpa only [Image.accepted_ofAccepted, List.length_take,
              Nat.min_eq_left withinAccepted] using based)
            loaded.logStart chain (by simpa only [Image.accepted_ofAccepted] using chainExact)
            (loaded.rootLog.extract 0 height) (by simpa only [Image.accepted_ofAccepted] using sized)
            (loaded.chainLog.toList.take (height + 1)).toArray
            (by simpa only [Image.accepted_ofAccepted] using cutLog)
            (opened.baseWorld.bind fun w => foldRecords rootBytes w loaded.baseHeight between)
    else .error s!"height {height} is below the Store's base at {loaded.baseHeight}"
  else .error "durable log is shorter than the requested height"

/-- **A kept checkpoint below the open's base**, as the past-read path admits
it. The Store keeps every checkpoint (`durable-checkpoint-at` returns the latest
at or below a height); this one opened under the Store's key — exact decode,
key id, recomputed world root, MAC (`openSealed`) — at a positive height inside
the log, and its sealed world root is the root the MAC-verified log tag at its
height carries (`rootLog`). What no check can establish is that the host sealed
the right state; that is the honesty premise every checkpoint carries
(`resume_sound`, `Loaded.atPrefixFrom_kept`). -/
structure Loaded.Kept {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) where
  /-- The Store's MAC key the checkpoint opened under. -/
  key : MacKey
  height : Nat
  state : State
  positive : 0 < height
  within : height ≤ loaded.image.accepted.length
  authentic : ∃ bytes body, openSealed key rootBytes bytes = .ok body ∧ body.height = height ∧
    body.state = state ∧
    loaded.rootLog[height - 1]? = some (some (DurableCheckpointCodec.worldRoot rootBytes body))

/-- **The state at log height `height`.** At or above the open's base: that base
plus the records after it up to `height` (D2's resume, on the cut image). Below
it: the kept checkpoint `kept` plus the records after it, when `kept` sits at or
below `height`; otherwise the genesis fold of the prefix. The Store keeps every
record since the seed and every checkpoint, so the retention floor is height 0
and a past read replays at most the distance to the nearest kept checkpoint. -/
def Loaded.atPrefixFrom {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (kept : Option (loaded.Kept)) (height : Nat) : Option (DataSnapshot rootBytes) :=
  if loaded.baseHeight ≤ height then
    resume rootBytes (loaded.prefixImage height) loaded.baseHeight loaded.base
  else
    match kept with
    | some base =>
        if base.height ≤ height then
          resume rootBytes (loaded.prefixImage height) base.height base.state
        else resume rootBytes (loaded.prefixImage height) 0 (State.ofSeed loaded.image.seed)
    | none => resume rootBytes (loaded.prefixImage height) 0 (State.ofSeed loaded.image.seed)

/-- The base a past read at `height` resumes from, as `atPrefixFrom` picks it:
the open's own base, else the kept checkpoint, else the seed. -/
def Loaded.pastBase {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (kept : Option (loaded.Kept)) (height : Nat) : Nat × State :=
  if loaded.baseHeight ≤ height then (loaded.baseHeight, loaded.base)
  else
    match kept with
    | some base =>
        if base.height ≤ height then (base.height, base.state)
        else (0, State.ofSeed loaded.image.seed)
    | none => (0, State.ofSeed loaded.image.seed)

theorem Loaded.atPrefixFrom_pastBase {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (kept : Option (loaded.Kept)) (height : Nat) :
    loaded.atPrefixFrom kept height = resume rootBytes (loaded.prefixImage height)
      (loaded.pastBase kept height).1 (loaded.pastBase kept height).2 := by
  unfold Loaded.atPrefixFrom Loaded.pastBase
  split
  · rfl
  · cases kept with
    | none => rfl
    | some base =>
        simp only
        split <;> rfl

theorem Loaded.pastBase_le {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (kept : Option (loaded.Kept)) (height : Nat) :
    (loaded.pastBase kept height).1 ≤ height ∧
      (loaded.pastBase kept height).1 ≤ loaded.image.accepted.length := by
  unfold Loaded.pastBase
  split
  · rename_i above
    exact ⟨above, loaded.withinLog⟩
  · cases kept with
    | none => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    | some base =>
        simp only
        split
        · rename_i above
          exact ⟨above, base.within⟩
        · exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- A checkpoint state's admissibility at a past height, off the session's
indexes: duplicate-freedom in one pass, every identifier the seed's or written
below `height` (`writesAt`), no pass over the prefix's records. -/
def Loaded.admissibleAt {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (height : Nat) (state : State) : Bool :=
  let seeded : Std.HashSet CellId := Std.HashSet.ofList (loaded.image.seed.cells.map Prod.fst)
  DurableEngine.nodupFast (state.cells.map Prod.fst) &&
    decide (state.absentBytes = loaded.image.seed.absentBytes) &&
    (state.cells.map Prod.fst).all fun cellId =>
      seeded.contains cellId || (loaded.writesAt[cellId]?).any fun first => decide (first < height)

theorem Loaded.admissibleAt_iff {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (height : Nat) (state : State) :
    loaded.admissibleAt height state = true ↔ state.Admissible (loaded.prefixImage height) := by
  unfold Loaded.admissibleAt State.Admissible Image.cellIds Loaded.prefixImage
  simp only [Bool.and_eq_true, DurableEngine.nodupFast_iff, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem,
    SessionIndex.KeyIndex.below_eq loaded.writesAtExact, List.mem_eraseDups, List.mem_append,
    Image.ofAccepted_seed, Image.accepted_ofAccepted, and_assoc]

/-- The engine at a past base height `height`: the base state's cells, the
prefix's nullifiers and transaction ids read off the session's first-index
tables (`spentAt`, `txs`) against `height`. Nothing walks the prefix. -/
def Loaded.engineAt {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) (height : Nat)
    (state : State) : DurableEngine.Engine rootBytes :=
  DurableEngine.Engine.ofIndexed rootBytes state loaded.image.accepted height
    (fun nullifier => (loaded.spentAt[nullifier]?).any fun first => decide (first < height))
    (SessionIndex.KeyIndex.below_eq loaded.spentAtExact height)
    (fun transactionId => (loaded.txs[transactionId]?).any fun first => decide (first < height))
    (SessionIndex.TxIndex.below_eq loaded.txsExact height)

/-- **The past read, compiled**: from the base `pastBase` picks, the indexed
engine replays only the records between that base and `height`. -/
def Loaded.atPrefixFast {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (kept : Option (loaded.Kept)) (height : Nat) : Option (DataSnapshot rootBytes) :=
  let start := loaded.pastBase kept height
  if loaded.admissibleAt height start.2 then
    ((loaded.engineAt start.1 start.2).replay rootBytes
      ((loaded.image.accepted.drop start.1).take (height - start.1))).map
        (DurableEngine.Engine.view rootBytes)
  else none

/-- **Refinement, compiled**: every past read the host runs is `atPrefixFast`;
the replacement is this theorem, not a trusted `implemented_by`. -/
@[csimp] theorem Loaded.atPrefixFrom_eq_atPrefixFast :
    @Loaded.atPrefixFrom = @Loaded.atPrefixFast := by
  funext rootBytes loaded kept height
  rw [Loaded.atPrefixFrom_pastBase]
  unfold Loaded.atPrefixFast
  have bounded := loaded.pastBase_le kept height
  generalize loaded.pastBase kept height = start at bounded ⊢
  obtain ⟨base, state⟩ := start
  simp only at bounded ⊢
  unfold resume
  by_cases admissible : state.Admissible (loaded.prefixImage height)
  · rw [if_pos admissible, if_pos ((loaded.admissibleAt_iff height state).mpr admissible)]
    have takeEq : (loaded.prefixImage height).accepted.take base = loaded.image.accepted.take base := by
      simp only [Loaded.prefixImage, Image.accepted_ofAccepted]
      rw [List.take_take, Nat.min_eq_left bounded.1]
    have dropEq : (loaded.prefixImage height).accepted.drop base =
        (loaded.image.accepted.drop base).take (height - base) := by
      simp only [Loaded.prefixImage, Image.accepted_ofAccepted]
      rw [List.drop_take]
    rw [takeEq, dropEq, ← DurableEngine.Engine.view_ofIndexed rootBytes state loaded.image.accepted base
      _ (SessionIndex.KeyIndex.below_eq loaded.spentAtExact base)
      _ (SessionIndex.TxIndex.below_eq loaded.txsExact base), DurableEngine.Engine.replay_view]
    rfl
  · rw [if_neg admissible,
      if_neg (fun fast => admissible ((loaded.admissibleAt_iff height state).mp fast))]

#assert_axioms Loaded.atPrefixFrom_eq_atPrefixFast

theorem Loaded.prefixImage_current {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.prefixImage loaded.height = loaded.image := by
  unfold prefixImage
  rw [Loaded.height_eq, List.take_length, Image.ofAccepted_accepted]

/-- **At the current height the past read is the current state**, whatever
kept checkpoint was supplied: the same snapshot every current read decodes. -/
theorem Loaded.atPrefixFrom_current {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) (kept : Option (loaded.Kept)) :
    loaded.atPrefixFrom kept loaded.height = some loaded.snapshot := by
  unfold atPrefixFrom
  rw [if_pos (show loaded.baseHeight ≤ loaded.height from loaded.withinLog), loaded.prefixImage_current]
  exact loaded.resumed

/-- **Below the base with no kept checkpoint in use, the past read is the
genesis fold of the prefix** — unconditionally. (With `kept := none` this is
the pre-kept `atPrefix_below` statement verbatim.) -/
theorem Loaded.atPrefixFrom_below {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) (kept : Option (loaded.Kept)) {height : Nat}
    (below : height < loaded.baseHeight)
    (unused : ∀ base ∈ kept, height < base.height) :
    loaded.atPrefixFrom kept height = (loaded.prefixImage height).restore rootBytes := by
  unfold atPrefixFrom
  rw [if_neg (by omega)]
  cases kept with
  | none => exact resume_genesis rootBytes (loaded.prefixImage height)
  | some base =>
      simp only
      rw [if_neg (Nat.not_le_of_lt (unused base rfl))]
      exact resume_genesis rootBytes (loaded.prefixImage height)

/-- **Below the base, from a kept checkpoint, the past read is the genesis fold
of the prefix** for an honest checkpoint (`resume_sound`'s premises, the same
ones `atPrefixFrom_from_checkpoint` carries for the open's own base). -/
theorem Loaded.atPrefixFrom_kept {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) (base : loaded.Kept) {height : Nat}
    (below : height < loaded.baseHeight) (above : base.height ≤ height)
    (atBase : DataSnapshot rootBytes)
    (seedValid : (loaded.image.seed.cells.map Prod.fst).Nodup)
    (stateValid : base.state.Admissible (loaded.prefixImage height))
    (prefixReplay : replay rootBytes (loaded.image.seed.snapshot rootBytes)
      ((loaded.image.accepted.take height).take base.height) = some atBase)
    (honest : base.state.snapshot rootBytes
      ((loaded.image.accepted.take height).take base.height) = atBase) :
    loaded.atPrefixFrom (some base) height = (loaded.prefixImage height).restore rootBytes := by
  unfold atPrefixFrom
  rw [if_neg (by omega)]
  simp only
  rw [if_pos above]
  exact resume_sound rootBytes (loaded.prefixImage height) base.height base.state atBase
    seedValid stateValid
    (by simpa only [Loaded.prefixImage, Image.ofAccepted_seed, Image.accepted_ofAccepted] using prefixReplay)
    (by simpa only [Loaded.prefixImage, Image.accepted_ofAccepted] using honest)

/-- **At or above the base the past read is the base plus the suffix fold** —
and, for an honest base (`resume_sound`'s premises), the genesis fold of the
prefix. The kept checkpoint plays no part. -/
theorem Loaded.atPrefixFrom_from_checkpoint {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) (kept : Option (loaded.Kept)) {height : Nat}
    (above : loaded.baseHeight ≤ height)
    (atBase : DataSnapshot rootBytes)
    (seedValid : (loaded.image.seed.cells.map Prod.fst).Nodup)
    (stateValid : loaded.base.Admissible (loaded.prefixImage height))
    (prefixReplay : replay rootBytes (loaded.image.seed.snapshot rootBytes)
      ((loaded.image.accepted.take height).take loaded.baseHeight) = some atBase)
    (honest : loaded.base.snapshot rootBytes
      ((loaded.image.accepted.take height).take loaded.baseHeight) = atBase) :
    loaded.atPrefixFrom kept height = (loaded.prefixImage height).restore rootBytes := by
  unfold atPrefixFrom
  rw [if_pos above]
  exact resume_sound rootBytes (loaded.prefixImage height) loaded.baseHeight loaded.base atBase
    seedValid stateValid
    (by simpa only [Loaded.prefixImage, Image.ofAccepted_seed, Image.accepted_ofAccepted] using prefixReplay)
    (by simpa only [Loaded.prefixImage, Image.accepted_ofAccepted] using honest)

/-- The kept checkpoint a past read at `height` resumes from: the Store's
latest checkpoint at or below `height`, admitted as a `Kept` (every check named
in its doc), or `none` when the open's own base already serves `height`, when
no checkpoint is kept at or below it, or when it is too low to beat genesis.
A checkpoint that fails a check refuses the read by name; it is never replaced
by a genesis fold. -/
def Loaded.keptAt {rootBytes : List UInt8 → Digest} (transport : Transport) (key : MacKey)
    (loaded : Loaded rootBytes) (height : Nat) : IO (Except String (Option (loaded.Kept))) := do
  if loaded.baseHeight ≤ height ∨ height < transport.checkpointEvery then return .ok none
  match ← transport.checkpointAt height with
  | .error message => return .error s!"past state unavailable: the kept checkpoint read failed: {message}"
  | .ok none => return .ok none
  | .ok (some checkpoint) =>
      -- the same cached open as the full open's checkpoint (loadChained): the tree evaluated once
      match opened : openSealedWith (α := CheckpointRoots rootBytes) key rootBytes checkpoint.bytes
          (fun _ => RootCache.build _) (fun _ built => built.1.root)
          (fun _ => RootCache.ofEntries_root _) with
      | .error reason =>
          return .error s!"past state refused: the kept checkpoint at {checkpoint.height} does not open ({repr reason})"
      | .ok ⟨body, built⟩ =>
          let root := built.1.root
          if body.height ≠ checkpoint.height ∨ body.height > height then
            return .error s!"past state refused: the kept checkpoint at {checkpoint.height} names height {body.height}"
          if positive : 0 < body.height then
            if within : body.height ≤ loaded.height then
              if logged : loaded.rootLog[body.height - 1]? = some (some root) then
                have plain := openSealedWith_ok opened
                return .ok (some ⟨key, body.height, body.state, positive, within,
                  ⟨checkpoint.bytes, body, plain.1, rfl, rfl, by rw [← plain.2]; exact logged⟩⟩)
              else
                return .error s!"past state refused: the kept checkpoint at {body.height} differs from its log entry's root"
            else return .error s!"past state refused: the kept checkpoint at {body.height} is beyond the log"
          else return .ok none

#assert_axioms Loaded.atPrefixFrom_current
#assert_axioms Loaded.atPrefixFrom_below
#assert_axioms Loaded.atPrefixFrom_kept
#assert_axioms Loaded.atPrefixFrom_from_checkpoint

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

/-- The fold's World's system store a session holds: what every sealer puts in a v4 body. -/
def Loaded.system {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    Option (Minidregg.Theory.Store.Store Kernel.WorldSystemCodec.DSys) :=
  loaded.track.world?.map (·.system)

/-- **A checkpoint sealed from the cached root is the specification seal**,
byte for byte: the served root is the world root of the checkpoint body. -/
theorem sealCheckpoint_uses_cached_root {rootBytes : List UInt8 → Digest} (key : MacKey)
    (loaded : Loaded rootBytes) (frontier : List (Nat × Digest)) (indexRoot : Digest) :
    sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.system loaded.worldRoot =
      sealCheckpoint key rootBytes loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.system := by
  apply sealAt_eq_sealCheckpoint
  rw [loaded.worldRoot_eq, DurableCheckpointCodec.worldRoot, stateEntries_ofSnapshot]

/-- The sealed root is `Kernel.WorldRoot`'s deployed root of the sealed body. -/
theorem cachedSeal_root {rootBytes : List UInt8 → Digest} (key : MacKey)
    (loaded : Loaded rootBytes) (frontier : List (Nat × Digest)) (indexRoot : Digest) :
    (sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.system loaded.worldRoot).root =
      DurableCheckpointCodec.worldRoot rootBytes
        (sealAt key loaded.image.accepted.length loaded.chain frontier indexRoot
          (State.ofSnapshot loaded.image loaded.snapshot) loaded.system loaded.worldRoot).body := by
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
/-- info: 'Minidregg.Compiler.DurableReceiverIO.stateEntries_ofSnapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stateEntries_ofSnapshot

/-- Seal and store a checkpoint of the head. A failed write loses nothing (the
log is complete); the caller then keeps its old base. -/
def storeCheckpoint (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (indexRoot : Digest) : IO Bool := do
  let .ok key ← transport.key | return false
  let some frontier := loaded.frontier | return false
  let sealed := sealAt key loaded.height loaded.chain frontier indexRoot
    (State.ofSnapshot loaded.image loaded.snapshot) loaded.system loaded.worldRoot
  match ← transport.putCheckpoint loaded.height (checkpointFrame.encode sealed) with
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
    loaded.height % transport.checkpointEvery == 0

/-- After a stored checkpoint, rebase on it; otherwise keep the base. -/
def afterCheckpoint {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (stored : Bool) : Loaded rootBytes :=
  if stored then loaded.rebase else loaded

theorem afterCheckpoint_headTag {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (stored : Bool) : (afterCheckpoint loaded stored).headTag = loaded.headTag := by
  unfold afterCheckpoint
  split <;> rfl

theorem afterCheckpoint_image {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (stored : Bool) : (afterCheckpoint loaded stored).image = loaded.image := by
  unfold afterCheckpoint
  split
  · exact (Loaded.rebase_image _).1
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
        match current.prepare intent with
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
        (sealAt key height current.chain frontier indexRoot state current.system current.worldRoot)
      let full := checkpointFrame.encode
        (sealCheckpoint key rootBytes height current.chain frontier indexRoot state current.system)
      let atHeight := stored.checkpoint.bind fun checkpoint =>
        if checkpoint.height = height then some checkpoint.bytes else none
      return .ok (cached, full, atHeight)


/-- The head entry's tag: the one the image was read with, else the Store's
entry at the head height. Unverified bytes: every caller checks them with
`DurableHistory.Head.verify` before relying on them. An image the session
extended by its own append carries no tag (`Loaded.extend`). -/
def Loaded.headTagOrRead {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) : IO (Except String (List UInt8)) := do
  match loaded.headTag with
  | some tag => return .ok tag
  | none =>
      match ← transport.read loaded.height false with
      | .ok (some stored) =>
          match stored.entries.head? with
          | some entry => return .ok entry.tag
          | none => return .error "durable head entry missing"
      | .ok none => return .error "durable store is not initialized"
      | .error message => return .error message

/-- The index root after this image's head: carried by the head entry's tag,
whose MAC is verified for the head's height, chain and accumulator frontier
(`DurableHistory.Head.verify`). The empty log's is the empty map's. -/
def Loaded.headIndexRoot {rootBytes : List UInt8 → Digest} (transport : Transport) (key : MacKey)
    (loaded : Loaded rootBytes) : IO (Except String Digest) := do
  let height := loaded.height
  if height = 0 then return .ok DurableIndex.emptyDigest
  let some frontier := loaded.frontier
    | return .error "this opening carries no accumulator frontier (it was not read from the Store)"
  let tag ← match ← loaded.headTagOrRead transport with
    | .ok tag => pure tag
    | .error message => return .error message
  match DurableHistory.Head.verify (DurableHistory.StoreIdentity.ofOpen key loaded.logStart) height tag
      loaded.chain frontier with
  | .ok head => return .ok head.indexRoot
  | .error refusal => return .error refusal.message

/-- **A checkpoint at the head, on demand** (HOT-PATH §2(h) item 6): the Host's `checkpoint`
verb (before a journey template is saved) and a session's clean end. The same sealer as the due
cadence (`storeCheckpoint`), at whatever height the head is, so a Store restored from it
fast-forwards zero records. Returns the sealed height (0: an empty log seals nothing). -/
def sealHead (transport : Transport) (rootBytes : List UInt8 → Digest) : IO (Except String Nat) := do
  let loaded ← match ← load transport rootBytes with
    | .error message => return .error message
    | .ok loaded => pure loaded
  let height := loaded.height
  if height = 0 then return .ok 0
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let indexRoot ← match ← loaded.headIndexRoot transport key with
    | .error message => return .error message
    | .ok root => pure root
  if ← storeCheckpoint transport rootBytes loaded indexRoot then return .ok height
  else return .error "the checkpoint at the head was not stored"

/-- The index rows on the paths of `keys` and beside them (each prefix's
sibling, which a delete's collapse reads), at or below `height`, down to `depth`
bits (520: every prefix). Untrusted: every opening or reveal built from them is
verified against the authenticated index root, so a path cut short opens to
nothing and refuses (`withIndexRows` then reads every prefix). -/
def indexRows (transport : Transport) (height : Nat) (keys : List DurableIndex.IndexKey)
    (depth : Nat := 520) : IO (Except String (List Bool → Option DurableIndex.Row)) := do
  let mut seen : Std.HashSet (List UInt8) := {}
  let mut requested : Array (Nat × List UInt8) := #[]
  let mut paths : Std.HashMap (List UInt8) (List Bool) := {}
  for k in keys do
    for path in DurableIndex.readPrefixes k depth do
      let rowKey := DurableIndex.rowKey path
      unless seen.contains rowKey do
        seen := seen.insert rowKey
        paths := paths.insert rowKey path
        requested := requested.push (DurableIndex.indexSpace, rowKey)
  -- The Store answers at most 65536 node keys per request: read in chunks.
  let mut found : Std.HashMap (List Bool) DurableIndex.Row := {}
  for chunk in requested.toList.toChunks 60000 do
    match ← transport.history ⟨height, [], chunk⟩ with
    | .error message => return .error message
    | .ok read =>
        found := read.nodes.foldl (init := found) fun map node =>
          match paths.get? node.2.1 with
          | none => map
          | some path =>
              match node.2.2 with
              | none => map
              | some (_, value) =>
                  match DurableIndex.rowStream.toLawful.decode value with
                  | some row => map.insert path row
                  | none => map
  let rows := found
  return .ok fun path => rows.get? path

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


/-- The node rows an append writes: the accumulator nodes it completes
(space 1) and the index rows its changes write (space 3). -/
def appendNodes (accumulator : List ((Nat × Nat) × Digest))
    (index : List (List Bool × DurableIndex.Row)) : List NodeWrite :=
  accumulator.map (fun node => ⟨DurableIndex.accumulatorSpace,
      DurableHistory.nodeKey node.1.1 node.1.2, Tower256ConcreteBackend.digestStream.encode node.2⟩) ++
    index.map fun row => ⟨DurableIndex.indexSpace, DurableIndex.rowKey row.1,
      DurableIndex.rowStream.encode row.2⟩


end Minidregg.Compiler.DurableReceiverIO
