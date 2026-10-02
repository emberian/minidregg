/-
# Compiler.DurableReceiverIO — the host's durable log, checkpoints and receiving loop

The store is a seed, an append-only log of accepted records, and MAC'd
checkpoints (`Compiler.DurableCheckpointCodec`). Lean decodes, chains, MACs,
resumes and executes; the native helper stores opaque bytes, appends entry
`h + 1` only while the head is `h`, and assigns no meaning to anything.

* **Open** (`load`): recompute the log chain over every stored record, open
  the latest checkpoint (key id, recomputed world root, MAC, chain value),
  verify the head entry's tag, then `DurableCheckpoint.resume` — materialize
  the checkpoint and replay only the records after it. No signed ingress is
  re-admitted here; that is the operator `audit` (`NativeHostReplay.verifyLoaded`).
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
import Kernel.PresenceIndex

namespace Minidregg.Compiler.DurableReceiverIO

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.DurableCheckpointCodec

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
  /-- Append at the given height iff the head is one below it. -/
  append : Nat → Entry → IO CasObservation
  putCheckpoint : Nat → List UInt8 → IO (Except String Unit)
  initializeSeed : List UInt8 → IO CasObservation
  key : IO (Except String MacKey)
  checkpointEvery : Nat
  /-- The log chain's start for a seed (the host: `NativeHostCodec.logRoot0`
  of its domain and semantics), so one chain is both MAC'd and rooted. -/
  logStart : Seed → Digest

structure NativeConfig where
  binary : System.FilePath
  root : System.FilePath
  /-- The Store's 32-byte MAC key file (mode 0600, generated at bootstrap). -/
  key : System.FilePath
  checkpointEvery : Nat := 64

/-- One Store call, through the binary's long-lived `serve` helper
(`NativeCoprocess.output`: the one-shot call's exact output, no fork of the Host). -/
def runNative (config : NativeConfig) (arguments : Array String) : IO IO.Process.Output :=
  NativeCoprocess.output config.binary.toString arguments

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
def NativeConfig.append (config : NativeConfig) (height : Nat) (entry : Entry)
    (crashAt : Option String := none) : IO CasObservation :=
  try
    IO.FS.withTempDir fun directory => do
      let recordPath := directory / "record.bin"
      let tagPath := directory / "tag.bin"
      IO.FS.writeBinFile recordPath entry.record.toByteArray
      IO.FS.writeBinFile tagPath entry.tag.toByteArray
      let arguments := match crashAt with
        | none => #["durable-append", config.root.toString, toString height,
            recordPath.toString, tagPath.toString]
        | some phase => #["durable-append-crash", config.root.toString, toString height,
            recordPath.toString, tagPath.toString, phase]
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

def NativeConfig.transport (config : NativeConfig) (logStart : Seed → Digest) : Transport :=
  ⟨config.read, fun height entry => config.append height entry, config.putCheckpoint,
    config.initialize, config.readKey, config.checkpointEvery, logStart⟩

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
        PresenceIndex.ofRecords image.accepted, rfl⟩

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

private def decodeRecords : List Entry → Except String (List IntentRecord)
  | [] => .ok []
  | entry :: rest => do
      let some record := recordFrame.decode entry.record
        | throw "noncanonical durable log record"
      return record :: (← decodeRecords rest)

/-- Chain values after each prefix: element `i` is the chain after `i` records. -/
private def chainPrefixes (start : Digest) (records : List IntentRecord) : Array Digest :=
  records.foldl (fun acc record => acc.push (chainStep (acc.back?.getD start) record)) #[start]

private theorem chainPrefixes_foldl_back (start : Digest) :
    ∀ (records : List IntentRecord) (acc : Array Digest),
      (records.foldl (fun acc record => acc.push (chainStep (acc.back?.getD start) record))
          acc).back?.getD start = chainAfter (acc.back?.getD start) records
  | [], _ => by simp [chainAfter]
  | record :: rest, acc => by
      rw [List.foldl_cons, chainPrefixes_foldl_back start rest]
      simp [chainAfter, Array.back?_push]

/-- The last prefix is the head chain, so `load` hashes the log once, not twice. -/
private theorem chainPrefixes_back (start : Digest) (records : List IntentRecord) :
    (chainPrefixes start records).back?.getD start = chainAfter start records := by
  unfold chainPrefixes
  rw [chainPrefixes_foldl_back]
  simp

/-- The single open path. Every check refuses; nothing reinterprets. -/
def load (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Loaded rootBytes)) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  match ← transport.read 1 true with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      let some seedBytes := stored.seed | return .error "durable seed missing"
      let some seed := seedFrame.decode seedBytes | return .error "noncanonical durable seed"
      let records ← match decodeRecords stored.entries with
        | .error message => return .error message
        | .ok records => pure records
      let logStart := transport.logStart seed
      let chains := chainPrefixes logStart records
      let headChain := chains.back?.getD logStart
      let (baseHeight, base) ← match stored.checkpoint with
        | none => pure (0, State.ofSeed seed)
        | some checkpoint =>
            match openSealed key rootBytes checkpoint.bytes with
            | .error reason => return .error s!"checkpoint refused: {repr reason}"
            | .ok body =>
                if body.height ≠ checkpoint.height ∨ body.height > stored.head then
                  return .error "checkpoint height does not match the log"
                if body.chain ≠ chains.getD body.height ⟨0⟩ then
                  return .error "checkpoint does not match the log chain"
                pure (body.height, body.state)
      if stored.head > baseHeight then
        match stored.entries.getLast? with
        | none => return .error "durable log head missing"
        | some last =>
            if last.tag ≠ entryTag key stored.head headChain then
              return .error "durable log head tag refused"
      let image : Image := ⟨seed, records⟩
      if within : baseHeight ≤ image.accepted.length then
        match resumed : resume rootBytes image baseHeight base with
        | none => return .error "durable log suffix does not replay through the canonical executor"
        | some snapshot =>
            return .ok ⟨image, baseHeight, base, snapshot, within, resumed, logStart, headChain,
              chainPrefixes_back logStart records,
              RootCache.ofEntries (entriesOf image snapshot headChain),
              RootsExact.ofEntries (entriesOf image snapshot headChain),
              PresenceIndex.ofRecords image.accepted, rfl⟩
      else return .error "checkpoint beyond the log head"

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
  ⟨loaded.image.append intent, loaded.baseHeight, loaded.base, ready.next,
    by simp only [Image.append, List.length_append]; exact Nat.le_add_right_of_le loaded.withinLog,
    ready.resumed, loaded.logStart, chain,
    by show chainStep loaded.chain record = _
       rw [loaded.chainExact]; simp [chainAfter, Image.append, List.foldl_append, record],
    roots.1, roots.2,
    loaded.index.admit (loaded.image.accepted.length + 1) record,
    by rw [loaded.indexExact]
       exact (PresenceIndex.ofRecords_snoc loaded.image.accepted record).symm⟩

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
        loaded.index, loaded.indexExact⟩

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

/-! ## A past height (K-HISTORY-READ) -/

/-- The image cut at log height `height`: the seed and the first `height` records. -/
def Loaded.prefixImage {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (height : Nat) : Image :=
  ⟨loaded.image.seed, loaded.image.accepted.take height⟩

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
    (loaded : Loaded rootBytes) :
    sealAt key loaded.image.accepted.length loaded.chain
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot =
      sealCheckpoint key rootBytes loaded.image.accepted.length loaded.chain
        (State.ofSnapshot loaded.image loaded.snapshot) := by
  apply sealAt_eq_sealCheckpoint
  rw [loaded.worldRoot_eq, DurableCheckpointCodec.worldRoot, stateEntries_ofSnapshot]

/-- The sealed root is `Kernel.WorldRoot`'s deployed root of the sealed body. -/
theorem cachedSeal_root {rootBytes : List UInt8 → Digest} (key : MacKey)
    (loaded : Loaded rootBytes) :
    (sealAt key loaded.image.accepted.length loaded.chain
        (State.ofSnapshot loaded.image loaded.snapshot) loaded.worldRoot).root =
      DurableCheckpointCodec.worldRoot rootBytes
        (sealAt key loaded.image.accepted.length loaded.chain
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
    (loaded : Loaded rootBytes) : IO Bool := do
  let .ok key ← transport.key | return false
  let sealed := sealAt key loaded.image.accepted.length loaded.chain
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
      let records ← match decodeRecords stored.entries with
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
      let cached := checkpointFrame.encode (sealAt key height current.chain state current.worldRoot)
      let full := checkpointFrame.encode (sealCheckpoint key rootBytes height current.chain state)
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
      let .ok key ← transport.key
        | return (false, .ordinary (.unavailable "checkpoint MAC key unavailable"))
      let height := loaded.image.accepted.length + 1
      let recordBytes := recordFrame.encode (IntentRecord.ofIntent intent)
      let chain := loaded.chainAfterIntent intent
      let entry : Entry := ⟨recordBytes, entryTag key height chain⟩
      let confirm := fun (installed : Bool) (kind : Confirmation) => do
        match ← readBackEntry transport height with
        | .error message =>
            return (false, DetailedResult.ordinary (.uncertain s!"append attempted; readback unavailable: {message}"))
        | .ok none =>
            return (false, .ordinary (.uncertain "append attempted; entry absent on readback"))
        | .ok (some stored) =>
            if stored = entry then
              let extended := loaded.extend ready
              let checkpointStored ←
                if checkpointDue transport extended then storeCheckpoint transport rootBytes extended
                else pure false
              return (installed, .exact kind
                ⟨afterCheckpoint extended checkpointStored,
                  afterCheckpoint_image extended checkpointStored, entry, rfl⟩)
            else return (false, .ordinary .contention)
      match ← transport.append height entry with
      | .installed => confirm true .installed
      | .alreadyPresent => confirm false .installed
      | .conflict => return (false, .ordinary .contention)
      | .uncertain _ => confirm false .recoveredAfterUncertainResponse

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

/-- Extend a live loaded image by entries a concurrent writer appended after
it: the chain must continue, the new head's tag must verify, and every new
record must be accepted by the shared executor in order. -/
def extendFrom (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) : IO (Except String (Loaded rootBytes)) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let height := loaded.image.accepted.length
  match ← transport.read (height + 1) false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      if stored.head = height then return .ok loaded
      if stored.head < height then return .error "durable log shrank beneath the session"
      let records ← match decodeRecords stored.entries with
        | .error message => return .error message
        | .ok records => pure records
      let chain := chainAfter loaded.chain records
      let some last := stored.entries.getLast? | return .error "durable log head missing"
      if last.tag ≠ entryTag key stored.head chain then
        return .error "durable log head tag refused"
      let mut current := loaded
      for record in records do
        let some intent := record.bind? rootBytes
          | return .error "durable log record does not bind its roots"
        match prepare current.image current.baseHeight current.base current.snapshot
            current.withinLog current.resumed intent with
        | .inl ready => current := current.extend ready
        | .inr _ => return .error "durable log suffix does not replay through the canonical executor"
      if current.chain ≠ chain then return .error "durable log chain mismatch"
      if current.image.accepted.length ≥ current.baseHeight + 2 * max 1 transport.checkpointEvery then
        match current.rebase with
        | some rebased => return .ok rebased
        | none => return .error "rebase at the head does not resume through the canonical executor"
      return .ok current

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

end Minidregg.Compiler.DurableReceiverIO
