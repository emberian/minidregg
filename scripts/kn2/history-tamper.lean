/- KN2-STORE-OPEN executed check: a tampered NON-head record (height 20 of 41) is
refused BY NAME at use, through the Store-backed Reader, while its neighbours
and the head still verify; a tampered accumulator node on its path is refused
the same way; the open itself refuses the tampered Store naming height 20.

Usage: lake env lean --run scripts/kn2/history-tamper.lean STORE-HELPER
(the helper binary from native/hyperdocument-link-sqlite-store, schema v5).
Tampering edits the SQLite file directly with python3's sqlite3 module (the
helper never rewrites an entry). -/
import Compiler.DurableStoreAudit
import Compiler.DurableServed
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO
open Minidregg.Compiler.DurableHistoryReader

namespace HistoryTamper

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def seed : Seed := { absentBytes := [], cells := [(⟨1⟩, [1]), (⟨3⟩, [0])], available := fun _ => 1000 }

def nullifier (number : Nat) : StableNullifier := ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

/-- Record `number` moves cell 3 from `[number - 1]` to `[number]`. -/
def step (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨1000 + number⟩
  writes := [⟨⟨3⟩, rootBytes [UInt8.ofNat (number - 1)], rootBytes [UInt8.ofNat number], [UInt8.ofNat number]⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
  subject := none
  postRootsBound := by simp
  guardsReadOnly := by simp

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL history tamper: {label}")

def sql (database : System.FilePath) (statement : String) : IO Unit := do
  let output ← IO.Process.output { cmd := "python3", args := #["-c",
    s!"import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute(sys.argv[2]); c.commit()",
    database.toString, statement] }
  unless output.exitCode == 0 do throw (IO.userError s!"FAIL sql: {output.stderr}")

def expectRefusedAt (label : String) (height : Nat) (result : Except DurableHistory.Refusal α) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"FAIL history tamper: {label} verified")
  | .error refusal =>
      IO.println s!"refused as expected ({label}): {refusal.message}"
      require s!"{label} names height {height}" (refusal == .notIncluded height)

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  for number in List.range' 1 41 do
    match ← receive transport rootBytes (step number) 3 with
    | .confirmed _ _ => pure ()
    | .rejected reason => throw (IO.userError s!"FAIL commit {number}: rejected {repr reason}")
    | .unavailable detail => throw (IO.userError s!"FAIL commit {number}: unavailable {detail}")
    | .uncertain detail => throw (IO.userError s!"FAIL commit {number}: uncertain {detail}")
    | .contention => throw (IO.userError s!"FAIL commit {number}: contention")
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL open: {detail}")
  require "41 records" (loaded.height == 41)
  let database := directory / "store" / "forward-link.sqlite3"
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  -- Honest reads: every height, the transaction index, the spent set, a past state.
  for height in List.range' 1 41 do
    match ← reader.atHeight height with
    | .ok read =>
        require s!"record {height} is the record appended there"
          (read.record.transactionId == (⟨1000 + height⟩ : Digest))
    | .error refusal => throw (IO.userError s!"FAIL honest read {height}: {refusal.message}")
  match ← reader.byTx ⟨1020⟩ with
  | .ok (.present found) =>
      require "byTx finds height 20" (found.height == 20)
  | .ok (.absent _) => throw (IO.userError "FAIL byTx: accepted transaction reported absent")
  | .error refusal => throw (IO.userError s!"FAIL byTx: {refusal.message}")
  match ← reader.byTx ⟨5555⟩ with
  | .ok (.absent _) => pure ()
  | .ok (.present _) => throw (IO.userError "FAIL byTx: unknown transaction reported present")
  | .error refusal => throw (IO.userError s!"FAIL byTx absent: {refusal.message}")
  match ← reader.spent (nullifier 33) with
  | .ok answer =>
      require "nullifier 33 spent at height 33" (answer.value == some 33)
  | .error refusal => throw (IO.userError s!"FAIL spent: {refusal.message}")
  match ← reader.spent (nullifier 77) with
  | .ok answer =>
      require "nullifier 77 unspent" (answer.value == none)
  | .error refusal => throw (IO.userError s!"FAIL unspent: {refusal.message}")
  match ← reader.stateAt 30 with
  | .ok state =>
      require "state at 30 holds cell 3 = [30], from the checkpoint at 16"
        (state.snapshot.canonicalBytes ⟨3⟩ == [30] && state.baseHeight == 16 && state.reads.length == 14)
  | .error refusal => throw (IO.userError s!"FAIL stateAt: {refusal.message}")
  IO.println "honest: heights 1..41, byTx present/absent, spent present/absent, stateAt 30 all verified"
  -- The light opening of the head: the checkpoint at 32 and records 33..41 only.
  match ← DurableServed.openHead transport rootBytes with
  | .error detail => throw (IO.userError s!"FAIL light open: {detail}")
  | .ok opening =>
      require "light open: head 41, from the checkpoint at 32"
        (opening.head.height == 41 && opening.baseHeight == 32 && opening.served.height == 41)
      require "light open serves the full open's world root" (opening.served.worldRoot == loaded.worldRoot)
      require "light open serves the full open's chain" (opening.served.chain == loaded.chain)
      require "light open serves the full open's cells" (opening.served.cellIds == loaded.cellIds)
      require "light open: cell 3 holds [41]" (opening.served.canonicalBytes ⟨3⟩ == [41])
      IO.println "light open: head 41 from the checkpoint at 32; root, chain and cells equal the full open's"
  match ← DurableStoreAudit.audit transport rootBytes with
  | .ok report => IO.println report.line
  | .error message => throw (IO.userError s!"FAIL store audit on the honest Store: {message}")
  -- The light receive: record 42 on the light opening; the full open then agrees on the root.
  let opening ← match ← DurableServed.openHead transport rootBytes with
    | .ok opening => pure opening
    | .error detail => throw (IO.userError s!"FAIL light open: {detail}")
  let next ← match ← DurableServed.receiveServed transport rootBytes opening (step 42) with
    | .appended _ next _ _ _ => pure next
    | .rejected reason => throw (IO.userError s!"FAIL light receive 42: rejected {repr reason}")
    | .replayed _ => throw (IO.userError "FAIL light receive 42: replayed")
    | .contention => throw (IO.userError "FAIL light receive 42: contention")
    | .unavailable detail => throw (IO.userError s!"FAIL light receive 42: {detail}")
    | .uncertain detail => throw (IO.userError s!"FAIL light receive 42: uncertain {detail}")
  let full ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL full open after the light receive: {detail}")
  require "light receive: head 42, the full open's root and cell bytes"
    (next.head.height == 42 && full.height == 42 && next.served.worldRoot == full.worldRoot &&
      next.served.canonicalBytes ⟨3⟩ == [42])
  -- A session's refresh: the opening at 41 extended by the entry another writer appended (42),
  -- verified as the open verifies; it serves what the writer's opening serves.
  match ← opening.extend transport rootBytes with
  | .error detail => throw (IO.userError s!"FAIL light refresh: {detail}")
  | .ok refreshed =>
      require "light refresh: head 42, the writer's root, chain and cells"
        (refreshed.head.height == 42 && refreshed.served.worldRoot == next.served.worldRoot &&
          refreshed.served.chain == next.served.chain && refreshed.served.cellIds == next.served.cellIds)
      match ← refreshed.extend transport rootBytes with
      | .ok again => require "light refresh with nothing new is the same head" (again.head.height == 42)
      | .error detail => throw (IO.userError s!"FAIL light refresh (nothing new): {detail}")
      -- Record 43 on the refreshed opening, then ONE BYTE of record 42 (no longer the head, which the
      -- native anchor pins): the refresh of the opening at 41 refuses naming 42; then restored.
      match ← DurableServed.receiveServed transport rootBytes refreshed (step 43) with
      | .appended .. => pure ()
      | _ => throw (IO.userError "FAIL light receive 43 on the refreshed opening")
      sql database "CREATE TABLE kn2_saved AS SELECT height, record FROM durable_log WHERE height = 42"
      sql database "UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = 42"
      match ← opening.extend transport rootBytes with
      | .ok _ => throw (IO.userError "FAIL light refresh accepted a tampered record at 42")
      | .error detail =>
          IO.println s!"light refresh refused the tampered record: {detail}"
          require "light refresh names height 42" ((detail.splitOn "height 42").length > 1)
      sql database "UPDATE durable_log SET record = (SELECT record FROM kn2_saved) WHERE height = 42"
      sql database "DROP TABLE kn2_saved"
      require "record 42 restored" ((← opening.extend transport rootBytes).toOption.isSome)
  -- The same transaction again: the footprint finds it (verified at use), the executor replays it.
  match ← DurableServed.receiveServed transport rootBytes next (step 42) with
  | .replayed _ => pure ()
  | _ => throw (IO.userError "FAIL light receive: a repeated transaction was not replayed")
  -- A new transaction spending nullifier 5 (consumed at height 5, below the checkpoint at 32): the
  -- spent map answers it consumed; the light receive refuses it (no silent "absent").
  let reuse : DataIntent rootBytes := { step 43 with nullifiers := [nullifier 5] }
  match ← DurableServed.receiveServed transport rootBytes next reuse with
  | .rejected reason =>
      IO.println s!"light receive refused a nullifier consumed at height 5: {repr reason}"
      require "the refusal is alreadyConsumed" (reason == .durable .alreadyConsumed)
  | _ => throw (IO.userError "FAIL light receive accepted a nullifier consumed below its checkpoint")
  -- The declaration is load-bearing: on a view that did NOT declare the nullifier, the executor
  -- sees it unconsumed and would accept the reuse (what `Family.covers` forbids a port to do).
  match ← (next.reader transport rootBytes).footprint ⟨[], []⟩ with
  | .error refusal => throw (IO.userError s!"FAIL empty footprint: {refusal.message}")
  | .ok undeclared =>
      match DurableDataIntent.execute .complete (next.served.viewAt undeclared) reuse with
      | .accepted _ => IO.println "control: an undeclared nullifier reads unconsumed on a view (the hazard the declaration closes)"
      | _ => throw (IO.userError "FAIL control: the undeclared view refused the reuse; the control no longer distinguishes")
  IO.println "light receive: record 42 appended (root equals the full open's), its repeat replayed, a pre-checkpoint nullifier refused"
  -- TAMPER 1: one byte of the record at height 20 (a non-head record).
  sql database "UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = 20"
  expectRefusedAt "tampered record at height 20 of 41" 20 (← reader.atHeight 20)
  require "height 19 still verifies" ((← reader.atHeight 19).toOption.isSome)
  require "height 21 still verifies" ((← reader.atHeight 21).toOption.isSome)
  require "the head still verifies" ((← reader.atHeight 41).toOption.isSome)
  match ← reader.byTx ⟨1020⟩ with
  | .error refusal => require "byTx through the tampered record refuses at 20" (refusal == .notIncluded 20)
  | .ok _ => throw (IO.userError "FAIL byTx returned the tampered record")
  match ← DurableStoreAudit.audit transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL store audit accepted the tampered Store")
  | .error message =>
      IO.println s!"store audit refused the tampered Store: {message}"
      require "store audit names height 20" ((message.splitOn "height 20").length > 1)
  match ← load transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL the open accepted the tampered Store")
  | .error detail =>
      IO.println s!"open refused the tampered Store: {detail}"
      require "open names height 20" ((detail.splitOn "height 20").length > 1)
  -- The light open reads nothing below the checkpoint (32): record 20 is verified at use.
  match ← DurableServed.openHead transport rootBytes with
  | .ok _ => IO.println "light open: record 20 lies below the checkpoint; it is refused at use (above), not read at open"
  | .error detail => throw (IO.userError s!"FAIL light open read below its checkpoint: {detail}")
  -- TAMPER 2: an accumulator node on height 19's path (the leaf node at level 0, end 20).
  sql database "UPDATE durable_node SET value = zeroblob(length(value)) WHERE space = 1 AND height = 20"
  expectRefusedAt "tampered accumulator node beside height 19" 19 (← reader.atHeight 19)
  -- TAMPER 3a: the spent-map rows record 34 wrote (after the checkpoint). A spent read at use
  -- refuses; the light open never trusts those rows (it re-derives every spent root after its
  -- checkpoint from the checkpoint's version and the records) and still opens.
  sql database "UPDATE durable_node SET value = zeroblob(length(value)) WHERE space = 2 AND height = 34"
  match ← reader.spent (nullifier 34) with
  | .ok _ => throw (IO.userError "FAIL a spent read through a forged row at 34 verified")
  | .error refusal => IO.println s!"refused as expected (spent read through a forged row at 34): {refusal.message}"
  match ← DurableServed.openHead transport rootBytes with
  | .ok _ => IO.println "light open: rows written after its checkpoint are re-derived, not trusted"
  | .error detail => throw (IO.userError s!"FAIL light open trusted a row written after its checkpoint: {detail}")
  -- TAMPER 3b: the spent map's rows at the checkpoint's version (written by record 32): the
  -- light open's re-derivation starts from them and refuses at the first record after it.
  sql database "UPDATE durable_node SET value = zeroblob(length(value)) WHERE space = 2 AND height = 32"
  match ← DurableServed.openHead transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL light open accepted forged spent rows at its checkpoint")
  | .error detail =>
      IO.println s!"light open refused the forged checkpoint-version spent rows: {detail}"
      require "light open names height 33" ((detail.splitOn "height 33").length > 1)
  sql database "DELETE FROM durable_node WHERE space = 2 AND (height = 32 OR height = 34)"
  -- TAMPER 4: one byte of the record at height 37 (after the checkpoint): refused at open by name.
  sql database "UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = 37"
  match ← DurableServed.openHead transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL light open accepted a tampered record at 37")
  | .error detail =>
      IO.println s!"light open refused the tampered suffix record: {detail}"
      require "light open names height 37" ((detail.splitOn "height 37").length > 1)
  -- EPOCH: a Store born with the previous accumulator component (checkpoint v2,
  -- before the consumed list left the checkpoint) is refused at open, by name.
  let olderLabel := "state-key/tagged-v4;schema-refs/v5;" ++ DurableCheckpointCodec.logTagLabel ++
    ";history/mmr-v1;spent/trie-v1"
  let olderFrame := DurableCheckpointCodec.seedFrameName ++ [2] ++ olderLabel.toUTF8.toList
  let olderSeed := (Tower256ConcreteBackend.StreamCodec.product Tower256ConcreteBackend.bytesStream
    DurableReceiverCodec.seedStream).encode (olderFrame, seed)
  let hex := String.join (olderSeed.map fun b =>
    let digits := String.ofList (Nat.toDigits 16 b.toNat)
    if digits.length = 1 then "0" ++ digits else digits)
  sql database s!"UPDATE durable_seed SET bytes = X'{hex}'"
  match ← load transport rootBytes with
  | .ok _ => throw (IO.userError "FAIL an older-epoch Store opened")
  | .error detail =>
      IO.println s!"older epoch refused: {detail}"
      require "the refusal names the accumulator component"
        ((detail.splitOn "history accumulator: Store history/mmr-v1;spent/trie-v1").length > 1)
  IO.println "PASS history tamper: a non-head record and an accumulator node, each refused by name at use"

end HistoryTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (HistoryTamper.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/history-tamper.lean STORE-HELPER")
