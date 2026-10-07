/- KN2-STORE-OPEN executed check: a tampered NON-head record (height 20 of 41) is
refused BY NAME at use, through the Store-backed Reader, while its neighbours
and the head still verify; a tampered accumulator node on its path is refused
the same way; the open itself refuses the tampered Store naming height 20.

Usage: lake env lean --run scripts/kn2/history-tamper.lean STORE-HELPER
(the helper binary from native/hyperdocument-link-sqlite-store, schema v5).
Tampering edits the SQLite file directly with python3's sqlite3 module (the
helper never rewrites an entry). -/
import Compiler.DurableStoreAudit
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
  match ← DurableStoreAudit.audit transport rootBytes with
  | .ok report => IO.println report.line
  | .error message => throw (IO.userError s!"FAIL store audit on the honest Store: {message}")
  -- TAMPER 1: one byte of the record at height 20 (a non-head record).
  let database := directory / "store" / "forward-link.sqlite3"
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
  -- TAMPER 2: an accumulator node on height 19's path (the leaf node at level 0, end 20).
  sql database "UPDATE durable_node SET value = zeroblob(length(value)) WHERE space = 1 AND height = 20"
  expectRefusedAt "tampered accumulator node beside height 19" 19 (← reader.atHeight 19)
  IO.println "PASS history tamper: a non-head record and an accumulator node, each refused by name at use"

end HistoryTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (HistoryTamper.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/history-tamper.lean STORE-HELPER")
