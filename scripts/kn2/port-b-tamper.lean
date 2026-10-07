/- KN2 PORT-B executed check: the past-state ports read through `Reader.stateAt`
and `NativeHistorySelection.foldRange`.

Honest: the continuity witness built from `stateAt` (ReceiptContinuityIO.pastWitness)
equals, root, chain and siblings, the one the retired genesis-replay path
(`Loaded.atPrefix` + `entriesOf` over the cut image) computed, at height 30 (base:
the checkpoint at 16 + 14 records) and 10 (base: genesis) and at the head 41; the
windowed fold sees all 41 records.
Planted faults (each must refuse BY NAME, never answer a stale or absent value):
 1. one byte of the record at height 20 (strictly below the requested 30, above the
    checkpoint at 16): `stateAt 30` and the fold over 1..41 refuse naming height 20;
 2. one byte of the checkpoint at 32: `stateAt 41` refuses ("checkpoint refused").

Usage: lake env lean --run scripts/kn2/port-b-tamper.lean STORE-HELPER -/
import Compiler.DurableStoreAudit
import Compiler.ReceiptContinuityIO
import Kernel.NativeHistorySelection
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
    | _ => throw (IO.userError s!"FAIL commit {number}")
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL open: {detail}")
  require "41 records" (loaded.height == 41)
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  -- Honest: the stateAt witness equals the retired genesis-replay witness.
  for height in [10, 30, 41] do
    let past ← match ← reader.stateAt height with
      | .ok past => pure past
      | .error refusal => throw (IO.userError s!"FAIL honest stateAt {height}: {refusal.message}")
    let witness := ReceiptContinuityIO.pastWitness past
    let some snapshot := loaded.atPrefix height
      | throw (IO.userError s!"FAIL genesis replay at {height}")
    let image := loaded.prefixImage height
    let chain := DurableCheckpointCodec.chainAfter loaded.logStart image.accepted
    let roots := RootCache.ofEntries (entriesOf image snapshot chain)
    require s!"witness at {height}: root equals the genesis-replay root" (witness.point.worldRoot == roots.root)
    require s!"witness at {height}: chain equals the genesis-replay chain" (witness.chain == chain)
    require s!"witness at {height}: siblings equal the genesis-replay siblings"
      (witness.siblings == ReceiptContinuityIO.cachedSiblings roots.tree (WorldRoot.deployed.ix .system))
    require s!"witness at {height}: height" (witness.point.height == height)
  match ← NativeHistorySelection.foldRange reader 1 41 (0 : Nat) fun (count : Nat) window => (Except.ok (count + window.length) : Except String Nat) with
  | .ok count => require "the windowed fold sees 41 records" (count == 41)
  | .error detail => throw (IO.userError s!"FAIL honest fold: {detail}")
  IO.println "honest: pastWitness at 10/30/41 equals the genesis-replay witness; fold sees 41 records"
  let database := directory / "store" / "forward-link.sqlite3"
  -- PLANT 1: the record at height 20.
  sql database "UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = 20"
  expectRefusedAt "stateAt 30 over the tampered record at 20" 20 (← reader.stateAt 30)
  match ← NativeHistorySelection.foldRange reader 1 41 (0 : Nat) fun (count : Nat) window => (Except.ok (count + window.length) : Except String Nat) with
  | .ok _ => throw (IO.userError "FAIL the fold read through the tampered record")
  | .error detail =>
      IO.println s!"refused as expected (fold over 1..41): {detail}"
      require "fold names height 20" ((detail.splitOn "height 20").length > 1)
  -- PLANT 2: the checkpoint at 32 (stateAt 41 resumes from it).
  sql database "UPDATE durable_checkpoint SET bytes = CAST(substr(bytes,1,length(bytes)-1) || X'FF' AS BLOB) WHERE height = 32"
  match ← reader.stateAt 41 with
  | .ok _ => throw (IO.userError "FAIL stateAt resumed from a tampered checkpoint")
  | .error refusal =>
      IO.println s!"refused as expected (tampered checkpoint at 32): {refusal.message}"
      require "checkpoint refused" ((refusal.message.splitOn "checkpoint refused").length > 1)
  IO.println "PASS port-b tamper: a record below the requested height and the checkpoint, each refused by name"

end HistoryTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (HistoryTamper.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/port-b-tamper.lean STORE-HELPER")
