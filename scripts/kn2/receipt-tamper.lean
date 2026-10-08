/- KN2 PORT-D executed check: op 102 (receipt by transaction) reads through the
Store-backed Reader. `NativeHost.receiptByTransactionRead` is the handler core
(`receiptByTransactionVia` only builds the Reader from the open). Over a 41-record
Store:
* an accepted transaction answers `some` receipt whose height is its 1-based
  position and whose world root is the root bound into the verified log leaf;
* an unknown transaction answers `none`, by the spent map's verified absence;
* after ONE byte of the record at height 20 (a non-head record) is altered, the
  same lookup answers a REFUSAL naming height 20 (reason operationRejected,
  detail = `DurableHistory.Refusal.message`), never `none` ("unknown transaction")
  and never the stale receipt;
* a neighbour (height 21) still answers.

Usage: lake env lean --run scripts/kn2/receipt-tamper.lean STORE-HELPER
(the helper binary from native/hyperdocument-link-sqlite-store, schema v5). -/
import Kernel.NativeHost
import Compiler.DurableStoreAudit
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO

namespace ReceiptTamper

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def seed : Seed := { absentBytes := [], cells := [(⟨1⟩, [1]), (⟨3⟩, [0])], available := fun _ => 1000 }

def nullifier (number : Nat) : StableNullifier := ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

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
  unless condition do throw (IO.userError s!"FAIL receipt tamper: {label}")

def sql (database : System.FilePath) (statement : String) : IO Unit := do
  let output ← IO.Process.output { cmd := "python3", args := #["-c",
    s!"import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute(sys.argv[2]); c.commit()",
    database.toString, statement] }
  unless output.exitCode == 0 do throw (IO.userError s!"FAIL sql: {output.stderr}")

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
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  -- Honest: a present transaction, its receipt, and a verified absence.
  match ← NativeHost.receiptByTransactionRead reader ⟨1020⟩ with
  | .ok (some receipt) =>
      require "receipt names transaction 1020" (receipt.transactionId == (⟨1020⟩ : Digest))
      require "receipt height is the 1-based position 20" (receipt.acceptedCount == 20)
      match ← reader.atHeight 20 with
      | .ok read => require "receipt root is the verified leaf's world root" (receipt.worldRoot == read.verified.root)
      | .error refusal => throw (IO.userError s!"FAIL honest read: {refusal.message}")
  | .ok none => throw (IO.userError "FAIL accepted transaction answered unknown")
  | .error refusal => throw (IO.userError s!"FAIL honest lookup refused: {refusal.detail}")
  match ← NativeHost.receiptByTransactionRead reader ⟨5555⟩ with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError "FAIL unknown transaction answered a receipt")
  | .error refusal => throw (IO.userError s!"FAIL absent lookup refused: {refusal.detail}")
  IO.println "honest: receipt of 1020 at height 20 with the verified root; 5555 verified absent"
  -- PLANT: one byte of the record at height 20.
  sql (directory / "store" / "forward-link.sqlite3")
    "UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = 20"
  match ← NativeHost.receiptByTransactionRead reader ⟨1020⟩ with
  | .ok none => throw (IO.userError "FAIL tampered record answered unknown transaction")
  | .ok (some _) => throw (IO.userError "FAIL tampered record answered a receipt")
  | .error refusal =>
      IO.println s!"refused as expected: {refusal.detail}"
      require "the refusal is the named history refusal at 20"
        (refusal == NativeHost.historyRefusal (.notIncluded 20))
      require "the detail names height 20"
        ((refusal.detail.splitOn "durable history record refused at height 20").length > 1)
  match ← NativeHost.receiptByTransactionRead reader ⟨1021⟩ with
  | .ok (some receipt) => require "neighbour still answers" (receipt.acceptedCount == 21)
  | _ => throw (IO.userError "FAIL neighbour at 21 does not answer")
  IO.println "PASS receipt tamper: op-102 core refuses a tampered record by name, never unknown/stale"

end ReceiptTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (ReceiptTamper.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/receipt-tamper.lean STORE-HELPER")
