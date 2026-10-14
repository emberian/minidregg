/- STATE-AT executed check: a past read `at h` below the opening's base resumes
from the nearest KEPT checkpoint at or below h (`Loaded.keptAt` +
`Loaded.atPrefixFrom`), equals the genesis fold there, and a kept checkpoint that
fails a check refuses the read BY NAME — never a silent genesis fallback, never a
wrong state. Plants, each restored before the next:
  (1) a flipped MAC byte in the kept checkpoint at 16  -> "does not open (badMac)";
  (2) the checkpoint at 32's bytes stored under row 16  -> "names height 32";
  (3) a checkpoint at 16 sealed WITH the Store key over a state whose cell 3 is
      wrong (a dishonest key holder) -> "differs from its log entry's root".
Controls: at 10 (no kept checkpoint at or below) is the genesis fold; at 35 (above
the base 32) needs no kept checkpoint; the honest kept read equals the genesis fold.

Usage: lake env lean --run scripts/kn2/past-checkpoint-tamper.lean STORE-HELPER -/
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

namespace PastCheckpointTamper

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
  unless condition do throw (IO.userError s!"FAIL past-checkpoint tamper: {label}")

def sql (database : System.FilePath) (statement : String) : IO Unit := do
  let output ← IO.Process.output { cmd := "python3", args := #["-c",
    s!"import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute(sys.argv[2]); c.commit()",
    database.toString, statement] }
  unless output.exitCode == 0 do throw (IO.userError s!"FAIL sql: {output.stderr}")

def cell3 (snapshot : Option (DataSnapshot rootBytes)) : Option (List UInt8) :=
  snapshot.map (·.canonicalBytes ⟨3⟩)

def expectRefused (label needle : String) (result : Except String α) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"FAIL past-checkpoint tamper: {label} was admitted")
  | .error message =>
      IO.println s!"refused as expected ({label}): {message}"
      require s!"{label} names '{needle}'" ((message.splitOn needle).length > 1)

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
  require "41 records, base 32" (loaded.height == 41 && loaded.baseHeight == 32)
  let key ← match ← transport.key with
    | .ok key => pure key
    | .error detail => throw (IO.userError detail)
  let database := directory / "store" / "forward-link.sqlite3"
  -- Controls.
  match ← loaded.keptAt transport key 10 with
  | .ok none => require "at 10 is the genesis fold" (cell3 (loaded.atPrefixFrom none 10) == some [10])
  | _ => throw (IO.userError "FAIL at 10 found a kept checkpoint")
  match ← loaded.keptAt transport key 35 with
  | .ok none => require "at 35 from the opening's base" (cell3 (loaded.atPrefixFrom none 35) == some [35])
  | _ => throw (IO.userError "FAIL at 35 read a kept checkpoint")
  -- The honest kept read.
  let honest ← match ← loaded.keptAt transport key 20 with
    | .ok (some base) => pure base
    | .ok none => throw (IO.userError "FAIL at 20 found no kept checkpoint")
    | .error detail => throw (IO.userError s!"FAIL at 20: {detail}")
  require "at 20 resumes from the checkpoint at 16" (honest.height == 16)
  require "at 20 from the kept checkpoint = the genesis fold = [20]"
    (cell3 (loaded.atPrefixFrom (some honest) 20) == some [20] &&
      cell3 (loaded.atPrefixFrom none 20) == some [20])
  IO.println "at 10 genesis, at 35 from the base 32, at 20 from the kept checkpoint at 16: all equal the genesis fold"
  sql database "CREATE TABLE kn2_saved AS SELECT bytes FROM durable_checkpoint WHERE height = 16"
  let restore := "UPDATE durable_checkpoint SET bytes = (SELECT bytes FROM kn2_saved) WHERE height = 16"
  -- (1) a flipped MAC byte.
  sql database "UPDATE durable_checkpoint SET bytes = CAST(substr(bytes,1,length(bytes)-1) || X'FF' AS BLOB) WHERE height = 16"
  expectRefused "flipped MAC byte" "kept checkpoint at 16 does not open" (← loaded.keptAt transport key 20)
  sql database restore
  -- (2) another height's checkpoint under row 16.
  sql database "UPDATE durable_checkpoint SET bytes = (SELECT bytes FROM durable_checkpoint WHERE height = 32) WHERE height = 16"
  expectRefused "checkpoint 32 under row 16" "names height 32" (← loaded.keptAt transport key 20)
  sql database restore
  -- (3) a dishonest seal under the Store's own key.
  let some stored := (← transport.checkpointAt 16).toOption.join
    | throw (IO.userError "FAIL no checkpoint at 16")
  let body ← match DurableCheckpointCodec.openSealed key rootBytes stored.bytes with
    | .ok body => pure body
    | .error _ => throw (IO.userError "FAIL the honest checkpoint does not open")
  let wrong := { body.state with cells := body.state.cells.map fun cell =>
    if cell.1 == ⟨3⟩ then (cell.1, [99]) else cell }
  let forged := DurableCheckpointCodec.checkpointFrame.encode
    (DurableCheckpointCodec.sealCheckpoint key rootBytes 16 body.chain body.frontier body.indexRoot wrong)
  match ← transport.putCheckpoint 16 forged with
  | .ok () => pure ()
  | .error detail => throw (IO.userError s!"FAIL put: {detail}")
  expectRefused "dishonest seal under the key" "differs from its log entry's root" (← loaded.keptAt transport key 20)
  sql database restore
  match ← loaded.keptAt transport key 20 with
  | .ok (some base) => require "restored: kept again" (base.height == 16)
  | _ => throw (IO.userError "FAIL restored checkpoint not admitted")
  IO.println "PASS past-checkpoint tamper: three plants refused by name; honest reads equal the genesis fold"

end PastCheckpointTamper

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir fun directory => PastCheckpointTamper.run binary directory
  | _ => throw (IO.userError "usage: past-checkpoint-tamper STORE-HELPER")
