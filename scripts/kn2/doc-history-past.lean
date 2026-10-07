/- KN2 doc-history evidence (cv 01a0f60e-2dcf). `queryResultWith` consumes two
inputs besides the served snapshot: the past state after k records (`at`) and the
accepted records above a cursor (`since`). `queryResult` is `queryResultWith` over
`Past.ofLoaded` (the loaded image's own), so equal inputs give byte-identical output.
This probe, over an N-record Store:
 1. DIFFERENTIAL: at every stride-th height (stride max 1 (N/150)) and the last two the Reader's `stateAt` snapshot and the loaded
    image's `atPrefix` agree on every cell's canonical bytes; `NativeHost.readWindows`
    from cursor c equals `image.accepted` from c, for several c.
 2. PLANT: one byte of the record at N-5 altered; `stateAt (N-1)` and `readWindows`
    through it are REFUSED naming height N-5 (not absent, not stale).
 3. TIMING: the old `atPrefix` vs `stateAt` at 20 heights below the last checkpoint.
Usage: lake env lean --run scripts/kn2/doc-history-past.lean STORE-HELPER N -/
import Kernel.NativeHost
import Compiler.DurableStoreAudit
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO

namespace DocHistoryPast

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


def run (binary : System.FilePath) (n : Nat) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  for number in List.range' 1 n do
    match ← receive transport rootBytes (step number) 3 with
    | .confirmed _ _ => pure ()
    | _ => throw (IO.userError s!"FAIL commit {number}")
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"FAIL open: {detail}")
  require s!"{n} records" (loaded.height == n)
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .ok reader => pure reader
    | .error detail => throw (IO.userError s!"FAIL reader: {detail}")
  -- 1. differential
  let mut checked := 0
  let stride := max 1 (n / 150)
  for h in (List.range (n + 1)).filter (fun h => h % stride == 0 || h + 1 >= n) do
    let old := loaded.atPrefix h
    let new ← reader.stateAt h
    match old, new with
    | some o, .ok st =>
        require s!"stateAt {h} = atPrefix {h}"
          ([1, 3].all fun c => o.canonicalBytes ⟨c⟩ == st.snapshot.canonicalBytes ⟨c⟩)
        checked := checked + 1
    | _, .error r => throw (IO.userError s!"FAIL stateAt {h}: {r.message}")
    | none, _ => throw (IO.userError s!"FAIL atPrefix {h} none")
  for c in [0, 1, n / 3, n - 1, n] do
    let low := max 1 (c + 1)
    match ← NativeHost.readWindows reader low n with
    | .ok log =>
        require s!"windows from {c} = image tail" (log.map Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode ==
          (loaded.image.accepted.drop (low - 1)).map Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode)
    | .error r => throw (IO.userError s!"FAIL windows {c}: {r.detail}")
  IO.println s!"differential: stateAt = atPrefix on {checked} heights; since windows = image tail at 5 cursors"
  -- 3. timing
  let heights := (List.range 20).map fun i => (loaded.baseHeight * (i + 1)) / 21
  let t0 ← IO.monoMsNow
  let mut sink := 0
  for h in heights do
    if let some o := loaded.atPrefix h then sink := sink + (o.canonicalBytes ⟨3⟩).length
  let t1 ← IO.monoMsNow
  for h in heights do
    match ← reader.stateAt h with
    | .ok st => sink := sink + (st.snapshot.canonicalBytes ⟨3⟩).length
    | .error r => throw (IO.userError r.message)
  let t2 ← IO.monoMsNow
  IO.println s!"TIMING n={n} base={loaded.baseHeight}: 20 past states old atPrefix {t1 - t0} ms, Reader.stateAt {t2 - t1} ms (sink {sink})"
  -- 2. plant
  let target := n - 5
  sql (directory / "store" / "forward-link.sqlite3")
    s!"UPDATE durable_log SET record = CAST(substr(record,1,length(record)-1) || X'FF' AS BLOB) WHERE height = {target}"
  match ← reader.stateAt (n - 1) with
  | .ok _ => throw (IO.userError "FAIL tampered range answered stateAt")
  | .error r =>
      IO.println s!"stateAt refused: {r.message}"
      require "stateAt names the tampered height" (r == .notIncluded target)
  match ← NativeHost.readWindows reader 1 n with
  | .ok _ => throw (IO.userError "FAIL tampered range answered the since window")
  | .error r =>
      IO.println s!"since window refused: {r.detail}"
      require "since names the tampered height"
        ((r.detail.splitOn s!"refused at height {target}").length > 1)
  IO.println "PASS doc-history past: Reader inputs equal the image's; a tampered record in range is refused by name"

end DocHistoryPast

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary, n] => IO.FS.withTempDir (DocHistoryPast.run binary n.toNat!)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/doc-history-past.lean STORE-HELPER N")
