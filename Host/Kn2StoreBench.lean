/-
# kn2-store-bench -- Store open, first read and one append, at a given history length

KN2-STORE-OPEN measurement. For each N on the command line: a fresh Store
(the real SQLite helper, the real codecs, MAC, accumulator and spent map),
grown to N records through the receiving loop held open (one `receiveLoaded`
per record on the live image, checkpoints every 64), each record writing one
cell with 1000 bytes and spending one nullifier. Then, timed (compiled code):
* `open`: a cold `DurableReceiverIO.load`;
* `first read`: the Store-backed Reader of that opening (`readerOf`), then one
  verified record by height (the middle) and one transaction lookup (byTx);
* `append`: one more record through `receiveLoaded` on the fresh opening;
* `light open`: `DurableServed.openHead` (checkpoint + the records after it);
* `light open+append`: one more record through `DurableServed.receiveServed` on it.
Best of three for each. Not part of the umbrella gate.

usage: kn2-store-bench STORE-HELPER N...
-/
import Compiler.DurableHistoryStore
import Compiler.DurableServed
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableReceiverIO

namespace Kn2StoreBench

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def cellBytes (number : Nat) : List UInt8 := List.replicate 1000 (UInt8.ofNat number) ++ [UInt8.ofNat (number / 256)]

def seed : Seed := { absentBytes := [], cells := [(⟨3⟩, cellBytes 0)], available := fun _ => 1000000000 }

def nullifier (number : Nat) : StableNullifier := ⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩

def step (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨1000000 + number⟩
  writes := [⟨⟨3⟩, rootBytes (cellBytes (number - 1)), rootBytes (cellBytes number), cellBytes number⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
  subject := none
  postRootsBound := by simp
  guardsReadOnly := by simp

def ms (start : Nat) : IO Nat := return (← IO.monoMsNow) - start

def grow (transport : Transport) (count : Nat) : IO (Loaded rootBytes) := do
  let initial ← match ← load transport rootBytes with
    | .ok opened => pure opened
    | .error detail => throw (IO.userError s!"open: {detail}")
  let mut loaded := initial
  for number in List.range' (loaded.image.accepted.length + 1) (count - loaded.image.accepted.length) do
    match ← receiveLoadedDetailed transport rootBytes loaded (step number) with
    | .exact _ appended => loaded := appended.next
    | .ordinary _ => throw (IO.userError s!"append {number} did not confirm")
  return loaded

def run (binary : System.FilePath) (directory : System.FilePath) (count : Nat) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 64 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  match ← bootstrap transport rootBytes seed with
  | .error message => throw (IO.userError message)
  | .ok () => pure ()
  let growStart ← IO.monoMsNow
  let _ ← grow transport count
  let growMs ← ms growStart
  let mut openBest := 1000000000
  let mut readBest := 1000000000
  for _ in [0:3] do
    let t0 ← IO.monoMsNow
    let loaded ← match ← load transport rootBytes with
      | .ok loaded => pure loaded
      | .error detail => throw (IO.userError s!"open: {detail}")
    let openMs ← ms t0
    let t1 ← IO.monoMsNow
    match ← DurableHistoryStore.readerOf transport rootBytes loaded with
    | .error detail => throw (IO.userError s!"reader: {detail}")
    | .ok ⟨_, reader⟩ =>
        match ← reader.atHeight (count / 2) with
        | .error refusal => throw (IO.userError refusal.message)
        | .ok _ => pure ()
        match ← reader.byTx ⟨1000000 + count / 3⟩ with
        | .error refusal => throw (IO.userError refusal.message)
        | .ok _ => pure ()
    let readMs ← ms t1
    openBest := min openBest openMs
    readBest := min readBest readMs
  let mut lightBest := 1000000000
  for _ in [0:3] do
    let t ← IO.monoMsNow
    match ← DurableServed.openHead transport rootBytes with
    | .error detail => throw (IO.userError s!"light open: {detail}")
    | .ok opening =>
        unless opening.head.height == count do throw (IO.userError "light open: wrong head")
    lightBest := min lightBest (← ms t)
  let t2 ← IO.monoMsNow
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"open: {detail}")
  match ← receiveLoadedDetailed transport rootBytes loaded (step (count + 1)) with
  | .exact _ _ => pure ()
  | .ordinary _ => throw (IO.userError "the measured append did not confirm")
  let appendMs ← ms t2
  let t3 ← IO.monoMsNow
  match ← DurableServed.openHead transport rootBytes with
  | .error detail => throw (IO.userError s!"light open: {detail}")
  | .ok opening =>
      match ← DurableServed.receiveServed transport rootBytes opening (step (count + 2)) with
      | .appended .. => pure ()
      | _ => throw (IO.userError "the measured light append did not confirm")
  let lightAppendMs ← ms t3
  IO.println s!"records {count}: open {openBest} ms, first read (reader + 1 record + 1 byTx) {readBest} ms, open+append {appendMs} ms, light open {lightBest} ms, light open+append {lightAppendMs} ms (grown in {growMs} ms)"

end Kn2StoreBench

def main (arguments : List String) : IO Unit := do
  match arguments with
  | binary :: counts =>
      for count in counts.filterMap String.toNat? do
        IO.FS.withTempDir fun directory => Kn2StoreBench.run binary directory count
  | _ => throw (IO.userError "usage: kn2-store-bench STORE-HELPER N...")
