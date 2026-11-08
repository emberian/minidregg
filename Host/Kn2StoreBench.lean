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
Best of three for each (the past reads too). Not part of the umbrella gate.
`KN2_BENCH_CREATES=1`: each record instead births a fresh cell, so N records hold
N cells (the axis the world root's cost grows on).

With `KN2_BENCH_AT=1`, also the past reads (`at h`) on the cold opening, at heights near
a quarter, a half and three quarters of the way up: `at` = `Loaded.pastBytes` (the cell's
last write at or below `h`, no checkpoint read); `at genesis` = the genesis fold of the prefix,
only when N ≤ `KN2_BENCH_GENESIS_MAX` (default 3000), which the two must agree with. Each read
is forced by summing the cell's bytes inside `IO.lazyPure` (a pure `let` floats out of the
timed span).

With `KN2_BENCH_STORE=DIR`, the Store for N lives in DIR/N and is kept: a later
run reuses it (grown only by the records it lacks), so a representation change
is measured on the same bytes without regrowing.

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

/-- Record `number`: an update of cell 3, or (`creates`) the birth of cell `1000 + number`,
so the Store holds `number` cells after `number` records (the cell-count axis). -/
def step (creates : Bool) (number : Nat) : DataIntent rootBytes where
  transactionId := ⟨1000000 + number⟩
  writes := if creates then [⟨⟨1000 + number⟩, rootBytes [], rootBytes (cellBytes number), cellBytes number⟩]
    else [⟨⟨3⟩, rootBytes (cellBytes (number - 1)), rootBytes (cellBytes number), cellBytes number⟩]
  readGuards := []
  nullifiers := [nullifier number]
  exactCharge := fun _ => 1
  event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
  subject := none
  postRootsBound := by split <;> simp
  guardsReadOnly := by simp

def ms (start : Nat) : IO Nat := return (← IO.monoMsNow) - start

def force (snapshot : Option (DataSnapshot rootBytes)) : Nat :=
  match snapshot with
  | some snapshot => (snapshot.canonicalBytes ⟨3⟩).foldl (fun total byte => total + byte.toNat) 0
  | none => 0

def sumBytes (bytes : List UInt8) : Nat := bytes.foldl (fun total byte => total + byte.toNat) 0

/-- `at h` over a cold opening, off the log (`pastBytes`) and (bounded) the genesis way. -/
def pastReads (transport : Transport) (count : Nat) : IO Unit := do
  let genesisMax := ((← IO.getEnv "KN2_BENCH_GENESIS_MAX").bind String.toNat?).getD 3000
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"open: {detail}")
  for quarter in [1, 2, 3] do
    let height := (quarter * count / 4) / 64 * 64 + 32
    let mut pastMs := 1000000000
    let mut pastSum := 0
    for _ in [0:3] do
      let t0 ← IO.monoMsNow
      pastSum ← IO.lazyPure fun _ => sumBytes (loaded.pastBytes height ⟨3⟩)
      pastMs := min pastMs (← ms t0)
    if count ≤ genesisMax then
      let t1 ← IO.monoMsNow
      let genesisSum ← IO.lazyPure fun _ =>
        force ((loaded.prefixImage height).restore rootBytes)
      let genesisMs ← ms t1
      unless genesisSum == pastSum do throw (IO.userError s!"at {height}: the log and the genesis fold disagree")
      IO.println s!"records {count}: at {height}: {pastMs} ms, genesis {genesisMs} ms"
    else
      IO.println s!"records {count}: at {height}: {pastMs} ms (sum {pastSum})"

def grow (creates : Bool) (transport : Transport) (count : Nat) : IO (Loaded rootBytes) := do
  let initial ← match ← load transport rootBytes with
    | .ok opened => pure opened
    | .error detail => throw (IO.userError s!"open: {detail}")
  let mut loaded := initial
  for number in List.range' (loaded.image.accepted.length + 1) (count - loaded.image.accepted.length) do
    match ← receiveLoadedDetailed transport rootBytes loaded (step creates number) with
    | .exact _ appended => loaded := appended.next
    | .ordinary _ => throw (IO.userError s!"append {number} did not confirm")
  return loaded

def run (creates : Bool) (binary : System.FilePath) (directory : System.FilePath) (count : Nat)
    (reuse : Bool := false) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 64 }
  let transport := { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }
  unless reuse do
    match ← bootstrap transport rootBytes seed with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
  let growStart ← IO.monoMsNow
  let grown ← grow creates transport count
  let growMs ← ms growStart
  -- a reused Store already holds the measured appends of earlier runs
  let tip := grown.image.accepted.length
  if (← IO.getEnv "KN2_BENCH_AT") == some "1" then pastReads transport count
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
        unless opening.head.height == tip do throw (IO.userError "light open: wrong head")
    lightBest := min lightBest (← ms t)
  let t2 ← IO.monoMsNow
  let loaded ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => throw (IO.userError s!"open: {detail}")
  let tAppend ← IO.monoMsNow
  match ← receiveLoadedDetailed transport rootBytes loaded (step creates (tip + 1)) with
  | .exact _ _ => pure ()
  | .ordinary _ => throw (IO.userError "the measured append did not confirm")
  let appendOnlyMs ← ms tAppend
  let appendMs ← ms t2
  let t3 ← IO.monoMsNow
  match ← DurableServed.openHead transport rootBytes with
  | .error detail => throw (IO.userError s!"light open: {detail}")
  | .ok opening =>
      match ← DurableServed.receiveServed transport rootBytes opening (step creates (tip + 2)) with
      | .appended .. => pure ()
      | _ => throw (IO.userError "the measured light append did not confirm")
  let lightAppendMs ← ms t3
  IO.println s!"records {count}{if creates then " (each a cell birth)" else ""}: open {openBest} ms, first read (reader + 1 record + 1 byTx) {readBest} ms, open+append {appendMs} ms (the append alone {appendOnlyMs} ms), light open {lightBest} ms, light open+append {lightAppendMs} ms (grown in {growMs} ms)"

end Kn2StoreBench

def main (arguments : List String) : IO Unit := do
  match arguments with
  | binary :: counts =>
      let creates := (← IO.getEnv "KN2_BENCH_CREATES") == some "1"
      for count in counts.filterMap String.toNat? do
        match ← IO.getEnv "KN2_BENCH_STORE" with
        | some keep =>
            let directory : System.FilePath := keep / toString count
            let reuse ← (directory / "store").pathExists
            IO.FS.createDirAll directory
            Kn2StoreBench.run creates binary directory count reuse
        | none => IO.FS.withTempDir fun directory => Kn2StoreBench.run creates binary directory count
  | _ => throw (IO.userError "With `KN2_BENCH_STORE=DIR`, the Store for N lives in DIR/N and is kept: a later
run reuses it (grown only by the records it lacks), so a representation change
is measured on the same bytes without regrowing.

usage: kn2-store-bench STORE-HELPER N...")
