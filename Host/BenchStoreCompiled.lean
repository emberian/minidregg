/-
# bench-store-compiled -- compiled timings for the light-Store question (BURN-BENCH, measurement only)

One process = one measurement (so /usr/bin/time -v peak RSS is per measurement).
usage: bench-store-compiled STORE-HELPER grow DIR N
       bench-store-compiled STORE-HELPER DIR MODE
MODE: full-open | light-open | full-append | light-append | past-image | past-full-reader
    | past-light-reader | since-image | since-full-reader | since-light-reader | profile-light
DIR holds `key` and `store/`; checkpointEvery 64 (Host.Main's default).
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

namespace BenchStoreCompiled

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

def mkTransport (binary : System.FilePath) (directory : System.FilePath) : Transport :=
  let config : NativeConfig :=
    { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 64 }
  { config.transport (fun _ => ⟨7⟩) ⟨999⟩ with systemCell := none }

def fail {α} (msg : String) : IO α := throw (IO.userError msg)

def doLoad (t : Transport) : IO (Loaded rootBytes) := do
  match ← load t rootBytes with
  | .ok l => pure l
  | .error d => fail s!"open: {d}"

def doLight (t : Transport) : IO (DurableServed.Opening rootBytes) := do
  match ← DurableServed.openHead t rootBytes with
  | .ok o => pure o
  | .error d => fail s!"light open: {d}"

def grow (binary directory : System.FilePath) (count : Nat) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let transport := mkTransport binary directory
  match ← bootstrap transport rootBytes seed with
  | .error message => fail message
  | .ok () => pure ()
  let t0 ← IO.monoMsNow
  let initial ← doLoad transport
  let mut loaded := initial
  for number in List.range' (loaded.image.accepted.length + 1) count do
    match ← receiveLoadedDetailed transport rootBytes loaded (step number) with
    | .exact _ appended => loaded := appended.next
    | .ordinary _ => fail s!"append {number} did not confirm"
  IO.println s!"grown {count} in {← ms t0} ms"

/-- 20 heights below the last checkpoint of an N-record store. -/
def heights (n : Nat) : List Nat :=
  let cp := (n / 64) * 64
  (List.range 20).map fun i => (cp * (i + 1)) / 21

def say (label : String) (v : Nat) : IO Unit := IO.println s!"RESULT {label} ms={v}"

def pastReader {s} (reader : DurableHistoryReader.Reader rootBytes s) (n : Nat) : IO Unit := do
  let t ← IO.monoMsNow
  let mut sink := 0
  for h in heights n do
    match ← reader.stateAt h with
    | .ok st => sink := sink + (st.snapshot.canonicalBytes ⟨3⟩).length
    | .error r => fail r.message
  say s!"stateAt x20 (sink {sink})" (← ms t)

def sinceReader {s} (reader : DurableHistoryReader.Reader rootBytes s) (n : Nat) : IO Unit := do
  for back in [256, 2560] do
    let c := n - min n back
    let t ← IO.monoMsNow
    let mut cur := c + 1
    let mut cnt := 0
    while cur ≤ n do
      let hi := min n (cur + 255)
      match ← reader.range cur hi with
      | .ok log => cnt := cnt + log.length
      | .error r => fail r.message
      cur := hi + 1
    say s!"since window of {back} records (windows of 256, verified Reader.range; got {cnt})" (← ms t)

def measure (binary directory : System.FilePath) (mode : String) : IO Unit := do
  let t := mkTransport binary directory
  if mode.startsWith "image-at-" then
    let h := (mode.drop 9).toNat!
    let l ← doLoad t
    let t0 ← IO.monoMsNow
    match l.atPrefix h with
    | some o => say s!"atPrefix at height {h} (single; sink {(o.canonicalBytes ⟨3⟩).length}; base {l.baseHeight})" (← ms t0)
    | none => fail "atPrefix none"
    return
  match mode with
  | "full-open" =>
      let t0 ← IO.monoMsNow
      let l ← doLoad t
      say s!"full open (height {l.image.accepted.length}, base {l.baseHeight})" (← ms t0)
  | "light-open" =>
      let t0 ← IO.monoMsNow
      let o ← doLight t
      say s!"light open (height {o.head.height})" (← ms t0)
  | "full-append" =>
      let t0 ← IO.monoMsNow
      let l ← doLoad t
      let t1 ← IO.monoMsNow
      match ← receiveLoadedDetailed t rootBytes l (step (l.image.accepted.length + 1)) with
      | .exact _ _ => pure ()
      | .ordinary _ => fail "append did not confirm"
      say "full open" (t1 - t0)
      say "full append only" (← ms t1)
  | "light-append" =>
      let t0 ← IO.monoMsNow
      let o ← doLight t
      let t1 ← IO.monoMsNow
      match ← DurableServed.receiveServed t rootBytes o (step (o.head.height + 1)) with
      | .appended .. => pure ()
      | _ => fail "light append did not confirm"
      say "light open" (t1 - t0)
      say "light append only" (← ms t1)
  | "past-image" =>
      let l ← doLoad t
      let t0 ← IO.monoMsNow
      let mut sink := 0
      for h in heights l.image.accepted.length do
        match l.atPrefix h with
        | some o => sink := sink + (o.canonicalBytes ⟨3⟩).length
        | none => fail "atPrefix none"
      say s!"atPrefix x20 (sink {sink})" (← ms t0)
  | "past-full-reader" =>
      let l ← doLoad t
      match ← DurableHistoryStore.readerOf t rootBytes l with
      | .error d => fail d
      | .ok ⟨_, r⟩ => pastReader r l.image.accepted.length
  | "past-light-reader" =>
      let o ← doLight t
      pastReader (o.reader t rootBytes) o.head.height
  | "since-image" =>
      let l ← doLoad t
      let n := l.image.accepted.length
      for back in [256, 2560] do
        let c := n - min n back
        let t0 ← IO.monoMsNow
        let cnt := ((l.image.accepted.drop c).map DurableCheckpointCodec.recordFrame.encode).foldl (fun acc bs => acc + bs.length) 0
        if cnt == 0 then fail "empty"
        let e ← ms t0
        say s!"since window of {back} records (image tail, encoded; total encoded bytes {cnt})" e
  | "since-full-reader" =>
      let l ← doLoad t
      match ← DurableHistoryStore.readerOf t rootBytes l with
      | .error d => fail d
      | .ok ⟨_, r⟩ => sinceReader r l.image.accepted.length
  | "since-light-reader" =>
      let o ← doLight t
      sinceReader (o.reader t rootBytes) o.head.height
  | "profile-light" =>
      let o ← doLight t
      let n := o.head.height
      let reader := o.reader t rootBytes
      let hs := heights n
      let mut baseMs := 0
      let mut rangeMs := 0
      let mut stateMs := 0
      let mut recs := 0
      for h in hs do
        let a ← IO.monoMsNow
        match ← DurableHistoryStore.baseOf t rootBytes reader.seed o.head h with
        | .error r => fail r.message
        | .ok base =>
            baseMs := baseMs + (← ms a)
            let b ← IO.monoMsNow
            if base.height + 1 ≤ h then
              match ← DurableHistoryStore.range t o.head (base.height + 1) h with
              | .error r => fail r.message
              | .ok rs => recs := recs + rs.length
            rangeMs := rangeMs + (← ms b)
        let c ← IO.monoMsNow
        match ← reader.stateAt h with
        | .error r => fail r.message
        | .ok _ => stateMs := stateMs + (← ms c)
      say "stateAt x20: baseOf (checkpointAt + openSealed + atHeight) summed" baseMs
      say s!"stateAt x20: range after base (verify {recs} records) summed" rangeMs
      say "stateAt x20: full stateAt summed (replay = this - base - range)" stateMs
  | _ => fail s!"unknown mode {mode}"

end BenchStoreCompiled

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary, "grow", dir, n] => BenchStoreCompiled.grow binary dir n.toNat!
  | [binary, dir, mode] => BenchStoreCompiled.measure binary dir mode
  | _ => throw (IO.userError "usage: bench-store-compiled STORE-HELPER grow DIR N | STORE-HELPER DIR MODE")
