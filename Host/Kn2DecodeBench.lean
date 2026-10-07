/-
# kn2-decode-bench -- per-record decode of the durable log record frame

KN2 measurement (not part of the umbrella gate). Builds N records of the shape
`kn2-store-bench` appends (one 1001-byte cell write, one nullifier), encodes
each with the record frame, then times, best of three over all N:
* `decodeRecord`: `DurableRecordFast.decodeRecord`, what the open calls (decode + frame check +
  canonical re-encode; compiled through `decodeRecord_eq_fast`);
* `decodeRaw`: the stream decode alone (`decodePrefix` of the product);
* `reencode`: `recordFrame.encode` of the decoded records.

usage: kn2-decode-bench N...
-/
import Compiler.DurableCheckpointCodec
import Compiler.DurableRecordFast
import Compiler.Sp800185Cshake256

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.Tower256ConcreteBackend

def benchRoot (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.DURABLE.RECEIVER.PROBE/v1".toUTF8.toList bytes).digest

def cellBytes (number : Nat) : List UInt8 := List.replicate 1000 (UInt8.ofNat number) ++ [UInt8.ofNat (number / 256)]

def benchRecord (number : Nat) : IntentRecord :=
  { transactionId := ⟨1000000 + number⟩
    writes := [⟨⟨3⟩, benchRoot (cellBytes (number - 1)), benchRoot (cellBytes number), cellBytes number⟩]
    readGuards := []
    nullifiers := [⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩]
    exactCharge := fun _ => 1
    event := ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩
    subject := none }

def best (label : String) (n : Nat) (work : IO Nat) : IO Unit := do
  let mut least := 1000000000
  let mut sink := 0
  for _ in [0:3] do
    let t ← IO.monoMsNow
    sink := sink + (← work)
    least := min least ((← IO.monoMsNow) - t)
  IO.println s!"{label}: {n} records: {least} ms ({least * 1000 / n} us/record) [{sink % 7}]"

def main (arguments : List String) : IO Unit := do
  for n in arguments.filterMap String.toNat? do
    let records := (List.range' 1 n).map benchRecord
    let framed := records.map recordFrame.encode
    let sizes := framed.foldl (fun total bytes => total + bytes.length) 0
    IO.println s!"{n} records, {sizes / n} bytes each"
    best "decodeRecord (as the open calls it)       " n do
      let mut ok := 0
      for bytes in framed do
        if (DurableRecordFast.decodeRecord bytes).isSome then ok := ok + 1
      unless ok == n do throw (IO.userError "decode refused an honest record")
      return ok
    best "decodeRaw (stream only)                   " n do
      let mut ok := 0
      for bytes in framed do
        if ((StreamCodec.product bytesStream DurableReceiverCodec.intentStream).toLawful.decode bytes).isSome then ok := ok + 1
      return ok
    let arrays := framed.map List.toByteArray
    best "toByteArray (list -> ByteArray)           " n do
      let mut total := 0
      for bytes in framed do
        total := total + bytes.toByteArray.size
      return total
    best "fastRaw (ByteArray decode only)           " n do
      let mut ok := 0
      for b in arrays do
        if ((DurableRecordFast.Fast.product DurableRecordFast.bytesFast DurableRecordFast.intentFast).decode b 0).isSome then ok := ok + 1
      return ok
    best "decodeRecordFast (fast + re-encode check) " n do
      let mut ok := 0
      for bytes in framed do
        if (DurableRecordFast.decodeRecordFast bytes).isSome then ok := ok + 1
      return ok
    best "reencode (recordFrame.encode)             " n do
      let mut total := 0
      for record in records do
        total := total + (recordFrame.encode record).length
      return total
