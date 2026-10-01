/-
# cshake-bench -- throughput of the compiled cSHAKE256 / KMAC256

For each size (bytes) given on the command line, builds a deterministic
pseudo-random input outside the timed region and times
`cshake256Bytes` (customized and SHAKE-compatible) and `kmac256Bytes` over it.
Prints MB/s and the first digest bytes, so two Host builds can be compared for
byte identity on the same inputs.  Not part of the umbrella gate.
-/
import Compiler.Sp800185Cshake256Core
import Compiler.Sp800185Kmac256

open Minidregg.Compiler.Sp800185Cshake256

def benchInput (n seed : Nat) : List UInt8 := Id.run do
  let mut acc : Array UInt8 := Array.mkEmpty n
  let mut x : UInt64 := UInt64.ofNat (seed * 2654435761 + 12345)
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    acc := acc.push (x >>> 56).toUInt8
  return acc.toList

def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length = 1 then "0" ++ s else s)

def timeIt (label : String) (n : Nat) (f : Unit → List UInt8) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let out := f ()
  if out.length == 0 then IO.println "empty"
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1.0e9
  let mbps := n.toFloat / 1.0e6 / secs
  IO.println s!"{label} bytes={n} s={secs} MB/s={mbps} digest={hex out}"

/-- Many small hashes: the Store pattern (cells of a few hundred bytes). -/
def smallLoop (label : String) (count n : Nat) (f : List UInt8 → List UInt8) : IO Unit := do
  let inputs := (List.range count).map fun i => benchInput n (i + 7)
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for x in inputs do
    acc := acc + ((f x).headD 0).toNat
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1.0e9
  IO.println s!"{label} count={count} bytes={n} us_per_hash={secs * 1.0e6 / count.toFloat} acc={acc}"

def main (args : List String) : IO UInt32 := do
  let custom0 := "DREGG/BENCH/v1".toUTF8.toList
  let key0 := (List.range 32).map fun i => UInt8.ofNat (0x40 + i)
  if args.headD "" == "small" then
    for n in [32, 256, 1024] do
      smallLoop "small-cshake" 20000 n (cshake256Bytes custom0)
      smallLoop "small-shake" 20000 n (cshake256Bytes [])
      smallLoop "small-kmac" 20000 n (kmac256Bytes key0 custom0)
      smallLoop "prefix-only" 20000 n (fun x => customizationPrefix (custom0 ++ x.take 1))
    return 0
  let sizes := args.filterMap String.toNat?
  let custom := "DREGG/BENCH/v1".toUTF8.toList
  let key := (List.range 32).map fun i => UInt8.ofNat (0x40 + i)
  for n in sizes do
    let input := benchInput n n
    if input.length != n then IO.println "bad length"
    timeIt "cshake" n fun _ => cshake256Bytes custom input
    timeIt "shake" n fun _ => cshake256Bytes [] input
    timeIt "kmac" n fun _ => kmac256Bytes key custom input
  return 0
