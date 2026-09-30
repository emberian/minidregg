/-
# nock-eval — the compiled `Theory.Nock` interpreter behind a CLI

The differential harness (NOCK-RUNNER) drives this binary against `nockvm`.
Everything it prints is computed by `Minidregg.Theory.Nock.runJammed` (the
function `runJammed_sound` / `runJammed_crash_sound` are about) and
`Minidregg.Theory.Noun.cue`/`jam` (`cue_jam`); this file only moves bytes.

    nock-eval run [--fuel N] [--raw]   stdin: jam of [subject formula]
      stdout: `ok <steps> <hex>` | `crash <steps>` | `exhausted <steps>` | `malformed`
      exit:   0 ok · 1 crash · 2 exhausted · 3 malformed · 64 usage
    nock-eval cue [--raw] [--no-rejam] stdin: a jam
      stdout: `canonical <hex>` | `noncanonical <hex>` | `malformed`
              (`decoded` with --no-rejam: cue only, no canonicality check)
      exit:   0 canonical/decoded · 4 noncanonical · 3 malformed · 64 usage

Input is hex (whitespace and a leading `0x` ignored) unless `--raw`; bytes are
the jam atom's little-endian bytes, as `nockvm`'s `Atom::as_bytes`.
-/
import Theory.Nock

open Minidregg.Theory
open Minidregg.Theory.Nock

namespace NockEval

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def decodeHex (s : String) : Option (List UInt8) :=
  let cs := s.toList.filter fun c => !c.isWhitespace
  let cs := match cs with
    | '0' :: 'x' :: r => r
    | '0' :: 'X' :: r => r
    | r => r
  let rec go : List Char → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | [_], _ => none
    | a :: b :: r, acc => do
      let x ← hexDigit? a
      let y ← hexDigit? b
      go r ((x * 16 + y).toUInt8 :: acc)
  go cs []

def hexOf (bs : List UInt8) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

structure Opts where
  fuel : Nat := 1000000
  raw : Bool := false
  noRejam : Bool := false
  bad : Bool := false

def parseOpts : List String → Opts → Opts
  | [], o => o
  | "--raw" :: r, o => parseOpts r { o with raw := true }
  | "--no-rejam" :: r, o => parseOpts r { o with noRejam := true }
  | "--fuel" :: n :: r, o =>
    match n.toNat? with
    | some k => parseOpts r { o with fuel := k }
    | none => { o with bad := true }
  | _ :: _, o => { o with bad := true }

def readInput (raw : Bool) : IO (Option (List UInt8)) := do
  let stdin ← IO.getStdin
  let bytes ← stdin.readBinToEnd
  if raw then return some bytes.toList
  else
    match String.fromUTF8? bytes with
    | some s => return decodeHex s
    | none => return none

def usage : IO UInt32 := do
  IO.eprintln "usage: nock-eval run [--fuel N] [--raw] | nock-eval cue [--raw] [--no-rejam]   (stdin: jam, hex unless --raw)"
  return 64

end NockEval

open NockEval in
def main (args : List String) : IO UInt32 := do
  match args with
  | "run" :: rest =>
    let o := parseOpts rest {}
    if o.bad then return ← usage
    let some input ← readInput o.raw | IO.println "malformed"; return 3
    match runJammed o.fuel input with
    | .ok k out => IO.println s!"ok {k} {hexOf out}"; return 0
    | .crash k => IO.println s!"crash {k}"; return 1
    | .exhausted k => IO.println s!"exhausted {k}"; return 2
    | .malformed => IO.println "malformed"; return 3
  | "cue" :: rest =>
    let o := parseOpts rest {}
    if o.bad then return ← usage
    let some input ← readInput o.raw | IO.println "malformed"; return 3
    match Noun.cue input with
    | none => IO.println "malformed"; return 3
    | some n =>
      if o.noRejam then IO.println "decoded"; return 0
      let re := Noun.jam n
      if re == input then IO.println s!"canonical {hexOf re}"; return 0
      else IO.println s!"noncanonical {hexOf re}"; return 4
  | _ => usage
