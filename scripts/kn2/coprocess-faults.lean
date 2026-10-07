/- Executed plants for `Compiler.NativeCoprocess` (gate row coprocess-faults).

A helper that cannot be executed, or that answers with bytes that are not a reply,
is refused BY NAME, with no panic and no allocation sized by the pipe:

 0. armed: the runtime's own spawn of a missing binary, with buffered stdout, DOES
    leak the caller's buffered bytes into the child's stdout pipe (the 2026-10-07
    cause). If the runtime stops doing that, this row says so, and the launcher can be
    re-examined.
 0b. the launcher alone (no flush) passes ZERO of those bytes.
 1. missing helper, caller stdout holding buffered bytes: `attempt` answers
    `closed 0`: ZERO bytes read from the reply pipe; through
    `CredentialSignatureIO.verify` the verdict is `unavailable` naming it.
 2. a helper whose first bytes are not the reply tag: `untagged`.
 3. a helper declaring a stdout one byte over `maxField`: `oversized "stdout"`;
    at exactly `maxField` (and then closing) it is `closed`, not `oversized`.
 controls: a fake helper sending a well-formed tagged reply is answered exactly, and
    (with VERIFIER given) the real verifier's `serve` answers a usage request.

Usage: lake env lean --run scripts/kn2/coprocess-faults.lean [VERIFIER] -/
import Compiler.CredentialSignatureIO

open Minidregg.Compiler
open Minidregg.Compiler.NativeCoprocess

namespace CoprocessFaults

def fail (label : String) : IO α := throw (IO.userError s!"FAIL coprocess faults: {label}")

def beBytes (width value : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun index => (value >>> (8 * index)).toUInt8).toArray⟩

/-- A fake `serve` helper at `directory/name`: it writes `reply` once, then drains
its stdin until the caller closes or kills it. -/
def fakeHelper (directory : System.FilePath) (name : String) (reply : ByteArray) :
    IO System.FilePath := do
  let replyPath := directory / s!"{name}.reply"
  IO.FS.writeBinFile replyPath reply
  let path := directory / name
  IO.FS.writeFile path s!"#!/bin/sh\n[ \"$1\" = serve ] || exit 2\ncat '{replyPath}'\nexec cat >/dev/null\n"
  let mode ← IO.Process.output { cmd := "/bin/chmod", args := #["0700", path.toString] }
  unless mode.exitCode == 0 do fail s!"chmod {path}: {mode.stderr}"
  pure path

def frame (code : Nat) (stdout stderr : String) : ByteArray :=
  replyTag ++ beBytes 4 code ++ beBytes 8 stdout.utf8ByteSize ++ stdout.toUTF8 ++
    beBytes 8 stderr.utf8ByteSize ++ stderr.toUTF8

def expectFailure (label : String) (binary : System.FilePath) (expected : Failure) : IO Unit := do
  match ← attempt binary.toString #["verify"] with
  | .error failure =>
      unless failure == expected do
        fail s!"{label}: refused as {repr failure}, expected {repr expected}"
      IO.println s!"refused as expected ({label}): {failure.render}"
  | .ok (output, read) => fail s!"{label}: answered code {output.exitCode} after {read} bytes"

def run (verifier : Option String) (directory : System.FilePath) : IO Unit := do
  -- 0. armed: the runtime's spawn leaks buffered stdout into a failed child's pipe.
  IO.print "buffered-before-the-direct-spawn "
  let child ← IO.Process.spawn
    { cmd := (directory / "absent-direct").toString, stdin := .null, stdout := .piped, stderr := .null }
  let leaked ← child.stdout.readBinToEnd
  discard <| child.wait
  if leaked.size == 0 then
    fail "armed row: the runtime no longer leaks buffered stdout into a failed exec; re-examine NativeCoprocess.launcher"
  IO.println s!"\narmed: the runtime's direct spawn of a missing binary leaked {leaked.size} buffered bytes into its pipe"
  -- 0b. the launcher ALONE (no flush): the same buffered bytes, the same missing binary,
  -- started as `start` starts it but without its flush: zero bytes reach the pipe.
  IO.print "buffered-before-the-launcher-spawn "
  let launched ← IO.Process.spawn
    { cmd := launcher, args := launcherArgs (directory / "absent-launched").toString,
      stdin := .null, stdout := .piped, stderr := .null }
  let through ← launched.stdout.readBinToEnd
  let code ← launched.wait
  unless through.size == 0 do
    fail s!"launcher row: {through.size} bytes reached the pipe through the launcher"
  IO.println s!"\nlauncher alone (no flush): 0 bytes reached the pipe; the shell exited {code}"
  -- 1. missing helper with buffered stdout: zero bytes read, refused by name.
  IO.print "buffered-before-the-helper-spawn "
  expectFailure "missing helper, buffered stdout" (directory / "absent-helper") (.closed 0)
  IO.print "buffered-before-the-verifier-spawn "
  let config : CredentialSignatureIO.NativeConfig := ⟨directory / "absent-verifier"⟩
  match ← CredentialSignatureIO.verify config (List.replicate 32 1) [0] (List.replicate 64 2) with
  | .error (.unavailable detail) =>
      unless detail == (Failure.closed 0).render do
        fail s!"missing verifier: unavailable, but not as `closed 0`: {detail}"
      IO.println s!"refused as expected (missing verifier): unavailable \"{detail}\""
  | other => fail s!"missing verifier answered {repr other}"
  -- 2. untagged first frame.
  let garbage ← fakeHelper directory "garbage" "store at height 3 (the fixture's prefix)\n".toUTF8
  expectFailure "untagged reply" garbage (.untagged 8)
  -- 3. oversized declared length, and the boundary.
  let oversized ← fakeHelper directory "oversized" (replyTag ++ beBytes 4 0 ++ beBytes 8 (maxField + 1))
  expectFailure "oversized stdout" oversized (.oversized "stdout" (maxField + 1))
  let atBound ← fakeHelper directory "at-bound" (replyTag ++ beBytes 4 0 ++ beBytes 8 maxField)
  expectFailure "stdout at the bound, then closed" atBound (.closed 20)
  -- controls.
  let good ← fakeHelper directory "good" (frame 7 "seven\n" "to stderr\n")
  match ← attempt good.toString #["verify"] with
  | .ok (output, read) =>
      unless output.exitCode == 7 && output.stdout == "seven\n" && output.stderr == "to stderr\n" &&
          read == (frame 7 "seven\n" "to stderr\n").size do
        fail s!"control: a well-formed reply read as {output.exitCode} {repr output.stdout} {repr output.stderr} ({read} bytes)"
      IO.println s!"control (well-formed tagged reply): answered exactly, {read} bytes"
  | .error failure => fail s!"control: a well-formed reply refused: {failure.render}"
  if let some verifier := verifier then
    match ← attempt verifier #["verify"] with
    | .ok (output, _) =>
        if output.exitCode == 0 then fail "control: the verifier accepted a usage request"
        IO.println s!"control (real verifier serve): answered a usage request with code {output.exitCode}"
    | .error failure => fail s!"control: the real verifier's serve refused: {failure.render}"
  IO.println "PASS coprocess faults: a missing helper reads zero reply bytes and is unavailable by name; an untagged and an oversized reply are refused by name; well-formed replies answer exactly"

end CoprocessFaults

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] => IO.FS.withTempDir (CoprocessFaults.run none)
  | [verifier] => IO.FS.withTempDir (CoprocessFaults.run (some verifier))
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/coprocess-faults.lean [VERIFIER]")
