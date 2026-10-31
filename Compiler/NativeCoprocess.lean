/-
# Compiler.NativeCoprocess — a Host's long-lived native helpers

The Host calls its native helpers (the durable Store) on every request.
`IO.Process.output` forks the calling process, and a fork
copies the caller's page tables: measured on persvati (2026-10-01), one fork of
a Host holding one 566 KB Nock program took 6.4 ms against 0.7 ms before it was
born, and its `execve` 7.4 ms against 1.1 ms — a tax on every request that
grows with the bytes the Host holds.

So each helper binary runs once, as `<binary> serve`, for the Host's lifetime.
`output binary args` sends it `args`; the helper runs `<binary> args` as its
own child (its files, stdout, stderr and exit code are the one-shot call's)
and replies with exactly those three. The caller gets the same
`IO.Process.Output` the one-shot call would have produced, so every parser and
theorem over that output (`DurableReceiverIO.parseCasOutput`) reads it unchanged.

Frames (big-endian): request `u32 argc, (u32 len, bytes)*`; reply
`replyTag (8 bytes), u32 code, u64 len, stdout, u64 len, stderr`, each length
at most `maxField`. A helper that fails an exchange is killed and forgotten,
and the call throws the `Failure` by name: the caller's existing `catch` turns
that into the same unavailable/uncertain outcome a failed spawn produced.

## Why a failed start never reaches the reply pipe (measured 2026-10-07)

Lean's `IO.Process.spawn` forks and `execvp`s; when the exec fails, the child
prints "could not execute external process" and calls `exit`, which FLUSHES
the stdio buffers it inherited. The child's stdout is the reply pipe, so a
caller holding buffered stdout (a Host logging to a file) received its own
log lines as a reply: "stor" read as the code, "e at hei" as a u64 length,
and the read of that length aborted the process with `INTERNAL PANIC: out of
memory` (scripts/kn2/invoke-undeclared.lean with no verifier, at fc24cd91).
The runtime offers no `posix_spawn` and no `_exit` path, so the guarantee is
built here, in three layers:

1. `start` never asks the runtime to exec the helper. It execs `/bin/sh`
   (`launcher`), which `exec`s the helper with `serve`. If the helper cannot
   be executed, the SHELL reports it on stderr and exits 127: it holds none of
   the caller's buffers, so the reply pipe sees zero bytes. The runtime's own
   flush can run only if `/bin/sh` itself cannot be executed.
2. For that residual case, `start` flushes the caller's stdout and stderr
   immediately before the spawn, under the helpers' mutex.
3. Whatever arrives, the reply parser trusts nothing: a reply must open with
   `replyTag`, every length is checked against `maxField` before any read,
   and reads are in bounded chunks, so no length from the pipe sizes an
   allocation.
Executed: scripts/kn2/coprocess-faults.lean.
-/
module

public import Std.Sync.Mutex

@[expose] public section

namespace Minidregg.Compiler.NativeCoprocess

set_option autoImplicit false

abbrev Helper := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

/-- The running helpers, by binary path. -/
initialize helpers : Std.Mutex (List (String × Helper)) ← Std.Mutex.new []

/-- The first eight bytes of every reply (ASCII `MDCOPRC1`). Bytes that are not
a helper's reply (a runtime's flushed buffer, a binary without `serve` that
prints its usage) are refused by name before any length is read. -/
def replyTag : ByteArray := "MDCOPRC1".toUTF8

/-- The largest stdout or stderr a helper may return: the Store's deployment
bound on one record (`MAX_RECORD_BYTES`, 64 MiB, native/hyperdocument-link-
sqlite-store/src/lib.rs), the largest legitimate field (`read ROOT` writes one
record to stdout). A larger declared length is refused before it is read. -/
def maxField : Nat := 64 * 1024 * 1024

/-- The largest single read from the pipe. -/
def chunk : Nat := 64 * 1024

/-- The program that starts every helper (layer 1 above). -/
def launcher : String := "/bin/sh"

/-- `launcher`'s arguments: the script `exec "$0" serve` with the helper as `$0`
(a positional parameter: the path is never parsed as shell text). -/
def launcherArgs (binary : String) : Array String := #["-c", "exec \"$0\" serve", binary]

/-- Why an exchange produced no reply. `read` counts the reply bytes this
exchange took from the pipe. -/
inductive Failure where
  | start (detail : String)
  | pipe (detail : String)
  | closed (read : Nat)
  | untagged (read : Nat)
  | oversized (field : String) (length : Nat)
  | notUtf8 (field : String)
  deriving Repr, DecidableEq

def Failure.render : Failure → String
  | .start detail => s!"native helper did not start: {detail}"
  | .pipe detail => s!"native helper pipe failed: {detail}"
  | .closed read => s!"native helper closed its reply after {read} bytes"
  | .untagged read => s!"native helper reply does not open with the reply tag ({read} bytes read)"
  | .oversized field length => s!"native helper reply {field} declares {length} bytes, over the {maxField}-byte bound"
  | .notUtf8 field => s!"native helper reply {field} is not UTF-8"

private def beBytes (width value : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun index => (value >>> (8 * index)).toUInt8).toArray⟩

private def beValue (bytes : ByteArray) : Nat :=
  bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- The request frame of one argv. -/
def requestFrame (args : Array String) : ByteArray :=
  args.foldl (fun frame arg => frame ++ beBytes 4 arg.utf8ByteSize ++ arg.toUTF8)
    (beBytes 4 args.size)

/-- A reply being read: the pipe and the bytes taken from it so far. -/
structure Reader where
  handle : IO.FS.Handle
  read : Nat

/-- Exactly `count` bytes (`count ≤ maxField` is the caller's check), in reads
of at most `chunk`. -/
private def readExact (reader : Reader) (count : Nat) : ExceptT Failure IO (ByteArray × Reader) := do
  let mut bytes := ByteArray.empty
  let mut read := reader.read
  while bytes.size < count do
    let piece ← (reader.handle.read (min chunk (count - bytes.size)).toUSize : IO ByteArray)
    if piece.isEmpty then throw (.closed read)
    bytes := bytes ++ piece
    read := read + piece.size
  return (bytes, { reader with read })

private def readText (reader : Reader) (field : String) : ExceptT Failure IO (String × Reader) := do
  let (header, reader) ← readExact reader 8
  let length := beValue header
  if length > maxField then throw (.oversized field length)
  let (bytes, reader) ← readExact reader length
  match String.fromUTF8? bytes with
  | some text => return (text, reader)
  | none => throw (.notUtf8 field)

/-- Parse one reply from `handle`, returning it with the number of bytes read. -/
def readReply (handle : IO.FS.Handle) : ExceptT Failure IO (IO.Process.Output × Nat) := do
  let (tag, reader) ← readExact ⟨handle, 0⟩ replyTag.size
  if tag != replyTag then throw (.untagged reader.read)
  let (code, reader) ← readExact reader 4
  let (stdout, reader) ← readText reader "stdout"
  let (stderr, reader) ← readText reader "stderr"
  return ({ exitCode := (beValue code).toUInt32, stdout, stderr }, reader.read)

/-! ## Memory requests (frame v2)

A request may carry its input files as named blobs and get the files it writes back the same
way, so a call makes no temporary directory and no file round trip: the request opens with
`memoryMark`, then `u32 count, (u32 len, name, u64 len, bytes)*`, then the argv frame; a path
argument `mem:NAME` names a blob. The reply opens with `replyTagMemory` and appends the blobs
written in the same shape. A helper that does not know the mark fails the exchange, which is
reported like any other failed exchange. -/

/-- The four bytes a memory request opens with (`u32` all ones: never an argc). -/
def memoryMark : ByteArray := beBytes 4 0xFFFFFFFF

/-- The first eight bytes of a memory request's reply (ASCII `MDCOPRC2`). -/
def replyTagMemory : ByteArray := "MDCOPRC2".toUTF8

/-- The most blobs a memory request or reply carries, and the longest blob name. -/
def maxBlobs : Nat := 8
def maxBlobName : Nat := 256

/-- The request frame of one argv with its input blobs. -/
def requestFrameMemory (blobs : List (String × ByteArray)) (args : Array String) : ByteArray :=
  blobs.foldl (fun frame blob => frame ++ beBytes 4 blob.1.utf8ByteSize ++ blob.1.toUTF8 ++
      beBytes 8 blob.2.size ++ blob.2)
    (memoryMark ++ beBytes 4 blobs.length) ++ requestFrame args

private def readBytes (reader : Reader) (field : String) : ExceptT Failure IO (ByteArray × Reader) := do
  let (header, reader) ← readExact reader 8
  let length := beValue header
  if length > maxField then throw (.oversized field length)
  readExact reader length

/-- Parse one memory reply: the output and the blobs written, with the bytes read. -/
def readReplyMemory (handle : IO.FS.Handle) :
    ExceptT Failure IO ((IO.Process.Output × List (String × ByteArray)) × Nat) := do
  let (tag, reader) ← readExact ⟨handle, 0⟩ replyTagMemory.size
  if tag != replyTagMemory then throw (.untagged reader.read)
  let (code, reader) ← readExact reader 4
  let (stdout, reader) ← readText reader "stdout"
  let (stderr, reader) ← readText reader "stderr"
  let (count, reader) ← readExact reader 4
  let count := beValue count
  if count > maxBlobs then throw (.oversized "blob count" count)
  let mut reader := reader
  let mut blobs : List (String × ByteArray) := []
  for _ in [0:count] do
    let (length, next) ← readExact reader 4
    let length := beValue length
    if length > maxBlobName then throw (.oversized "blob name" length)
    let (name, next) ← readExact next length
    let some name := String.fromUTF8? name | throw (.notUtf8 "blob name")
    let (bytes, next) ← readBytes next name
    blobs := blobs ++ [(name, bytes)]
    reader := next
  return (({ exitCode := (beValue code).toUInt32, stdout, stderr }, blobs), reader.read)

/-- Start `binary serve` through `launcher` (layers 1 and 2 of the module doc). -/
def start (binary : String) : IO (Except Failure Helper) := do
  try
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    let helper ← IO.Process.spawn
      { cmd := launcher, args := launcherArgs binary, stdin := .piped, stdout := .piped,
        stderr := .inherit }
    pure (.ok helper)
  catch error => pure (.error (.start s!"{error}"))

/-- Send one request and read its reply. A helper that has already exited makes
the write fail (EPIPE); the reply pipe is read anyway, so such a helper is
reported by what it sent (`closed 0` for one that never started), not by the
race between its exit and the write. An IO error reading the pipe is `pipe`. -/
private def exchangeWith {α : Type} (helper : Helper) (frame : ByteArray)
    (read : IO.FS.Handle → ExceptT Failure IO (α × Nat)) : IO (Except Failure (α × Nat)) := do
  let sent ← try
      helper.stdin.write frame
      helper.stdin.flush
      pure none
    catch error => pure (some s!"{error}")
  let reply ← try (read helper.stdout).run
    catch error => pure (.error (.pipe s!"{error}"))
  match sent, reply with
  | some detail, .ok _ => pure (.error (.pipe s!"the request was not sent ({detail}), yet a reply arrived"))
  | _, reply => pure reply

/-- One exchange of `frame` with `binary`'s `serve` helper (started on first use), read by
`read`. A failed exchange kills and forgets the helper. -/
def attemptWith {α : Type} (binary : String) (frame : ByteArray)
    (read : IO.FS.Handle → ExceptT Failure IO (α × Nat)) : IO (Except Failure (α × Nat)) :=
  helpers.atomically do
    let running ← get
    let helper : Except Failure Helper ← match running.lookup binary with
      | some helper => pure (Except.ok helper)
      | none => do
          let started ← start binary
          if let .ok helper := started then set ((binary, helper) :: running)
          pure started
    match helper with
    | .error failure => pure (Except.error failure)
    | .ok helper =>
        let result ← exchangeWith helper frame read
        if result matches .error _ then
          try
            helper.kill
            discard <| helper.wait
          catch _ => pure ()
          modify fun running => running.filter fun entry => entry.1 != binary
        pure result

/-- One exchange with `binary`'s `serve` helper (started on first use), with the
reply bytes it read. A failed exchange kills and forgets the helper. -/
def attempt (binary : String) (args : Array String) : IO (Except Failure (IO.Process.Output × Nat)) :=
  attemptWith binary (requestFrame args) readReply

/-- `IO.Process.output { cmd := binary, args }`, run by `binary`'s own `serve`
helper (started on first use). A failed exchange throws its `Failure` by name. -/
def output (binary : String) (args : Array String) : IO IO.Process.Output := do
  match ← attempt binary args with
  | .ok (result, _) => pure result
  | .error failure => throw (IO.userError failure.render)

/-- `output` with input files as blobs and the files written returned as blobs (`mem:NAME`
paths; the memory requests section above). A failed exchange throws its `Failure` by name. -/
def outputMemory (binary : String) (args : Array String) (inputs : List (String × ByteArray)) :
    IO (IO.Process.Output × List (String × ByteArray)) := do
  match ← attemptWith binary (requestFrameMemory inputs args) readReplyMemory with
  | .ok (result, _) => pure result
  | .error failure => throw (IO.userError failure.render)

end Minidregg.Compiler.NativeCoprocess
