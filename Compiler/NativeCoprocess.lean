/-
# Compiler.NativeCoprocess — a Host's long-lived native helpers

The Host calls its native helpers (the durable Store, the signature verifier)
on every request. `IO.Process.output` forks the calling process, and a fork
copies the caller's page tables: measured on persvati (2026-10-01), one fork of
a Host holding one 566 KB Nock program took 6.4 ms against 0.7 ms before it was
born, and its `execve` 7.4 ms against 1.1 ms — a tax on every request that
grows with the bytes the Host holds.

So each helper binary runs once, as `<binary> serve`, for the Host's lifetime.
`output binary args` sends it `args`; the helper runs `<binary> args` as its
own child (its files, stdout, stderr and exit code are the one-shot call's)
and replies with exactly those three. The caller gets the same
`IO.Process.Output` the one-shot call would have produced, so every parser and
theorem over that output (`CredentialSignatureIO.positive_response_exact`,
`DurableReceiverIO.parseCasOutput`) reads it unchanged.

Frames (big-endian): request `u32 argc, (u32 len, bytes)*`; reply `u32 code,
u64 len, stdout, u64 len, stderr`. A helper that fails an exchange is killed
and forgotten, and the call throws: the caller's existing `catch` turns that
into the same unavailable/uncertain outcome a failed spawn produced. A helper
binary without `serve` exits at once, so the first call refuses loudly.
-/
import Std.Sync.Mutex

namespace Minidregg.Compiler.NativeCoprocess

set_option autoImplicit false

abbrev Helper := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

/-- The running helpers, by binary path. -/
initialize helpers : Std.Mutex (List (String × Helper)) ← Std.Mutex.new []

private def beBytes (width value : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun index => (value >>> (8 * index)).toUInt8).toArray⟩

private def beValue (bytes : ByteArray) : Nat :=
  bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- The request frame of one argv. -/
def requestFrame (args : Array String) : ByteArray :=
  args.foldl (fun frame arg => frame ++ beBytes 4 arg.utf8ByteSize ++ arg.toUTF8)
    (beBytes 4 args.size)

private def readExact (handle : IO.FS.Handle) (count : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < count do
    let chunk ← handle.read (count - bytes.size).toUSize
    if chunk.isEmpty then throw (IO.userError "native helper closed its reply")
    bytes := bytes ++ chunk
  return bytes

private def readText (handle : IO.FS.Handle) : IO String := do
  let bytes ← readExact handle (beValue (← readExact handle 8))
  match String.fromUTF8? bytes with
  | some text => return text
  | none => throw (IO.userError "native helper reply is not UTF-8")

private def exchange (helper : Helper) (args : Array String) : IO IO.Process.Output := do
  helper.stdin.write (requestFrame args)
  helper.stdin.flush
  let code := beValue (← readExact helper.stdout 4)
  let stdout ← readText helper.stdout
  let stderr ← readText helper.stdout
  return { exitCode := code.toUInt32, stdout, stderr }

/-- `IO.Process.output { cmd := binary, args }`, run by `binary`'s own `serve`
helper (started on first use). -/
def output (binary : String) (args : Array String) : IO IO.Process.Output :=
  helpers.atomically do
    let running ← get
    let helper ← match running.lookup binary with
      | some helper => pure helper
      | none => do
          let helper : Helper ← IO.Process.spawn
            { cmd := binary, args := #["serve"], stdin := .piped, stdout := .piped,
              stderr := .inherit }
          set ((binary, helper) :: running)
          pure helper
    try
      exchange helper args
    catch error =>
      try
        helper.kill
        discard <| helper.wait
      catch _ => pure ()
      modify fun running => running.filter fun entry => entry.1 != binary
      throw error

end Minidregg.Compiler.NativeCoprocess
