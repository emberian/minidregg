/- A narrow, separately installed public carry-edge verifier.
It does not embed the old or target runtime semantics as its trust identity.
The caller pins this executable explicitly and supplies its already retained
old capsule. This executable never opens a Store or submits an operation. -/
import Host.CarryInspection

open Lean

private partial def readBounded (input : IO.FS.Handle) (remaining : Nat)
    (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  let chunk ← input.read (min 65536 (remaining + 1)).toUSize
  if chunk.size > remaining then throw (IO.userError "carry verifier request exceeds bound")
  if chunk.isEmpty then return acc
  readBounded input (remaining - chunk.size) (acc ++ chunk)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [configuration, operation, input, output] =>
      let bytes ← IO.FS.withFile input .read fun handle => readBounded handle 1048576
      let some text := String.fromUTF8? bytes
        | throw (IO.userError "carry verifier request is not UTF-8")
      let request ← IO.ofExcept (Json.parse text)
      let result ← match operation with
        | "carry-verifier-profile" =>
          Minidregg.Host.CarryInspection.registeredVerifierProfile configuration request
        | "carry-edge-verify" =>
          Minidregg.Host.CarryInspection.verifyRegisteredRequest configuration request
        | _ => pure (.error "unsupported carry verifier operation")
      let result ← IO.ofExcept result
      IO.FS.writeFile output result.compress
      return (0 : UInt32)
    | _ =>
      IO.eprintln "usage: minidregg-carry-verifier OLD_CONFIG carry-verifier-profile|carry-edge-verify REQUEST_JSON RESULT_JSON"
      return (2 : UInt32)
  catch error =>
    IO.eprintln s!"carry verifier refused: {error}"
    return (1 : UInt32)
