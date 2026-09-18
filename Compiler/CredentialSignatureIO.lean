/-
# Compiler.CredentialSignatureIO — opaque native Ed25519 verification

The configured executable is the source/version-pinned
`native/credential-signature-verifier` adapter to ed25519-dalek 2.2.0
`verify_strict`. It receives only a 32-byte public key, the exact Lean frame,
and a 64-byte detached signature. It cannot select authority or parse a
semantic request. Only one exact successful process response is positive.

This IO boundary does not prove the crypto implementation, process/OS byte
transport, or EUF-CMA/key custody. Those remain the explicit verifier and
custody assumptions of CredentialSignedEnvelopeController. No native reply
is deserialized as an authorization token.
-/
import Kernel.CredentialSignedEnvelopeController

namespace Minidregg.Compiler.CredentialSignatureIO

set_option autoImplicit false

structure NativeConfig where
  binary : System.FilePath

inductive Error where
  | publicKeyLength
  | signatureLength
  | processFailed (exitCode : UInt32) (detail : String)
  | malformedResponse
  | unavailable (detail : String)
  deriving DecidableEq, Repr

def parseOutput (output : IO.Process.Output) : Except Error Bool :=
  if output.exitCode != 0 then
    .error (.processFailed output.exitCode output.stderr)
  else if output.stderr != "" then
    .error .malformedResponse
  else
    match output.stdout with
    | "verified\n" => .ok true
    | "invalid\n" => .ok false
    | _ => .error .malformedResponse

def verify (config : NativeConfig) (publicKey frame signature : List UInt8) :
    IO (Except Error Bool) :=
  if publicKey.length != 32 then pure (.error .publicKeyLength)
  else if signature.length != 64 then pure (.error .signatureLength)
  else
    try
      IO.FS.withTempDir fun directory => do
        let keyPath := directory / "public-key.bin"
        let framePath := directory / "frame.bin"
        let signaturePath := directory / "signature.bin"
        IO.FS.writeBinFile keyPath publicKey.toByteArray
        IO.FS.writeBinFile framePath frame.toByteArray
        IO.FS.writeBinFile signaturePath signature.toByteArray
        let output ← IO.Process.output
          { cmd := config.binary.toString
            args := #["verify", keyPath.toString, framePath.toString, signaturePath.toString] }
        pure (parseOutput output)
    catch error => pure (.error (.unavailable s!"{error}"))

theorem positive_response_exact (output : IO.Process.Output)
    (accepted : parseOutput output = .ok true) :
    output.exitCode = 0 ∧ output.stderr = "" ∧ output.stdout = "verified\n" := by
  unfold parseOutput at accepted
  split at accepted
  next failed => contradiction
  next exited =>
    split at accepted
    next noisy => contradiction
    next quiet =>
      split at accepted
      next exactResponse =>
        exact ⟨by simpa using exited, by simpa using quiet, exactResponse⟩
      next => contradiction
      next => contradiction

theorem parse_verified :
    parseOutput { stdout := "verified\n", stderr := "", exitCode := 0 } = .ok true := by decide

theorem parse_ambiguous_refuses :
    parseOutput { stdout := "verified\ninvalid\n", stderr := "", exitCode := 0 } =
      .error .malformedResponse := by decide

theorem parse_stderr_refuses :
    parseOutput { stdout := "verified\n", stderr := "warning\n", exitCode := 0 } =
      .error .malformedResponse := by decide

end Minidregg.Compiler.CredentialSignatureIO
