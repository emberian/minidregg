/-
# Compiler.CredentialSignatureIO — opaque native Ed25519 verification

The configured executable is the source/version-pinned
`native/credential-signature-verifier` adapter to ed25519-dalek 2.2.0
`verify_strict`. It receives only a 32-byte public key, the exact Lean frame,
and a 64-byte detached signature. It cannot select authority or parse a
semantic request. Only one exact successful process response is positive.

The same executable's `verify-sshsig` verb checks an OpenSSH SSHSIG
signature (PROTOCOL.sshsig) by an ssh-ed25519 key: it receives the 32-byte
key, the namespace, the message and the raw 64-byte signature, computes
SHA-512 of the message (Lean has no SHA-512) and verifies strictly over
`Kernel.PayEnrolMemo.sshsigSignedData namespace (SHA-512 message)`.  The
native boundary therefore grows by exactly one hash, and every other byte of
the signed data is fixed in Lean (`PayEnrolMemo.sshsig_signed_data_fixture`
and the Rust `tests/sshsig.rs` assert the same bytes).

This IO boundary does not prove the crypto implementation, process/OS byte
transport, or EUF-CMA/key custody. Those remain the explicit verifier and
custody assumptions of CredentialSignedEnvelopeController. No native reply
is deserialized as an authorization token.
-/
import Kernel.CredentialSignedEnvelopeController
import Compiler.NativeCoprocess

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

/-- A recorded run of the pinned native verifier: the exact `(publicKey, frame,
signature)` triples it answered `verified` on. Only `Oracle.recorded` consumes one,
and that oracle exists only at `Id` (a pure evaluation); the Host's receivers run
at `IO`, where the only oracle is the process (`Oracle.io_process`). Every transcript
in the tree is re-submitted to the pinned verifier by
`scripts/check-native-transcripts.sh` (each triple must read `verified`, the same
triple with one flipped signature byte `invalid`). -/
structure Transcript where
  verified : List (List UInt8 × List UInt8 × List UInt8)
  deriving DecidableEq, Repr

/-- A transcript answers only what the verifier answered: a recorded triple is
`verified`; any other triple has no verdict (`unavailable`), never `invalid` and
never `verified`. -/
def Transcript.answer (transcript : Transcript) (publicKey frame signature : List UInt8) :
    Except Error Bool :=
  if (publicKey, frame, signature) ∈ transcript.verified then .ok true
  else .error (.unavailable "the transcript holds no verdict for this signature")

theorem Transcript.answer_true_recorded {transcript : Transcript}
    {publicKey frame signature : List UInt8}
    (answered : transcript.answer publicKey frame signature = .ok true) :
    (publicKey, frame, signature) ∈ transcript.verified := by
  unfold Transcript.answer at answered
  split at answered
  · assumption
  · cases answered

theorem Transcript.answer_never_false (transcript : Transcript)
    (publicKey frame signature : List UInt8) :
    transcript.answer publicKey frame signature ≠ .ok false := by
  unfold Transcript.answer
  split <;> simp

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
        -- The binary's long-lived `serve` helper: the one-shot call's exact output.
        let output ← NativeCoprocess.output config.binary.toString
          #["verify", keyPath.toString, framePath.toString, signaturePath.toString]
        pure (parseOutput output)
    catch error => pure (.error (.unavailable s!"{error}"))

/-- `verify-sshsig`: the SSHSIG check of `signature` by the ssh-ed25519 key
`publicKey` over `message` under `nameSpace`.  Only the exact positive
response is `true`; the namespace must be non-empty (PROTOCOL.sshsig). -/
def verifySshsig (config : NativeConfig) (publicKey nameSpace message signature : List UInt8) :
    IO (Except Error Bool) :=
  if publicKey.length != 32 then pure (.error .publicKeyLength)
  else if signature.length != 64 then pure (.error .signatureLength)
  else
    try
      IO.FS.withTempDir fun directory => do
        let keyPath := directory / "public-key.bin"
        let namespacePath := directory / "namespace.bin"
        let messagePath := directory / "message.bin"
        let signaturePath := directory / "signature.bin"
        IO.FS.writeBinFile keyPath publicKey.toByteArray
        IO.FS.writeBinFile namespacePath nameSpace.toByteArray
        IO.FS.writeBinFile messagePath message.toByteArray
        IO.FS.writeBinFile signaturePath signature.toByteArray
        let output ← IO.Process.output
          { cmd := config.binary.toString
            args := #["verify-sshsig", keyPath.toString, namespacePath.toString,
              messagePath.toString, signaturePath.toString] }
        pure (parseOutput output)
    catch error => pure (.error (.unavailable s!"{error}"))

/-- The verdict of a recorded run: the same length checks as `verify`, then the
transcript's answer. -/
def recordedVerdict (transcript : Transcript) (publicKey frame signature : List UInt8) :
    Except Error Bool :=
  if publicKey.length != 32 then .error .publicKeyLength
  else if signature.length != 64 then .error .signatureLength
  else transcript.answer publicKey frame signature

/-- **Who answers a signature check.** A closed family, indexed by the monad the
admission runs in: `live` is the pinned native process and exists only at `IO`;
`recorded` is a recorded run of it and exists only at `Id`. The Host's receivers
run at `IO`, so the only oracle they can be handed is the process
(`Oracle.io_process`); a transcript can answer only a pure evaluation, such as
`Assurance.NativeAcceptedFixture`. Every receipt keeps `source` of the oracle that
answered it (`CredentialSignatureAdmission.CheckedSignature.source`). -/
inductive Oracle : (Type → Type) → Type where
  | live (config : NativeConfig) : Oracle IO
  | recorded (transcript : Transcript) : Oracle Id

/-- A pinned config is the live oracle (at `IO`, and nowhere else). -/
instance : Coe NativeConfig (Oracle IO) := ⟨Oracle.live⟩

/-- What a receipt records about the oracle that answered its signature check. -/
inductive Source where
  | process (binary : System.FilePath)
  | transcript (transcript : Transcript)
  /-- `oracle` answered the check for the Receiver, before the family's
  `prepare` ran; the receipt was built from the Receiver's voucher
  (`CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim`). -/
  | receiver (oracle : Source)
  deriving DecidableEq, Repr

def Oracle.source : {m : Type → Type} → Oracle m → Source
  | _, .live config => .process config.binary
  | _, .recorded transcript => .transcript transcript

def Oracle.check : {m : Type → Type} → Oracle m → (publicKey frame signature : List UInt8) →
    m (Except Error Bool)
  | _, .live config, publicKey, frame, signature => verify config publicKey frame signature
  | _, .recorded transcript, publicKey, frame, signature =>
      (recordedVerdict transcript publicKey frame signature : Except Error Bool)

/-- `IO` and `Id` are different monads: `IO Empty` has a value (a thrown error),
`Id Empty` has none. -/
theorem io_ne_id : (IO : Type → Type) ≠ Id := by
  intro same
  have thrown : Nonempty (IO Empty) := ⟨throw (IO.userError "")⟩
  rw [same] at thrown
  exact thrown.elim fun (value : Empty) => value.elim

/-- **At `IO` the oracle is the process.** Every oracle the Host's `IO` receivers
can be handed is `live`: its verdicts are the pinned binary's and its receipts
record `.process`. A transcript-backed receipt cannot be constructed at `IO`. -/
theorem Oracle.io_process (oracle : Oracle IO) :
    ∃ config : NativeConfig, oracle.source = .process config.binary ∧
      oracle.check = verify config := by
  suffices general : ∀ {m : Type → Type} (oracle : Oracle m) (atIO : m = IO),
      ∃ config : NativeConfig, oracle.source = .process config.binary ∧
        HEq oracle.check (verify config) from
    (general oracle rfl).elim fun config ⟨source, check⟩ => ⟨config, source, eq_of_heq check⟩
  intro m oracle atIO
  cases oracle with
  | live config => exact ⟨config, rfl, HEq.rfl⟩
  | recorded _ => exact absurd atIO.symm io_ne_id

/-- **A transcript answers only what the process answered**: a recorded oracle's
`true` is a triple in its transcript, and it never answers `false`. -/
theorem Oracle.recorded_true {transcript : Transcript} {publicKey frame signature : List UInt8}
    (answered : (Oracle.recorded transcript).check publicKey frame signature = .ok true) :
    (publicKey, frame, signature) ∈ transcript.verified := by
  simp only [Oracle.check, recordedVerdict] at answered
  split at answered
  · cases answered
  · split at answered
    · cases answered
    · exact Transcript.answer_true_recorded answered

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
