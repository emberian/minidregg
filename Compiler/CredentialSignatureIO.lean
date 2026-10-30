/-
# Compiler.CredentialSignatureIO — opaque native Ed25519 verification

The live verifier is the source/version-pinned Ed25519 kernel in
`native/mini-kernels` (ed25519-dalek 2.2.0 `verify_strict`), linked into the
Host and called through the same C shim pattern as the cSHAKE/KMAC kernels. It
receives only a 32-byte public key, the exact Lean frame, and a 64-byte detached
signature. It cannot select authority or parse a semantic request. Only its
exact positive verdict is `true`; malformed inputs and unknown verdict codes
refuse.

The same kernel checks an OpenSSH SSHSIG signature (PROTOCOL.sshsig) by an
ssh-ed25519 key: it receives the 32-byte key, the namespace, the message and the
raw 64-byte signature, computes SHA-512 of the message (Lean has no SHA-512) and
verifies strictly over `Kernel.PayEnrolMemo.sshsigSignedData namespace (SHA-512
message)`. The native boundary therefore grows by exactly one hash, and every
other byte of the signed data is fixed in Lean
(`PayEnrolMemo.sshsig_signed_data_fixture` and the Rust tests assert the same
bytes).

This IO boundary does not prove the crypto implementation or EUF-CMA/key
custody. Those remain the explicit verifier and custody assumptions of
CredentialSignedEnvelopeController. No native reply is deserialized as an
authorization token. The legacy `NativeConfig.binary` remains only for retained
artifact pinning in the carry protocols; live verification never reads it.
-/
module

public import Kernel.CredentialSignedEnvelopeController
public import Compiler.CredentialSignatureKernel

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Compiler.CredentialSignatureIO

set_option autoImplicit false

/-- Retained verifier-artifact identity used by the carry protocols. The live
in-process verifier does not consult this path. -/
structure NativeConfig where
  binary : System.FilePath

inductive Error where
  | publicKeyLength
  | signatureLength
  /-- Legacy wire variants: recorded refusal codecs still carry process-era
  errors, although the in-process verifier never constructs them. -/
  | processFailed (exitCode : UInt32) (detail : String)
  | malformedResponse
  | unavailable (detail : String)
  deriving DecidableEq, Repr

/-- The native ABI's three verdict codes. Any other code is refused. -/
def nativeVerified : UInt8 := 0
def nativeInvalid : UInt8 := 1
def nativeInputError : UInt8 := 2

/-- Translate the native verdict without turning an input failure or an
unrecognized code into either a Boolean verdict. -/
def decodeNativeVerdict (verdict : UInt8) : Except Error Bool :=
  if verdict == nativeVerified then .ok true
  else if verdict == nativeInvalid then .ok false
  else .error (.unavailable "mini-kernels 0.1.0 rejected the signature verification inputs")

/-- A recorded run of the pinned native verifier: the exact `(publicKey, frame,
signature)` triples it answered `verified` on. Only `Oracle.recorded` consumes
one, and that oracle exists only at `Id` (a pure evaluation); the Host's
receivers run at `IO`, where the only oracle is the linked native kernel
(`Oracle.io_native`). Every transcript in the tree is re-submitted to the pinned
verifier by `scripts/check-native-transcripts.sh` (each triple must read
`verified`, the same triple with one flipped signature byte `invalid`). -/
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

/-- The transcript that holds no verdict: every signature it is asked about is
`unavailable` (`Transcript.answer`), never `verified`. It is the oracle of a pure
evaluation that consults no verifier (a receiver's replay, a fixture whose families make
no signature claims). A named `Transcript`, so `scripts/NativeTranscripts.lean` lists it
(zero triples) instead of finding an anonymous `Transcript.mk` it could not re-verify. -/
def Transcript.empty : Transcript := ⟨[]⟩

theorem Transcript.empty_answers_nothing (publicKey frame signature : List UInt8) :
    (Transcript.empty.answer publicKey frame signature).toOption = none := by
  simp [Transcript.answer, Transcript.empty, Except.toOption]

#assert_axioms Transcript.empty_answers_nothing

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

/-- The one live check: no temporary files, helper process, or configured
executable. The length checks remain at the Lean boundary. -/
def verify (_config : NativeConfig) (publicKey frame signature : List UInt8) :
    IO (Except Error Bool) :=
  if publicKey.length != 32 then pure (.error .publicKeyLength)
  else if signature.length != 64 then pure (.error .signatureLength)
  else pure (decodeNativeVerdict
    (ed25519Kernel publicKey.toByteArray frame.toByteArray signature.toByteArray))

/-- The SSHSIG check of `signature` by the ssh-ed25519 key `publicKey` over
`message` under `nameSpace`. Only the exact positive native verdict is `true`;
the kernel retains PROTOCOL.sshsig's non-empty namespace check. -/
def verifySshsig (_config : NativeConfig) (publicKey nameSpace message signature : List UInt8) :
    IO (Except Error Bool) :=
  if publicKey.length != 32 then pure (.error .publicKeyLength)
  else if signature.length != 64 then pure (.error .signatureLength)
  else pure (decodeNativeVerdict
    (sshsigKernel publicKey.toByteArray nameSpace.toByteArray message.toByteArray
      signature.toByteArray))

/-- The verdict of a recorded run: the same length checks as `verify`, then the
transcript's answer. -/
def recordedVerdict (transcript : Transcript) (publicKey frame signature : List UInt8) :
    Except Error Bool :=
  if publicKey.length != 32 then .error .publicKeyLength
  else if signature.length != 64 then .error .signatureLength
  else transcript.answer publicKey frame signature

/-- **Who answers a signature check.** A closed family, indexed by the monad the
admission runs in: `live` is the linked native kernel and exists only at `IO`;
`recorded` is a recorded run of it and exists only at `Id`. The Host's receivers
run at `IO`, so the only oracle they can be handed is the native kernel
(`Oracle.io_native`); a transcript can answer only a pure evaluation, such as
`Fixtures.NativeAcceptedFixture`. Every receipt keeps `source` of the oracle that
answered it (`CredentialSignatureAdmission.CheckedSignature.source`). -/
inductive Oracle : (Type → Type) → Type where
  | live (config : NativeConfig) : Oracle IO
  | recorded (transcript : Transcript) : Oracle Id

/-- A native config selects the live oracle (at `IO`, and nowhere else); its
legacy artifact path is not a verifier implementation choice. -/
instance : Coe NativeConfig (Oracle IO) := ⟨Oracle.live⟩

/-- What a receipt records about the oracle that answered its signature check. -/
inductive Source where
  | native (kernel : String)
  | transcript (transcript : Transcript)
  /-- `oracle` answered the check for the Receiver, before the family's
  `prepare` ran; the receipt was built from the Receiver's voucher
  (`CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim`). -/
  | receiver (oracle : Source)
  deriving DecidableEq, Repr

/-- The receipt identity of the linked implementation. -/
def nativeKernel : String := "mini-kernels 0.1.0 (ed25519-dalek 2.2.0)"

def Oracle.source : {m : Type → Type} → Oracle m → Source
  | _, .live _ => .native nativeKernel
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

/-- **At `IO` the oracle is the linked native verifier.** Every oracle the
Host's `IO` receivers can be handed is `live`: its verdicts are `verify`'s and
its receipts record `.native nativeKernel`. A transcript-backed receipt cannot
be constructed at `IO`. -/
theorem Oracle.io_native (oracle : Oracle IO) :
    ∃ config : NativeConfig, oracle.source = .native nativeKernel ∧
      oracle.check = verify config := by
  suffices general : ∀ {m : Type → Type} (oracle : Oracle m) (atIO : m = IO),
      ∃ config : NativeConfig, oracle.source = .native nativeKernel ∧
        HEq oracle.check (verify config) from
    (general oracle rfl).elim fun config ⟨source, check⟩ => ⟨config, source, eq_of_heq check⟩
  intro m oracle atIO
  cases oracle with
  | live config => exact ⟨config, rfl, HEq.rfl⟩
  | recorded _ => exact absurd atIO.symm io_ne_id

/-- **A transcript answers only what the verifier answered**: a recorded
oracle's `true` is a triple in its transcript, and it never answers `false`. -/
theorem Oracle.recorded_true {transcript : Transcript} {publicKey frame signature : List UInt8}
    (answered : (Oracle.recorded transcript).check publicKey frame signature = .ok true) :
    (publicKey, frame, signature) ∈ transcript.verified := by
  simp only [Oracle.check, recordedVerdict] at answered
  split at answered
  · cases answered
  · split at answered
    · cases answered
    · exact Transcript.answer_true_recorded answered

/-- Exact positive verdict, replacing the process parser's exact-response theorem. -/
theorem decodeNative_true_exact (verdict : UInt8)
    (accepted : decodeNativeVerdict verdict = .ok true) :
    verdict = nativeVerified := by
  unfold decodeNativeVerdict at accepted
  split at accepted
  next verified => exact eq_of_beq verified
  next => split at accepted <;> cases accepted

theorem decodeNative_verified : decodeNativeVerdict nativeVerified = .ok true := by rfl

theorem decodeNative_invalid : decodeNativeVerdict nativeInvalid = .ok false := by rfl

theorem decodeNative_input_error_refuses :
    decodeNativeVerdict nativeInputError =
      .error (.unavailable "mini-kernels 0.1.0 rejected the signature verification inputs") := by
  rfl

theorem decodeNative_unknown_refuses :
    decodeNativeVerdict 3 =
      .error (.unavailable "mini-kernels 0.1.0 rejected the signature verification inputs") := by
  rfl

end Minidregg.Compiler.CredentialSignatureIO
