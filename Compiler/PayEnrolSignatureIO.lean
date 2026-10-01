/-
# Compiler.PayEnrolSignatureIO — the two possession checks of an enrollment memo

`Checked mint enrolAddress memo` is the only source of the `Verified` bits
`PayEnrolDecision.decideEnrol` consumes.  Its constructor is private and its
one producer, `verifyNative`, runs the pinned native verifier twice on
exactly this memo:

* `verify` (Ed25519, `verify_strict`) of `memo.miniSig` by `memo.miniKey` over
  `PayEnrolMemo.miniFrame mint enrolAddress memo`;
* `verify-sshsig` of `memo.sshSig` by `memo.sshKey` under namespace
  `dregg-enrol@v1` over `PayEnrolMemo.sshsigMessage mint enrolAddress memo`.

A native error (unavailable binary, malformed response) is an `Error`, never
a `false`: an infrastructure failure must refuse the observation (nothing is
consumed), not journal the friend's payment as `miniSigInvalid`.

What stays assumed is stated as structures, deliberately not inhabited here
(the `CredentialSignatureAdmission.NativeIORefinement` pattern): the process
transport returns the verifier's result (`SshsigIORefinement`), and a
`true` from `verify-sshsig` means an Ed25519 signature over
`sshsigSignedData namespace (sha512 message)` for the real SHA-512
(`SshsigRefinement`, which names SHA-512 as a parameter because Lean has none).
-/
import Compiler.CredentialSignatureIO
import Kernel.PayEnrolDecision

namespace Minidregg.Compiler.PayEnrolSignatureIO

open Minidregg.Kernel.PayTariff (Address32)
open Minidregg.Kernel.PayEnrolMemo
open Minidregg.Kernel.PayEnrolDecision (Verified)

set_option autoImplicit false

/-- The native answers for one memo under one mint and enrollment address. -/
structure Checked (mint enrolAddress : Address32) (memo : Memo) where
  private mk ::
  verifier : CredentialSignatureIO.NativeConfig
  verified : Verified

def verifyNative (config : CredentialSignatureIO.NativeConfig) (mint enrolAddress : Address32)
    (memo : Memo) : IO (Except CredentialSignatureIO.Error (Checked mint enrolAddress memo)) := do
  match ← CredentialSignatureIO.verify config memo.miniKey (miniFrame mint enrolAddress memo)
      memo.miniSig with
  | .error error => return .error error
  | .ok mini =>
      match ← CredentialSignatureIO.verifySshsig config memo.sshKey sshsigNamespace
          (sshsigMessage mint enrolAddress memo) memo.sshSig with
      | .error error => return .error error
      | .ok ssh => return .ok ⟨config, ⟨mini, ssh⟩⟩

/-- The process transport returns what the verifier computes, for both verbs. -/
structure SshsigIORefinement
    (config : CredentialSignatureIO.NativeConfig)
    (Returned : CredentialSignatureIO.NativeConfig → List UInt8 → List UInt8 → List UInt8 →
      List UInt8 → Except CredentialSignatureIO.Error Bool → Prop)
    (verify : List UInt8 → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool) : Prop where
  exactResult : ∀ publicKey nameSpace message signature result,
    Returned config publicKey nameSpace message signature result →
      verify publicKey nameSpace message signature = result

/-- A positive `verify-sshsig` is an Ed25519 signature over the SSHSIG signed
data with the real SHA-512 (`sha512`), under the given key. -/
structure SshsigRefinement
    (verify : List UInt8 → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool)
    (sha512 : List UInt8 → List UInt8)
    (Authenticates : List UInt8 → List UInt8 → List UInt8 → Prop) : Prop where
  sound : ∀ publicKey nameSpace message signature,
    verify publicKey nameSpace message signature = .ok true →
      Authenticates publicKey (sshsigSignedData nameSpace (sha512 message)) signature

/-- What the receipt's `ssh` bit claims, once both refinements are supplied:
the ssh key authenticated the SSHSIG signed data of this memo's message. -/
theorem ssh_bit_authenticates
    {verify : List UInt8 → List UInt8 → List UInt8 → List UInt8 →
      Except CredentialSignatureIO.Error Bool}
    {sha512 : List UInt8 → List UInt8} {Authenticates : List UInt8 → List UInt8 → List UInt8 → Prop}
    (refinement : SshsigRefinement verify sha512 Authenticates)
    (mint enrolAddress : Address32) (memo : Memo)
    (returned : verify memo.sshKey sshsigNamespace (sshsigMessage mint enrolAddress memo)
      memo.sshSig = .ok true) :
    Authenticates memo.sshKey
      (sshsigSignedData sshsigNamespace (sha512 (sshsigMessage mint enrolAddress memo)))
      memo.sshSig :=
  refinement.sound _ _ _ _ returned

#assert_axioms ssh_bit_authenticates

end Minidregg.Compiler.PayEnrolSignatureIO
