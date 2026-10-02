/-
Native possession boundary for quote-bound paid entry. Both checks bind the
entire v2 frame, including stable identity, current authorizing key/epoch,
next-key commitment, exact terms and processing-chain-hour expiry. A verifier
transport failure is not a negative possession result and cannot consume value.
-/
import Compiler.CredentialSignatureIO
import Kernel.PayEnrolMemoV2

namespace Minidregg.Compiler.PayEnrolSignatureV2IO

open Minidregg.Kernel.PayEnrolMemoV2
set_option autoImplicit false

structure Checked (context : Context) (memo : Memo) where
  private mk ::
  verifier : CredentialSignatureIO.NativeConfig
  mini : Bool
  ssh : Bool

def verifyNative (config : CredentialSignatureIO.NativeConfig) (context : Context)
    (memo : Memo) : IO (Except CredentialSignatureIO.Error (Checked context memo)) := do
  match ← CredentialSignatureIO.verify config memo.unsigned.authorizingKey
      (miniFrame context memo) memo.miniSignature with
  | .error error => return .error error
  | .ok mini =>
    match ← CredentialSignatureIO.verifySshsig config memo.unsigned.sshKey sshsigNamespace
        (sshsigMessage context memo) memo.sshSignature with
    | .error error => return .error error
    | .ok ssh => return .ok ⟨config, mini, ssh⟩

end Minidregg.Compiler.PayEnrolSignatureV2IO
