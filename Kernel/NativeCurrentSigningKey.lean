/- Current key selection below chronological replay. The witness is indexed by
the actual loaded authority of one source snapshot, so a release validator can
consume its Prepared.authority directly. This does not mint a mutation grant,
installation promise or release permit. Native signature verification remains
an explicit deployment-pinned effect boundary. -/
import Kernel.NativeHostContext

namespace Minidregg.Kernel.NativeCurrentSigningKey
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
set_option autoImplicit false

variable {deployment : CanonicalCellRegistry.Deployment}
  {physical : DurableDataIntent.DataSnapshot ResourceBirthCodec.rootBytes}

structure Selected (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey : List UInt8) where
  private mk ::
  key : KeyRecord
  current : CredentialAuthorityState.currentSigningKey loaded.snapshot.logical subject = some key
  standing : CredentialAuthorityState.keyStanding loaded.snapshot.cell
    (CredentialAuthorityState.signingKeyRevocation key) = .live
  algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm
  exactKey : key.keyEpoch = epoch ∧ key.publicKey = publicKey
  activation : key.activeFrom ≤ loaded.snapshot.revision ∧ loaded.snapshot.revision ≤ key.activeUntil

def select (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey : List UInt8) : Except String (Selected loaded subject epoch publicKey) :=
  match current : CredentialAuthorityState.currentSigningKey loaded.snapshot.logical subject with
  | none => .error "no current source signing key"
  | some key =>
    if standing : CredentialAuthorityState.keyStanding loaded.snapshot.cell
        (CredentialAuthorityState.signingKeyRevocation key) = .live then
      if algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm then
        if exactKey : key.keyEpoch = epoch ∧ key.publicKey = publicKey then
          if activation : key.activeFrom ≤ loaded.snapshot.revision ∧
              loaded.snapshot.revision ≤ key.activeUntil then
            .ok ⟨key,current,standing,algorithm,exactKey,activation⟩
          else .error "source signing key inactive"
        else .error "source signing key rotated or substituted"
      else .error "unsupported source signing algorithm"
    else .error "source signing key revoked or unregistered"

structure Verified (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey statement signature : List UInt8) where
  private mk ::
  selected : Selected loaded subject epoch publicKey

def verify (native : CredentialSignatureIO.NativeConfig)
    (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey statement signature : List UInt8) :
    IO (Except String (Verified loaded subject epoch publicKey statement signature)) := do
  match select loaded subject epoch publicKey with
  | .error reason => return .error reason
  | .ok selected =>
    match ← CredentialSignatureIO.verify native selected.key.publicKey statement signature with
    | .error _ => return .error "source signature verifier unavailable or malformed"
    | .ok false => return .error "invalid source signature"
    | .ok true => return .ok ⟨selected⟩

theorem selected_current (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey : List UInt8) (selected : Selected loaded subject epoch publicKey) :
    CredentialAuthorityState.currentSigningKey loaded.snapshot.logical subject = some selected.key :=
  selected.current

theorem selected_root (loaded : Loaded deployment physical) (subject : SubjectId)
    (epoch : Nat) (publicKey : List UInt8) (_selected : Selected loaded subject epoch publicKey) :
    CredentialAuthorityDomainReceiver.cellRoot loaded.snapshot.cell =
      physical.model.roots (CredentialAuthorityDomainReceiver.cellIdOf deployment) :=
  loaded.root_exact

#assert_axioms selected_current
#assert_axioms selected_root
end Minidregg.Kernel.NativeCurrentSigningKey
