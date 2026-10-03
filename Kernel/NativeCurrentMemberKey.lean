/- Rooted current recipient authentication. Actual chronological native source
admission, source current key/standing and deployment-pinned strict Ed25519
verification are required. There is no decoder for Authenticated and no remote
pubkey/Boolean callback. A serialized result still needs a closed independently
pinned local verifier/custody-point consumer; it is not a remote trust anchor. -/
import Compiler.CurrentRecipientRecord
import Kernel.NativeHostReplay
namespace Minidregg.Kernel.NativeCurrentMemberKey
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

/-- The existing independent client continuity point, not an operator's new
claim about what is current. The closed physical consumer owns this input. -/
structure Point where
  height : Nat
  root : Digest
  deriving DecidableEq

structure Selected (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) where
  private mk ::
  source : NativeHostReplay.Verified config target
  heightExact : source.opened.durable.image.accepted.length = point.height
  rootExact : source.opened.durable.worldRoot = point.root
  bounded : CurrentRecipientRecord.bounded claim
  key : KeyRecord
  current : CredentialAuthorityState.currentSigningKey source.opened.authority.snapshot.logical
    claim.member = some key
  standing : CredentialAuthorityState.keyStanding source.opened.authority.snapshot.cell
    (CredentialAuthorityState.signingKeyRevocation key) = .live
  algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm
  keyExact : key.keyEpoch = claim.epoch ∧ key.publicKey = claim.signingKey
  activation : key.activeFrom ≤ source.opened.authority.snapshot.revision ∧
    source.opened.authority.snapshot.revision ≤ key.activeUntil

def select (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) : IO (Except String (Selected config target point claim)) := do
  match ← NativeHostReplay.verifyLoaded config target with
  | .error failure => return .error s!"source audit failed at {failure.index}: {failure.detail}"
  | .ok source =>
    if heightExact : source.opened.durable.image.accepted.length = point.height then
      if rootExact : source.opened.durable.worldRoot = point.root then
        if bounded : CurrentRecipientRecord.bounded claim then
          match current : CredentialAuthorityState.currentSigningKey source.opened.authority.snapshot.logical claim.member with
          | none => return .error "no current member signing key"
          | some key =>
            if standing : CredentialAuthorityState.keyStanding source.opened.authority.snapshot.cell
                (CredentialAuthorityState.signingKeyRevocation key) = .live then
              if algorithm : key.algorithm = CredentialSignatureAdmission.ed25519Algorithm then
                if keyExact : key.keyEpoch = claim.epoch ∧ key.publicKey = claim.signingKey then
                  if activation : key.activeFrom ≤ source.opened.authority.snapshot.revision ∧
                      source.opened.authority.snapshot.revision ≤ key.activeUntil then
                    return .ok ⟨source,heightExact,rootExact,bounded,key,current,standing,algorithm,keyExact,activation⟩
                  else return .error "member signing key inactive"
                else return .error "member signing key changed"
              else return .error "unsupported member signing algorithm"
            else return .error "member signing key revoked or unregistered"
        else return .error "noncanonical recipient record"
      else return .error "current source root differs from continuity point"
    else return .error "current source height differs from continuity point"

structure Authenticated (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) where
  private mk ::
  selected : Selected config target point claim

/-- Native process success is an explicit effect boundary, not a crypto theorem.
Only the operator-pinned config.signature helper is used, after source selection. -/
def authenticate (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) : IO (Except String (Authenticated config target point claim)) := do
  match ← select config target point claim with
  | .error detail => return .error detail
  | .ok selected =>
    match ← CredentialSignatureIO.verify config.signature selected.key.publicKey
        (CurrentRecipientRecord.statement claim) claim.signature with
    | .error _ => return .error "recipient signature verifier unavailable or malformed"
    | .ok false => return .error "invalid recipient signature"
    | .ok true => return .ok ⟨selected⟩

theorem authenticated_current (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) (accepted : Authenticated config target point claim) :
    CredentialAuthorityState.currentSigningKey accepted.selected.source.opened.authority.snapshot.logical
      claim.member = some accepted.selected.key := accepted.selected.current

theorem authenticated_root (config : Config) (target : Durable) (point : Point)
    (claim : CurrentRecipientRecord.Claim) (accepted : Authenticated config target point claim) :
    accepted.selected.source.opened.durable.worldRoot = point.root := accepted.selected.rootExact
#assert_axioms authenticated_current
#assert_axioms authenticated_root
end Minidregg.Kernel.NativeCurrentMemberKey
