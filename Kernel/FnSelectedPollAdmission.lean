/-
Current gateway signature, pinned local consumer identity and accepted owner
release for one selected poll. This checked object is deliberately not yet a
durable admission: a verifier-minted unified frontier predecessor is also
required before event17 can advance Mini or authorize any fn ACK.
-/
import Kernel.FnConsumerFrontierGateway
import Kernel.FnSelectedPollReleaseLink
import Kernel.FnSelectedPollAdmissionAt

namespace Minidregg.Kernel.FnSelectedPollAdmission

open Minidregg.Kernel
open Minidregg.Kernel.FnSelectedPollCoverage
open Minidregg.Compiler

set_option autoImplicit false

def context {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) :
    ResourceObservationAdmission.Context config.deployment :=
  (Minidregg.Compiler.ServedBasis.Ground.full _ verified.opened.directory verified.opened.authority)

def proposal (ingress : Ingress) : FnConsumerFrontierGateway.Proposal :=
  { domain := ingress.spec.domain
    semantics := ingress.spec.semantics
    application := ingress.spec.evidence.key.application
    subject := ingress.spec.gatewaySubject
    target := ingress.spec.gatewayTarget
    capability := ingress.spec.gatewayCapability
    canonicalSpec := specCodec.encode ingress.spec
    expectedAuthorityRoot := ingress.expectedAuthorityRoot
    expectedTargetRoot := ingress.expectedTargetRoot }

structure Checked {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) where
  private mk ::
  pin : NativeHost.FnGatewayPin
  pinExact : config.fnGateway = some pin
  current : FnGatewayPolicy.checkCurrent config verified.opened pin = .ok ()
  prepared : FnConsumerFrontierGateway.Prepared (context verified)
    config.profile config.federation
    (NativeHost.logicalHeight config verified.opened.durable) pin (proposal ingress)
  signature : FnConsumerFrontierGateway.Checked prepared ingress.gatewayEnvelope
  original : FnSelectedPollReleaseLink.Original
  originalExact : original.receipt = ingress.spec.evidence.releaseReceipt
  keyExact : FnSelectiveReleaseIngress.transactionId original.ingress =
    ingress.spec.evidence.releaseKey
theorem Checked.sound {config : NativeHost.Config} {target : NativeHost.Durable}
    {verified : NativeHostReplay.Verified config target} {ingress : Ingress}
    (checked : Checked verified ingress) :
    config.fnGateway = some checked.pin ∧
    FnGatewayPolicy.checkCurrent config verified.opened checked.pin = .ok () ∧
    FnConsumerFrontierGateway.authorize checked.prepared checked.signature.signature = some checked.signature.authorization ∧
    checked.original.receipt = ingress.spec.evidence.releaseReceipt ∧
    FnSelectiveReleaseIngress.transactionId checked.original.ingress =
      ingress.spec.evidence.releaseKey :=
  ⟨checked.pinExact, checked.current, checked.signature.authorized, checked.originalExact,
    checked.keyExact⟩

def check {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    IO (Except String (Checked verified ingress)) := do
  unless ingress.spec.evidence.valid && ingress.spec.keyMatchesGateway &&
      ingress.spec.domain == config.deployment.domain &&
      ingress.spec.semantics == config.profile.semantics &&
      ingress.gatewayEnvelope.length ≤ 4096 &&
      (ingressCodec.encode ingress).length ≤ 16384 &&
      ingress.expectedAuthorityRoot ==
        verified.opened.durable.snapshot.model.roots
          (CredentialAuthorityDomainReceiver.cellIdOf config.deployment) do
    return .error "selected fn poll testimony refused"
  let some pin := config.fnGateway
    | return .error "selected fn poll testimony refused"
  if pinExact : config.fnGateway = some pin then
    if current : FnGatewayPolicy.checkCurrent config verified.opened pin = .ok () then
      match FnConsumerFrontierGateway.prepare (context verified) config.profile
          config.federation (NativeHost.logicalHeight config verified.opened.durable)
          pin (proposal ingress) with
      | .error _ => return .error "selected fn poll testimony refused"
      | .ok prepared =>
          match ← FnConsumerFrontierGateway.check config.signature prepared
              ingress.gatewayEnvelope with
          | .error _ => return .error "selected fn poll testimony refused"
          | .ok signature =>
              let some original := FnSelectedPollReleaseLink.select verified
                  ingress.spec.evidence.releaseKey
                | return .error "selected fn poll testimony refused"
              if originalExact : original.receipt = ingress.spec.evidence.releaseReceipt then
                if keyExact : FnSelectiveReleaseIngress.transactionId original.ingress =
                    ingress.spec.evidence.releaseKey then
                  return .ok ⟨pin, pinExact, current, prepared, signature, original,
                    originalExact, keyExact⟩
                else return .error "selected fn poll testimony refused"
              else return .error "selected fn poll testimony refused"
    else return .error "selected fn poll testimony refused"
  else return .error "selected fn poll testimony refused"

/-- Live receiving uses only replay-minted cursor and owner-release evidence.
The lower `admitAt` is also used by the chronological verifier, but callers
cannot supply these two witnesses through this API. -/
structure AcceptedVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) where
  private mk ::
  cursor : FnConsumerFrontierCore.Cursor
  cursorExact : verified.frontierCursor ingress.spec.evidence.key = .ok cursor
  original : FnSelectedPollReleaseLink.Original
  originalExact : FnSelectedPollReleaseLink.select verified
    ingress.spec.evidence.releaseKey = some original
  registration : FnConsumerNamespaceHistory.Original
  registrationExact : verified.frontierRegistration ingress.spec.evidence.key
    ingress.spec.registrationReceipt = .ok registration
  lower : FnSelectedPollAdmissionAt.Accepted config verified.opened
    cursor original registration ingress
theorem AcceptedVerified.sound {config : NativeHost.Config} {target : NativeHost.Durable}
    {verified : NativeHostReplay.Verified config target} {ingress : Ingress}
    (accepted : AcceptedVerified verified ingress) :
    verified.frontierCursor ingress.spec.evidence.key = .ok accepted.cursor ∧
    FnSelectedPollReleaseLink.select verified ingress.spec.evidence.releaseKey =
      some accepted.original ∧
    verified.frontierRegistration ingress.spec.evidence.key
      ingress.spec.registrationReceipt = .ok accepted.registration ∧
    FnConsumerFrontierCore.checkAfter accepted.cursor (candidate ingress.spec) = .ok () :=
  ⟨accepted.cursorExact, accepted.originalExact, accepted.registrationExact,
    accepted.lower.frontierExact⟩

def admitVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    IO (Except String (AcceptedVerified verified ingress)) := do
  match cursorExact : verified.frontierCursor ingress.spec.evidence.key with
  | .error _ => return .error "selected fn poll frontier refused"
  | .ok cursor =>
      match originalExact : FnSelectedPollReleaseLink.select verified
          ingress.spec.evidence.releaseKey with
      | none => return .error "selected fn poll owner release absent"
      | some original =>
          match registrationExact : verified.frontierRegistration
              ingress.spec.evidence.key ingress.spec.registrationReceipt with
          | .error _ => return .error "selected fn poll registration refused"
          | .ok registration =>
              match ← FnSelectedPollAdmissionAt.admitAt config verified.opened cursor
                  original registration ingress with
              | .error reason => return .error reason
              | .ok lower => return .ok ⟨cursor, cursorExact, original,
                  originalExact, registration, registrationExact, lower⟩

def AcceptedVerified.intent {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress)
    (accepted : AcceptedVerified verified ingress) :
    DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  accepted.lower.intent config verified.opened accepted.cursor accepted.original
    accepted.registration ingress

end Minidregg.Kernel.FnSelectedPollAdmission
