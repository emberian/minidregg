/-
Current configured gateway authority for an ordered empty fn page. This is
pre-admission only: the accepted special event19 must also advance the
verifier-minted shared frontier before any fn ACK is authorized.
-/
import Kernel.FnConsumerFrontierGateway
import Kernel.FnEmptyPollProgressV2
import Kernel.NativeHostReplay
import Kernel.FnEmptyPollAdmissionAtV2

namespace Minidregg.Kernel.FnEmptyPollAdmissionV2

open Minidregg.Kernel
open Minidregg.Kernel.FnEmptyPollProgressV2
open Minidregg.Compiler

set_option autoImplicit false

def context {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) :
    ResourceObservationAdmission.Context config.deployment verified.opened.durable :=
  ⟨verified.opened.directory, verified.opened.authority⟩

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

def check {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    IO (Except String (Checked verified ingress)) := do
  unless ingress.spec.evidence.valid && ingress.spec.keyMatchesGateway &&
      ingress.spec.domain == config.deployment.domain &&
      ingress.spec.semantics == config.profile.semantics &&
      ingress.gatewayEnvelope.length ≤ 4096 &&
      (ingressCodec.encode ingress).length ≤ 12288 &&
      ingress.expectedAuthorityRoot ==
        verified.opened.durable.snapshot.model.roots
          config.deployment.authorityAnchor.catalogueCellId do
    return .error "ordered empty fn page refused"
  let some pin := config.fnGateway
    | return .error "ordered empty fn page refused"
  if pinExact : config.fnGateway = some pin then
    if current : FnGatewayPolicy.checkCurrent config verified.opened pin = .ok () then
      match FnConsumerFrontierGateway.prepare (context verified) config.profile
          config.federation (NativeHost.logicalHeight config verified.opened.durable)
          pin (proposal ingress) with
      | .error _ => return .error "ordered empty fn page refused"
      | .ok prepared =>
          match ← FnConsumerFrontierGateway.check config.signature prepared
              ingress.gatewayEnvelope with
          | .error _ => return .error "ordered empty fn page refused"
          | .ok signature =>
              return .ok ⟨pin, pinExact, current, prepared, signature⟩
    else return .error "ordered empty fn page refused"
  else return .error "ordered empty fn page refused"

/-- The live transition obtains its predecessor only from exact native replay;
an arbitrary caller cursor cannot serve as acceptance authority. -/
structure AcceptedVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) where
  private mk ::
  cursor : FnConsumerFrontierCore.Cursor
  cursorExact : verified.frontierCursor ingress.spec.evidence.key = .ok cursor
  registration : FnConsumerNamespaceHistory.Original
  registrationExact : verified.frontierRegistration ingress.spec.evidence.key
    ingress.spec.registrationReceipt = .ok registration
  lower : FnEmptyPollAdmissionAtV2.Accepted config verified.opened cursor
    registration ingress

def admitVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    IO (Except String (AcceptedVerified verified ingress)) := do
  match cursorExact : verified.frontierCursor ingress.spec.evidence.key with
  | .error _ => return .error "ordered empty fn frontier refused"
  | .ok cursor =>
      match registrationExact : verified.frontierRegistration
          ingress.spec.evidence.key ingress.spec.registrationReceipt with
      | .error _ => return .error "ordered empty fn registration refused"
      | .ok registration =>
          match ← FnEmptyPollAdmissionAtV2.admitAt config verified.opened cursor
              registration ingress with
          | .error reason => return .error reason
          | .ok lower => return .ok ⟨cursor, cursorExact, registration,
              registrationExact, lower⟩

def AcceptedVerified.intent {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress)
    (accepted : AcceptedVerified verified ingress) :
    DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  accepted.lower.intent config verified.opened accepted.cursor
    accepted.registration ingress

end Minidregg.Kernel.FnEmptyPollAdmissionV2
