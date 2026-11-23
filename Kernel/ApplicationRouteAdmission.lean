/- Read-only current authority to register a new immutable resident route.
This does not open an app stream. Every later request still requires dispatch.
Its challenge domain is distinct from continuation of an existing lease. -/
module

public import Compiler.ApplicationReceivingDomain
public import Kernel.ApplicationStreamContinuity

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

namespace Minidregg.Kernel.ApplicationRouteAdmission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationStreamContinuity (Binding Tip bindingFor tipFor)

set_option autoImplicit false

structure Selector where
  app : Nat
  appGeneration : Int
  session : Nat
  sessionGeneration : Int
  subject : Nat
  ticketResource : Nat
  kind : ApplicationDispatchCodec.InterfaceKind
  deriving DecidableEq

def selectorStream : StreamCodec Selector :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product intStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product intStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat ApplicationDispatchCodec.interfaceKindStream))))))
    (fun s => (s.app, s.appGeneration, s.session, s.sessionGeneration,
      s.subject, s.ticketResource, s.kind))
    (fun (app, generation, session, sessionGeneration, subject, ticket, kind) =>
      ⟨app, generation, session, sessionGeneration, subject, ticket, kind⟩)
    (by intro s; cases s; rfl)

def select (binding : Binding) (kind : ApplicationDispatchCodec.InterfaceKind) : Selector :=
  ⟨binding.app, binding.appGeneration, binding.session, binding.sessionGeneration,
    binding.subject, binding.ticketResource, kind⟩

structure Challenge where
  domain : Digest
  semantics : Digest
  selector : Selector
  registrationNonce : List UInt8
  deriving DecidableEq

def challengeStream : StreamCodec Challenge :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product selectorStream bytesStream)))
    (fun c => (c.domain, c.semantics, c.selector, c.registrationNonce))
    (fun (domain, semantics, selector, nonce) => ⟨domain, semantics, selector, nonce⟩)
    (by intro c; cases c; rfl)

def challengeCodec : LawfulCodec Challenge :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.routeAdmissionChallengeFrame challengeStream

def probeRequest (challenge : Challenge) : ApplicationDispatchCodec.Request :=
  { operationId := 0
    method := ApplicationDispatchAdmission.streamedOpenMethod
    path := []
    query := ApplicationStreamContinuity.hexBytes (challengeCodec.encode challenge)
    headers := [⟨ApplicationDispatchAdmission.webSocketProtocolHeader,
      ApplicationStreamContinuity.routeAdmissionProtocol, false⟩]
    body := [] }

theorem probe_reserved (challenge : Challenge) :
    ApplicationStreamContinuity.reservedProbe (probeRequest challenge) = true := by
  simp [ApplicationStreamContinuity.reservedProbe, probeRequest]

structure Request where
  challenge : Challenge
  ingress : List UInt8

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product challengeStream bytesStream)
    (fun r => (r.challenge, r.ingress)) (fun (c, i) => ⟨c, i⟩)
    (by intro r; cases r; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.routeAdmissionRequestFrame requestStream

def attestationCodec : LawfulCodec (Challenge × Binding × Tip) :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.routeAdmissionAttestationFrame
    (StreamCodec.product challengeStream
      (StreamCodec.product ApplicationStreamContinuity.bindingStream
        ApplicationStreamContinuity.tipStream))

structure Attestation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  challenge : Challenge
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  admitted : NativeHostReplay.DispatchAt config old.opened ingress
  namespaceExact : challenge.domain = config.deployment.domain ∧
    challenge.semantics = config.profile.semantics
  nonceExact : challenge.registrationNonce.length = 32
  human : ingress.dispatch.dispatch.session.origin = .human
  signedChallenge : ingress.dispatch.dispatch.request = probeRequest challenge
  selectorExact : select (bindingFor admitted) ingress.dispatch.dispatch.session.kind = challenge.selector
theorem Attestation.sound {config : Config} (a : Attestation config) :
    (a.challenge.domain = config.deployment.domain ∧
      a.challenge.semantics = config.profile.semantics) ∧
    a.ingress.dispatch.dispatch.request = probeRequest a.challenge ∧
    select (bindingFor a.admitted) a.ingress.dispatch.dispatch.session.kind = a.challenge.selector :=
  ⟨a.namespaceExact, a.signedChallenge, a.selectorExact⟩

def Attestation.verified {config : Config} (a : Attestation config) :
    NativeHostReplay.Verified config a.target := a.old

theorem Attestation.image_unchanged {config : Config} (a : Attestation config) :
    a.verified.opened.durable.image.accepted = a.old.opened.durable.image.accepted := rfl

theorem Attestation.receipts_unchanged {config : Config} (a : Attestation config) :
    a.verified.receipts = a.old.receipts := rfl

theorem Attestation.exact_current_binding {config : Config} (a : Attestation config) :
    select (bindingFor a.admitted) a.ingress.dispatch.dispatch.session.kind = a.challenge.selector := a.selectorExact

theorem Attestation.challenge_is_signed {config : Config} (a : Attestation config) :
    a.ingress.dispatch.dispatch.request = probeRequest a.challenge := a.signedChallenge

def Attestation.withFreshTip {config : Config} {α : Type} (a : Attestation config)
    (handoff : List UInt8 → IO α) : IO (Except String α) :=
  ApplicationStreamContinuity.withVerifiedFreshTip a.old
    (handoff (attestationCodec.encode (a.challenge, bindingFor a.admitted, tipFor a.old)))

private structure SignedProbe (config : Config) where
  challenge : Challenge
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  namespaceExact : challenge.domain = config.deployment.domain ∧
    challenge.semantics = config.profile.semantics
  nonceExact : challenge.registrationNonce.length = 32
  human : ingress.dispatch.dispatch.session.origin = .human
  signedChallenge : ingress.dispatch.dispatch.request = probeRequest challenge

private def signedProbe (config : Config) (bytes : List UInt8) : Except String (SignedProbe config) := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical route admission request"
  let challenge := request.challenge
  if namespaceExact : challenge.domain = config.deployment.domain ∧
      challenge.semantics = config.profile.semantics then
    if nonceExact : challenge.registrationNonce.length = 32 then
      let some ingress := ApplicationDispatchAdmissionIngress.codec.decode request.ingress
        | throw "noncanonical route signed ingress"
      if human : ingress.dispatch.dispatch.session.origin = .human then
        if signedChallenge : ingress.dispatch.dispatch.request = probeRequest challenge then
          return ⟨challenge, ingress, namespaceExact, nonceExact, human, signedChallenge⟩
        else throw "route challenge differs from signed request"
      else throw "route registration requires a human session"
    else throw "route registration requires a 32-byte nonce"
  else throw "route namespace differs from pinned source"

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO (Except String (Attestation config)) := do
  let ⟨challenge, ingress, namespaceExact, nonceExact, human, signedChallenge⟩ ← match signedProbe config bytes with
    | .error detail => return .error detail
    | .ok probe => pure probe
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
    | return .error "current route authority refused"
  if selectorExact : select (bindingFor admitted) ingress.dispatch.dispatch.session.kind = challenge.selector then
    return .ok ⟨target, old, challenge, ingress, admitted, namespaceExact,
      nonceExact, human, signedChallenge, selectorExact⟩
  else return .error "route current custody or generation changed"

/-- The callback is available only after the signed challenge and its binding were
re-admitted. It compares the physical tip again immediately before delivery. -/
def receiveLight {config : Config} (light : NativeHostLight.Light config) (bytes : ByteArray) :
    ExceptT String IO ((ByteArray → IO Unit) → IO (Except String Unit)) := do
  let probe ← signedProbe config bytes.toList
  let admitted ← ApplicationDispatchLight.admit config light probe.ingress
  let tip := ApplicationStreamContinuity.lightTip light
  let binding := ApplicationStreamContinuity.lightBinding admitted
  if select binding probe.ingress.dispatch.dispatch.session.kind != probe.challenge.selector then
    throw "route current custody or generation changed"
  return fun handoff => ApplicationStreamContinuity.withLightFreshTip light
    (handoff (attestationCodec.encode (probe.challenge, binding, tip)).toByteArray)

theorem challenge_decode_encode (c : Challenge) :
    challengeCodec.decode (challengeCodec.encode c) = some c := challengeCodec.decode_encode c

theorem request_decode_encode (r : Request) :
    requestCodec.decode (requestCodec.encode r) = some r := requestCodec.decode_encode r

theorem attestation_decode_encode (c : Challenge) (b : Binding) (t : Tip) :
    attestationCodec.decode (attestationCodec.encode (c, b, t)) = some (c, b, t) :=
  attestationCodec.decode_encode (c, b, t)

#assert_axioms probe_reserved
#assert_axioms Attestation.image_unchanged
#assert_axioms Attestation.receipts_unchanged
#assert_axioms Attestation.exact_current_binding
#assert_axioms Attestation.challenge_is_signed
#assert_axioms challenge_decode_encode
#assert_axioms request_decode_encode
#assert_axioms attestation_decode_encode

end Minidregg.Kernel.ApplicationRouteAdmission
