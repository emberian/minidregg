/-
Read-only continuation authority for one already admitted physical stream.
This reuses current signed dispatch admission and verifier-owned chronological
share provenance, but never turns the checked candidate into a pending event,
CAS, delivery permit, app RPC, or billing record. The reserved signed probe
shape is explicitly refused by the live op34 delivery receiver.
-/
import Compiler.ApplicationReceivingDomain
import Kernel.ApplicationDispatchProjection

namespace Minidregg.Kernel.ApplicationStreamContinuity

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Binding where
  app : Nat
  appGeneration : Int
  session : Nat
  sessionGeneration : Int
  subject : Nat
  ticketResource : Nat
  fingerprint : Digest
  deriving DecidableEq

def bindingStream : StreamCodec Binding :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product intStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product intStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat digestStream))))))
    (fun b => (b.app, b.appGeneration, b.session, b.sessionGeneration,
      b.subject, b.ticketResource, b.fingerprint))
    (fun (app, generation, session, sessionGeneration, subject, ticket, fingerprint) =>
      ⟨app, generation, session, sessionGeneration, subject, ticket, fingerprint⟩)
    (by intro b; cases b; rfl)

structure Challenge where
  domain : Digest
  semantics : Digest
  binding : Binding
  streamNonce : List UInt8
  attemptNonce : List UInt8
  minimumHeight : Nat
  minimumWorldRoot : Digest
  deriving DecidableEq

def challengeStream : StreamCodec Challenge :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product bindingStream
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream
              (StreamCodec.product StreamCodec.nat digestStream))))))
    (fun c => (c.domain, c.semantics, c.binding, c.streamNonce, c.attemptNonce,
      c.minimumHeight, c.minimumWorldRoot))
    (fun (domain, semantics, binding, stream, attempt, height, root) =>
      ⟨domain, semantics, binding, stream, attempt, height, root⟩)
    (by intro c; cases c; rfl)

def challengeCodec : LawfulCodec Challenge :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.streamContinuityChallengeFrame challengeStream

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 97 + n - 10)

def hexBytes (bytes : List UInt8) : List UInt8 :=
  (String.ofList <| bytes.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]).toUTF8.toList

/-- Reserved for signed read-only probes; never offered to an app. -/
def probeProtocol : List UInt8 := ApplicationReceivingDomain.streamContinuityProbeProtocol

def routeAdmissionProtocol : List UInt8 := ApplicationReceivingDomain.routeAdmissionProbeProtocol

def reservedProbe (request : ApplicationDispatchCodec.Request) : Bool :=
  request.headers.any (fun h =>
    h.name == ApplicationDispatchAdmission.webSocketProtocolHeader &&
      (h.value == probeProtocol || h.value == routeAdmissionProtocol))

/-- The complete domain-separated challenge is inside signed request bytes.
The operation id is not a new Mini event id: this receiver commits nothing. -/
def probeRequest (challenge : Challenge) : ApplicationDispatchCodec.Request :=
  { operationId := 0
    method := ApplicationDispatchAdmission.streamedOpenMethod
    path := []
    query := hexBytes (challengeCodec.encode challenge)
    headers := [⟨ApplicationDispatchAdmission.webSocketProtocolHeader, probeProtocol, false⟩]
    body := [] }

theorem probe_reserved (challenge : Challenge) :
    reservedProbe (probeRequest challenge) = true := by
  simp [reservedProbe, probeRequest]

structure Request where
  challenge : Challenge
  ingress : List UInt8
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product challengeStream bytesStream)
    (fun r => (r.challenge, r.ingress)) (fun (c, i) => ⟨c, i⟩)
    (by intro r; cases r; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.streamContinuityRequestFrame requestStream

structure Tip where
  height : Nat
  chain : Digest
  worldRoot : Digest
  deriving DecidableEq

def tipStream : StreamCodec Tip :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream digestStream))
    (fun t => (t.height, t.chain, t.worldRoot)) (fun (h, c, r) => ⟨h, c, r⟩)
    (by intro t; cases t; rfl)

def attestationCodec : LawfulCodec (Challenge × Tip) :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.streamContinuityAttestationFrame
    (StreamCodec.product challengeStream tipStream)

def bindingFor {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress) : Binding :=
  let d := ingress.dispatch.dispatch
  ⟨d.app.resource, d.app.generation, d.session.resource, d.session.generation,
    d.session.subject.value, admitted.prior.evidence.spec.ticket.resource,
    admitted.checked.checked.sessionFingerprint⟩

def tipFor {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target) : Tip :=
  ⟨old.opened.durable.image.accepted.length, old.opened.durable.chain,
    old.opened.durable.worldRoot⟩

def minimumCurrent (challenge : Challenge) (tip : Tip) : Bool :=
  decide (challenge.minimumHeight ≤ tip.height) &&
    (challenge.minimumHeight != tip.height || challenge.minimumWorldRoot == tip.worldRoot)

/-- No decoded JSON or unsigned plan constructs this. The exact fresh signed
probe is admitted against one verifier-owned chronological current image. -/
structure Attestation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  challenge : Challenge
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  admitted : NativeHostReplay.DispatchAt config old.opened ingress
  namespaceExact : challenge.domain = config.deployment.domain ∧
    challenge.semantics = config.profile.semantics
  noncesExact : challenge.streamNonce.length = 32 ∧ challenge.attemptNonce.length = 32
  humanWeb : ingress.dispatch.dispatch.session.origin = .human ∧
    ingress.dispatch.dispatch.session.kind = .web
  signedChallenge : ingress.dispatch.dispatch.request = probeRequest challenge
  bindingExact : bindingFor admitted = challenge.binding
  minimumExact : minimumCurrent challenge (tipFor old) = true

/-- Renewal retains the same verified image; it does not extend history. -/
def Attestation.verified {config : Config} (a : Attestation config) :
    NativeHostReplay.Verified config a.target := a.old

theorem Attestation.receipts_unchanged {config : Config} (a : Attestation config) :
    a.verified.receipts = a.old.receipts := rfl

theorem Attestation.image_unchanged {config : Config} (a : Attestation config) :
    a.verified.opened.durable.image.accepted = a.old.opened.durable.image.accepted := rfl

theorem Attestation.exact_current_binding {config : Config} (a : Attestation config) :
    bindingFor a.admitted = a.challenge.binding := a.bindingExact

theorem Attestation.challenge_is_signed {config : Config} (a : Attestation config) :
    a.ingress.dispatch.dispatch.request = probeRequest a.challenge := a.signedChallenge

/-- Inspection is representation only. The physical receiver must retain the
private pinned op152 provenance and compare the exact frame and challenge. -/
def inspectBytes (bytes : List UInt8) : Option (Challenge × Tip) :=
  attestationCodec.decode bytes

private def Attestation.canonicalBytes {config : Config} (a : Attestation config) : List UInt8 :=
  attestationCodec.encode (a.challenge, tipFor a.old)

/-- Exactly the current verified log entry and its MAC must still be the
physical tip. Only read/key are used; no append, checkpoint, initialization,
app RPC or billing operation occurs. This is point-in-time, not a lock against
later revocation. The physical lease must keep its bounded fallback. -/
def withOpenedFreshTip {config : Config} {α : Type}
    (opened : Opened config) (handoff : IO α) : IO (Except String α) := do
  let durable := opened.durable
  let some record := durable.image.accepted.getLast?
    | return .error "authority handoff requires nonempty history"
  let .ok key ← config.transport.key
    | return .error "authority physical key unavailable"
  let entry : DurableReceiverIO.Entry :=
    ⟨DurableCheckpointCodec.recordFrame.encode record,
      DurableCheckpointCodec.entryTag key durable.image.accepted.length durable.chain⟩
  let .ok current ← DurableReceiverIO.tipIs config.transport
      durable.image.accepted.length entry
    | return .error "authority physical tip unavailable"
  if current then return .ok (← handoff)
  else return .error "authority physical tip changed before handoff"

def withVerifiedFreshTip {config : Config} {target : Durable} {α : Type}
    (old : NativeHostReplay.Verified config target) (handoff : IO α) :
    IO (Except String α) := withOpenedFreshTip old.opened handoff

def Attestation.withFreshTip {config : Config} {α : Type} (a : Attestation config)
    (handoff : List UInt8 → IO α) : IO (Except String α) :=
  withVerifiedFreshTip a.old (handoff a.canonicalBytes)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO (Except String (Attestation config)) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical stream continuity request"
  let challenge := request.challenge
  if namespaceExact : challenge.domain = config.deployment.domain ∧
      challenge.semantics = config.profile.semantics then
    if noncesExact : challenge.streamNonce.length = 32 ∧ challenge.attemptNonce.length = 32 then
      let some ingress := ApplicationDispatchAdmissionIngress.codec.decode request.ingress
        | return .error "noncanonical continuity signed ingress"
      if humanWeb : ingress.dispatch.dispatch.session.origin = .human ∧
          ingress.dispatch.dispatch.session.kind = .web then
        if signedChallenge : ingress.dispatch.dispatch.request = probeRequest challenge then
          let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
            | return .error "current stream continuation authority refused"
          if bindingExact : bindingFor admitted = challenge.binding then
            if minimumExact : minimumCurrent challenge (tipFor old) = true then
              return .ok ⟨target, old, challenge, ingress, admitted, namespaceExact,
                noncesExact, humanWeb, signedChallenge, bindingExact, minimumExact⟩
            else return .error "continuity tip regressed below stream watermark"
          else return .error "continuity current projection or custody changed"
        else return .error "continuity challenge differs from signed request"
      else return .error "continuity requires a human web stream"
    else return .error "continuity requires two 32-byte nonces"
  else return .error "continuity namespace differs from pinned source"

theorem challenge_decode_encode (c : Challenge) :
    challengeCodec.decode (challengeCodec.encode c) = some c := challengeCodec.decode_encode c

theorem request_decode_encode (r : Request) :
    requestCodec.decode (requestCodec.encode r) = some r := requestCodec.decode_encode r

theorem attestation_decode_encode (c : Challenge) (t : Tip) :
    inspectBytes (attestationCodec.encode (c, t)) = some (c, t) :=
  attestationCodec.decode_encode (c, t)

#assert_axioms probe_reserved
#assert_axioms Attestation.receipts_unchanged
#assert_axioms Attestation.image_unchanged
#assert_axioms Attestation.exact_current_binding
#assert_axioms Attestation.challenge_is_signed
#assert_axioms challenge_decode_encode
#assert_axioms request_decode_encode
#assert_axioms attestation_decode_encode

end Minidregg.Kernel.ApplicationStreamContinuity
