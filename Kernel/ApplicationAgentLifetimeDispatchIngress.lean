/-
The distinct event26 carrier for an app-authorized lifetime agent route. The
old event21 carrier remains generation-bound and byte-for-byte unchanged.
These bytes select a historical event27 grant and a current, signed read of
its ordinary content resource; neither selector is an admission certificate.
-/
import Kernel.ApplicationAgentLifetimeGrantIntentTemplate
import Kernel.ApplicationDispatchAgentIngress

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext

set_option autoImplicit false

structure Ingress where
  dispatch : ApplicationDispatchAgentIngress.Ingress
  grantIssueIndex : Nat
  grantResource : Nat
  grantRoot : Digest
  grantObserveCapability : CapabilityId
  grantObservationEnvelope : List UInt8

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAgentIngress.ingressStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              bytesStream)))))
    (fun ingress => (ingress.dispatch, ingress.grantIssueIndex,
      ingress.grantResource, ingress.grantRoot,
      ingress.grantObserveCapability, ingress.grantObservationEnvelope))
    (fun (dispatch, grantIssueIndex, grantResource, grantRoot,
          grantObserveCapability, grantObservationEnvelope) =>
      ⟨dispatch, grantIssueIndex, grantResource, grantRoot,
        grantObserveCapability, grantObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def codec : LawfulCodec Ingress := ResourceBirthCodec.strictCodec
  (Minidregg.Compiler.NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-INGRESS/v1".toUTF8.toList
    ingressStream)

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 :=
  codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress :=
  codec.decode_encode ingress

theorem canonicalBytes_injective : Function.Injective Ingress.canonicalBytes := by
  intro left right same
  have decoded := congrArg codec.decode same
  exact Option.some.inj (by simpa only [decode_encode] using decoded)

/-- The event's exact canonical source is distinct from both event21 dispatch
and event27 grant issue. The underlying dispatch still carries the complete
HTTP request and the exact original reserve context. -/
def event (ingress : Ingress) : StableEvent where
  codecVersion := 26
  domain := ingress.dispatch.dispatch.dispatch.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

/-- Only the execution generation is fresh. The installed ticket/session
retain their original source-authored origin; they are never rewritten to
the new parent generation. Historical event22 and event27 provenance must
be supplied separately by the verifier's chronological Replay walk. -/
def matchesRoute (ingress : Ingress)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (originalTicketResource certifiedGrantIssueIndex : Nat) : Bool :=
  let paid := ingress.dispatch
  let base := paid.dispatch
  let context := paid.reserveContext
  decide (ingress.grantResource = grant.source.resource ∧
    ingress.grantIssueIndex = certifiedGrantIssueIndex ∧
    certifiedGrantIssueIndex > grant.source.issueIndex ∧
    ingress.grantObserveCapability = grant.participant.grantObserveCapability ∧
    context.domain = base.dispatch.domain ∧
    context.semantics = base.dispatch.semantics ∧
    context.app = base.dispatch.dispatch.app ∧
    context.session = base.dispatch.dispatch.session ∧
    context.ticketResource = originalTicketResource ∧
    context.ticketRoot = base.ticketRoot ∧
    context.httpOperationId = base.dispatch.dispatch.request.operationId ∧
    context.requestDigest = ApplicationDispatchCodec.requestDigest
      base.dispatch.dispatch.request ∧
    base.parent.map (fun parent => (parent.task, parent.state.generation)) =
      some (context.parentTask, context.parentGeneration) ∧
    context.parentTask = grant.participant.parentTask ∧
    context.session.origin = .agent grant.participant.parentTask
      grant.participant.originalGeneration ∧
    base.dispatch.dispatch.app.resource = grant.participant.app ∧
    base.dispatch.dispatch.session.resource = grant.participant.session ∧
    base.dispatch.dispatch.session.subject = grant.participant.subject)

theorem matchesRoute_request (ingress : Ingress)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (originalTicketResource certifiedGrantIssueIndex : Nat)
    (matched : matchesRoute ingress grant originalTicketResource
      certifiedGrantIssueIndex = true) :
    ingress.dispatch.reserveContext.httpOperationId =
      ingress.dispatch.dispatch.dispatch.dispatch.request.operationId ∧
    ingress.dispatch.reserveContext.requestDigest =
      ApplicationDispatchCodec.requestDigest
        ingress.dispatch.dispatch.dispatch.dispatch.request := by
  simp only [matchesRoute, decide_eq_true_eq] at matched
  aesop

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress
