/-
The distinct event26 carrier for an app-authorized lifetime agent route. It
retains the complete app dispatch and grant-bound v3 reserve/payer selectors.
Event21's v2 carrier and old ticket/session origin stay byte-for-byte intact.
-/
import Kernel.ApplicationAgentLifetimeDispatchReserveContext
import Kernel.ApplicationDispatchAdmissionIngress

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  dispatch : ApplicationDispatchAdmissionIngress.Ingress
  reserveContext : ApplicationAgentLifetimeDispatchReserveContext.Context
  reserveIndex : Nat
  payerCapability : CapabilityId
  payerObserve : CapabilityId
  payerSigned : DeclaredResourceController.SignedCommand
  grantRoot : Digest
  grantObserveCapability : CapabilityId
  grantObservationEnvelope : List UInt8

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAdmissionIngress.ingressStream
      (StreamCodec.product ApplicationAgentLifetimeDispatchReserveContext.contextStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product NativeHostCodec.signedInvocationStream
                (StreamCodec.product digestStream
                  (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                    bytesStream))))))))
    (fun ingress => (ingress.dispatch, ingress.reserveContext,
      ingress.reserveIndex, ingress.payerCapability, ingress.payerObserve,
      ingress.payerSigned, ingress.grantRoot, ingress.grantObserveCapability,
      ingress.grantObservationEnvelope))
    (fun (dispatch, reserveContext, reserveIndex, payerCapability,
          payerObserve, payerSigned, grantRoot, grantObserveCapability,
          grantObservationEnvelope) =>
      ⟨dispatch, reserveContext, reserveIndex, payerCapability, payerObserve,
        payerSigned, grantRoot, grantObserveCapability,
        grantObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def codec : LawfulCodec Ingress := ResourceBirthCodec.strictCodec
  (NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-INGRESS/v1".toUTF8.toList
    ingressStream)

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem canonicalBytes_injective : Function.Injective Ingress.canonicalBytes := by
  intro left right same
  have decoded := congrArg codec.decode same
  exact Option.some.inj (by simpa only [decode_encode] using decoded)

def event (ingress : Ingress) : StableEvent where
  codecVersion := 26
  domain := ingress.dispatch.dispatch.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

/-- The v3 reserve names the exact grant identity and original HTTP request.
Only current parent execution generation is independent from historical
ticket/session origin; the latter remains the exact event22 provenance. -/
def matchesRoute (ingress : Ingress)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (originalTicketResource certifiedGrantIssueIndex : Nat) : Bool :=
  let base := ingress.dispatch
  let context := ingress.reserveContext.base
  ApplicationAgentLifetimeDispatchReserveContext.matchesGrant ingress.reserveContext
    grant certifiedGrantIssueIndex &&
  decide (certifiedGrantIssueIndex > grant.source.issueIndex ∧
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
    ingress.reserveContext.base.httpOperationId =
      ingress.dispatch.dispatch.dispatch.request.operationId ∧
    ingress.reserveContext.base.requestDigest =
      ApplicationDispatchCodec.requestDigest
        ingress.dispatch.dispatch.dispatch.request := by
  simp only [matchesRoute, Bool.and_eq_true, decide_eq_true_eq] at matched
  aesop

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress
