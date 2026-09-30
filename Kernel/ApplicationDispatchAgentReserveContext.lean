/-
Canonical context for a dedicated AgentGrain dispatch reserve. The reserve is
signed before the app dispatch, so this carrier contains a source-derived
digest of the fixed canonical request and exact resource coordinates rather
than the later dispatch signature or a duplicate HTTP body. Decoding it
does not prove a reserve, payer delegation, or permission to call the app.
-/
import Kernel.ApplicationDispatchAdmissionIngress

namespace Minidregg.Kernel.ApplicationDispatchAgentReserveContext

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

/-- One fixed participant request and the independently delegated payer.
The payer's signed ordinary reserve must use `payerSubject`; a later v2
admission must also verify its current delegation to this exact scope. -/
structure Context where
  domain : Digest
  semantics : Digest
  app : App
  session : Session
  ticketResource : Nat
  ticketRoot : Digest
  parentTask : Nat
  parentGeneration : Int
  purseTask : Nat
  purseGeneration : Int
  payerSubject : SubjectId
  reserveAmount : Int
  maximumCharge : Int
  reserveOperationId : Nat
  httpOperationId : Nat
  requestDigest : Digest
  deriving DecidableEq, Repr

def contextStream : StreamCodec Context :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product appStream
          (StreamCodec.product sessionStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product digestStream
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product intStream
                    (StreamCodec.product StreamCodec.nat
                      (StreamCodec.product intStream
                        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
                          (StreamCodec.product intStream
                            (StreamCodec.product intStream
                              (StreamCodec.product StreamCodec.nat
                                (StreamCodec.product StreamCodec.nat digestStream)))))))))))))))
    (fun context => (context.domain, context.semantics, context.app,
      context.session, context.ticketResource, context.ticketRoot,
      context.parentTask, context.parentGeneration, context.purseTask,
      context.purseGeneration, context.payerSubject, context.reserveAmount,
      context.maximumCharge, context.reserveOperationId,
      context.httpOperationId, context.requestDigest))
    (fun (domain, semantics, app, session, ticketResource, ticketRoot,
          parentTask, parentGeneration, purseTask, purseGeneration,
          payerSubject, reserveAmount, maximumCharge, reserveOperationId,
          httpOperationId, requestDigest) =>
      ⟨domain, semantics, app, session, ticketResource, ticketRoot, parentTask,
        parentGeneration, purseTask, purseGeneration, payerSubject,
        reserveAmount, maximumCharge, reserveOperationId, httpOperationId,
        requestDigest⟩)
    (by intro context; cases context; rfl)

def codec : LawfulCodec Context :=
  Minidregg.Compiler.NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-CONTEXT/v2".toUTF8.toList
    contextStream

def Context.canonicalBytes (context : Context) : List UInt8 :=
  codec.encode context

theorem decode_encode (context : Context) :
    codec.decode context.canonicalBytes = some context :=
  codec.decode_encode context

/-- This is the ordinary AgentGrain command nonce. It is only a signature
message component; the original signed reserve and full recorded intent must
still be re-admitted at their verified prefix. -/
def nonce (context : Context) : Nat :=
  AgentGrain.contextNonce context.canonicalBytes

/-- Exact request/scope join before any paid v2 dispatch can be formed.
`issuedTicketResource` must come from the historically admitted share issue,
not from the caller's context. Payer authority remains a separate native
check. -/
def matchesIngress (context : Context)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issuedTicketResource : Nat) : Bool :=
  decide (context.domain = ingress.dispatch.domain ∧
    context.semantics = ingress.dispatch.semantics ∧
    context.app = ingress.dispatch.dispatch.app ∧
    context.session = ingress.dispatch.dispatch.session ∧
    context.ticketResource = issuedTicketResource ∧
    context.ticketRoot = ingress.ticketRoot ∧
    context.httpOperationId = ingress.dispatch.dispatch.request.operationId ∧
    context.requestDigest = ApplicationDispatchCodec.requestDigest
      ingress.dispatch.dispatch.request ∧
    ingress.parent.map (fun parent => (parent.task, parent.state.generation)) =
      some (context.parentTask, context.parentGeneration) ∧
    context.session.origin = .agent context.parentTask context.parentGeneration)

/-- The reserve signature binds the exact canonical HTTP request in the
event21 wrapper through its source-owned digest and explicit operation ID.
The digest equality uses the deployed cSHAKE collision boundary; the body is
present only once, in the base dispatch ingress. -/
theorem matches_request (context : Context)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (issuedTicketResource : Nat)
    (matched : matchesIngress context ingress issuedTicketResource = true) :
    context.httpOperationId = ingress.dispatch.dispatch.request.operationId ∧
    context.requestDigest = ApplicationDispatchCodec.requestDigest
      ingress.dispatch.dispatch.request := by
  simp only [matchesIngress, decide_eq_true_eq] at matched
  rcases matched with ⟨_, _, _, _, _, _, operationId, digest, _, _⟩
  exact ⟨operationId, digest⟩

end Minidregg.Kernel.ApplicationDispatchAgentReserveContext
