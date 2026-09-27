/-
Canonical special dispatch ingress. The base signed command binds the exact
app-visible request and app/session observation coordinates. This wrapper
also carries the independently signed ticket observation and the
historical share-issue ingress used to select an admitted issue event. None of
these bytes are authority until the receiving admission checks one image.
-/
import Kernel.ApplicationDispatchCommand

namespace Minidregg.Kernel.ApplicationDispatchAdmissionIngress

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.DeclaredEffectPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchIngress
open Minidregg.Kernel.ApplicationDispatchCommand

set_option autoImplicit false

structure Ingress where
  dispatch : ApplicationDispatchIngress.Ingress
  appSnapshotManifest : Nat
  appManagementSubject : SubjectId
  parent : Option Parent
  ticketRoot : Digest
  ticketObserveCapability : CapabilityId
  ticketObservationEnvelope : List UInt8
  issueIngressBytes : List UInt8

private def agentStateStream : StreamCodec AgentGrain.State :=
  StreamCodec.xmap
    (StreamCodec.product intStream
      (StreamCodec.product intStream
        (StreamCodec.product intStream intStream)))
    (fun state => (state.generation, state.status, state.remaining, state.reserved))
    (fun (generation, status, remaining, reserved) =>
      ⟨generation, status, remaining, reserved⟩)
    (by intro state; cases state; rfl)

private def parentStream : StreamCodec Parent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product agentStateStream
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product digestStream
            CredentialAuthorityEntryCodec.capabilityIdStream))))
    (fun parent => (parent.task, parent.state, parent.capability,
      parent.root, parent.observe))
    (fun (task, state, capability, root, observe) =>
      ⟨task, state, capability, root, observe⟩)
    (by intro parent; cases parent; rfl)

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchIngress.ingressStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product (StreamCodec.option parentStream)
            (StreamCodec.product digestStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product bytesStream bytesStream)))))))
    (fun ingress => (ingress.dispatch, ingress.appSnapshotManifest,
      ingress.appManagementSubject, ingress.parent, ingress.ticketRoot,
      ingress.ticketObserveCapability, ingress.ticketObservationEnvelope,
      ingress.issueIngressBytes))
    (fun (dispatch, appSnapshotManifest, appManagementSubject, parent,
          ticketRoot, ticketObserveCapability,
          ticketObservationEnvelope, issueIngressBytes) =>
      ⟨dispatch, appSnapshotManifest, appManagementSubject, parent,
        ticketRoot, ticketObserveCapability, ticketObservationEnvelope, issueIngressBytes⟩)
    (by intro ingress; cases ingress; rfl)

private def frame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-ADMISSION-INGRESS/v1".toUTF8.toList

private def rawCodec : LawfulCodec Ingress where
  encode ingress := frame ++ ingressStream.encode ingress
  decode bytes := if bytes.take frame.length = frame then
    ingressStream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def codec : LawfulCodec Ingress := ResourceBirthCodec.strictCodec rawCodec

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 :=
  codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec decoded

/-- The operation key is shared with the base dispatch carrier. A different
ticket or issue selector under that key is a transaction conflict, not a
second external delivery. -/
def nullifier (ingress : Ingress) : StableNullifier :=
  ApplicationDispatchIngress.nullifier ingress.dispatch

/-- The special pending event retains the complete admission ingress. The
ordinary DRC mutation event and the shorter base dispatch event do not carry
ticket observation or issue provenance selectors. Neither this event nor its
bytes alone prove admission. -/
def event (ingress : Ingress) : StableEvent where
  codecVersion := 11
  domain := ingress.dispatch.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/DISPATCH-ADMISSION-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationDispatchAdmissionIngress
