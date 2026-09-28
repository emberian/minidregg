/-
Source bytes for one joint session enrollment. The ordinary signed command
mutates only the participant's session and descriptor. A separate checked
app observation and physical read guard belong to the event28 receiver;
these request and ingress codecs do not themselves grant enrollment.
-/
import Kernel.ApplicationGrainSessionEnrollment
import Kernel.ApplicationDispatchAuthority
import Kernel.NativeHostContext

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationGrainSessionEnrollment

set_option autoImplicit false

/-- The ticket and participant are selected from verified event22 history.
The caller chooses only a role within that ticket's ceiling, a nonce, and
capability selectors whose current authority is checked by native admission. -/
structure Request where
  issueIndex : Nat
  ticketResource : Nat
  packageManifest : Nat
  role : RoleAssignment
  descriptorCapability : CapabilityId
  sessionObserveCapability : CapabilityId
  descriptorObserveCapability : CapabilityId
  manifestObserveCapability : CapabilityId
  nonce : Nat
  deriving DecidableEq, Repr

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product roleAssignmentStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                  (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                    StreamCodec.nat))))))))
    (fun request =>
      (request.issueIndex, request.ticketResource, request.packageManifest,
        request.role, request.descriptorCapability,
        request.sessionObserveCapability, request.descriptorObserveCapability,
        request.manifestObserveCapability, request.nonce))
    (fun (issueIndex, ticketResource, packageManifest, role,
          descriptorCapability, sessionObserveCapability,
          descriptorObserveCapability, manifestObserveCapability, nonce) =>
      ⟨issueIndex, ticketResource, packageManifest, role,
        descriptorCapability, sessionObserveCapability,
        descriptorObserveCapability, manifestObserveCapability, nonce⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SESSION-ENROLLMENT-REQUEST/v1".toUTF8.toList
    requestStream

theorem request_decode_encode (request : Request) :
    requestCodec.decode (requestCodec.encode request) = some request :=
  requestCodec.decode_encode request

/-- A distinct event ingress retains the complete ordinary signed joint
command and every independently signed read. The receiver must reselect the
original issue and check each envelope at the exact admitted image. -/
structure Ingress where
  request : Request
  enrollment : Enrollment
  issueReceipt : NativeHostCodec.Receipt
  appRoot : Digest
  manifestRoot : Digest
  ticketRoot : Digest
  signedBytes : List UInt8
  appObservationEnvelope : List UInt8
  manifestObservationEnvelope : List UInt8
  ticketObservationEnvelope : List UInt8
  deriving DecidableEq, Repr

private def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product enrollmentStream
        (StreamCodec.product NativeHostCodec.receiptStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product bytesStream
                  (StreamCodec.product bytesStream
                    (StreamCodec.product bytesStream bytesStream)))))))))
    (fun ingress =>
      (ingress.request, ingress.enrollment, ingress.issueReceipt,
        ingress.appRoot, ingress.manifestRoot, ingress.ticketRoot,
        ingress.signedBytes, ingress.appObservationEnvelope,
        ingress.manifestObservationEnvelope, ingress.ticketObservationEnvelope))
    (fun (request, enrollment, issueReceipt, appRoot,
          manifestRoot, ticketRoot, signedBytes, appObservationEnvelope,
          manifestObservationEnvelope, ticketObservationEnvelope) =>
      ⟨request, enrollment, issueReceipt, appRoot,
        manifestRoot, ticketRoot, signedBytes, appObservationEnvelope,
        manifestObservationEnvelope, ticketObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SESSION-ENROLLMENT-INGRESS/v1".toUTF8.toList
    ingressStream

theorem ingress_decode_encode (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress :=
  ingressCodec.decode_encode ingress

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 :=
  ingressCodec.encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : ingressCodec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical
    "DREGG/APPLICATION/SESSION-ENROLLMENT-INGRESS/v1".toUTF8.toList
    ingressStream decoded

def event (domain : Digest) (ingress : Ingress) : StableEvent where
  codecVersion := 28
  domain := domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SESSION-ENROLLMENT-EVENT/v1".toUTF8.toList
    (digestStream.encode domain ++ ingress.canonicalBytes)).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (domain : Digest) (ingress : Ingress) :
    (event domain ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource
