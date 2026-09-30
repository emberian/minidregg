/-
A separate, canonical native ingress for an application dispatch candidate.
The signed DRC command is retained in full. App, package manifest and session
enrollment are separately observed at current roots; the signed command has
only a session witness and optional agent-parent witness. The accepted special
event/nullifier is the durable pending request, not a generic content atom.
Merely decoding this carrier is not authority to hand HTTP to a process.
-/
import Kernel.ApplicationDispatchCodec
import Compiler.NativeHostCodec
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.ApplicationDispatchIngress

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

structure Ingress where
  domain : Digest
  semantics : Digest
  dispatch : Dispatch
  signed : DeclaredResourceController.SignedCommand
  appRoot : Digest
  appObserveCapability : CapabilityId
  appObservationEnvelope : List UInt8
  manifestObserveCapability : CapabilityId
  manifestObservationEnvelope : List UInt8
  enrollmentResource : Nat
  enrollmentRoot : Digest
  enrollmentObserveCapability : CapabilityId
  enrollmentObservationEnvelope : List UInt8

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product dispatchStream
          (StreamCodec.product NativeHostCodec.signedInvocationStream
            (StreamCodec.product digestStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product bytesStream
                  (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                    (StreamCodec.product bytesStream
                      (StreamCodec.product StreamCodec.nat
                        (StreamCodec.product digestStream
                          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                            bytesStream))))))))))))
    (fun ingress => (ingress.domain, ingress.semantics, ingress.dispatch,
      ingress.signed, ingress.appRoot, ingress.appObserveCapability,
      ingress.appObservationEnvelope, ingress.manifestObserveCapability,
      ingress.manifestObservationEnvelope, ingress.enrollmentResource,
      ingress.enrollmentRoot, ingress.enrollmentObserveCapability,
      ingress.enrollmentObservationEnvelope))
    (fun (domain, semantics, dispatch, signed, appRoot, appCapability,
          appEnvelope, manifestCapability, manifestEnvelope, enrollmentResource,
          enrollmentRoot, enrollmentCapability, enrollmentEnvelope) =>
      ⟨domain, semantics, dispatch, signed, appRoot, appCapability, appEnvelope,
        manifestCapability, manifestEnvelope, enrollmentResource, enrollmentRoot,
        enrollmentCapability, enrollmentEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

private def frame : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-INGRESS/v2".toUTF8.toList

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

/-- The one-use key is an app/session/operation coordinate. Changing request
bytes under this key must be a durable transaction conflict, not a new permit.
Uniqueness of its digest relies on the deployed cSHAKE collision boundary. -/
abbrev Key := Digest × Digest × Nat × Int × Nat × Int × Nat

def keyStream : StreamCodec Key :=
  StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product IntStream.intStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product IntStream.intStream StreamCodec.nat)))))

def key (ingress : Ingress) : Key :=
    (ingress.domain, ingress.semantics, ingress.dispatch.app.resource,
      ingress.dispatch.app.generation, ingress.dispatch.session.resource,
      ingress.dispatch.session.generation,
      ingress.dispatch.request.operationId)

def keyBytes (ingress : Ingress) : List UInt8 :=
  keyStream.encode (key ingress)

theorem keyBytes_eq_iff_key (left right : Ingress) :
    keyBytes left = keyBytes right ↔ key left = key right :=
  (lawful_encode_injective keyStream.toLawful).eq_iff

def keyDigest (ingress : Ingress) : Digest :=
  (Sp800185Cshake256.hash "DREGG/APPLICATION/DISPATCH-KEY/v1".toUTF8.toList
    (keyBytes ingress)).digest

/-- The DRC command signature binds the complete app-visible request and the
selected observation coordinates, never their signature envelopes (which
would be circular). The nullifier separately reserves the stable operation
key. Fresh admission must derive these coordinates from the current image and
native-check each observation envelope against its source-owned request. -/
def requestDigest (ingress : Ingress) : Digest :=
  (Sp800185Cshake256.hash "DREGG/APPLICATION/DISPATCH-REQUEST-BIND/v2".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product bytesStream
          (StreamCodec.product digestStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product digestStream
                    CredentialAuthorityEntryCodec.capabilityIdStream)))))))).encode
      (ingress.domain, ingress.semantics, ingress.dispatch.canonicalBytes,
        ingress.appRoot, ingress.appObserveCapability,
        ingress.manifestObserveCapability, ingress.enrollmentResource,
        ingress.enrollmentRoot, ingress.enrollmentObserveCapability))).digest

def nullifier (ingress : Ingress) : StableNullifier where
  codecVersion := 11
  domain := ingress.domain
  nullifierId := keyDigest ingress
  canonicalBytes := "DREGG/APPLICATION/DISPATCH-NULLIFIER/v1".toUTF8.toList ++
    keyBytes ingress

def event (ingress : Ingress) : StableEvent where
  codecVersion := 11
  domain := ingress.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/DISPATCH-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_ingress_exact (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationDispatchIngress
