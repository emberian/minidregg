/-
Canonical event21 carrier for a paid agent-origin application request. It
retains the complete app dispatch, original reserve selector/context, and
separately signed current payer witness. Decoding this carrier grants nothing:
Replay and the live receiver must independently verify all native signatures,
accepted history, current law, physical purse guard and durable CAS.
-/
import Kernel.ApplicationDispatchAgentReserveCore

namespace Minidregg.Kernel.ApplicationDispatchAgentIngress

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchAgentReserveContext

set_option autoImplicit false

structure Ingress where
  dispatch : ApplicationDispatchAdmissionIngress.Ingress
  reserveContext : Context
  reserveIndex : Nat
  payerCapability : CapabilityId
  payerObserve : CapabilityId
  payerSigned : DeclaredResourceController.SignedCommand

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAdmissionIngress.ingressStream
      (StreamCodec.product ApplicationDispatchAgentReserveContext.contextStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              NativeHostCodec.signedInvocationStream)))))
    (fun ingress => (ingress.dispatch, ingress.reserveContext,
      ingress.reserveIndex, ingress.payerCapability, ingress.payerObserve,
      ingress.payerSigned))
    (fun (dispatch, reserveContext, reserveIndex, payerCapability,
          payerObserve, payerSigned) =>
      ⟨dispatch, reserveContext, reserveIndex, payerCapability,
        payerObserve, payerSigned⟩)
    (by intro ingress; cases ingress; rfl)

def codec : LawfulCodec Ingress :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-ADMISSION-INGRESS/v2".toUTF8.toList
    ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 :=
  codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress :=
  codec.decode_encode ingress

def event (ingress : Ingress) : StableEvent where
  codecVersion := 21
  domain := ingress.dispatch.dispatch.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-DISPATCH-ADMISSION-EVENT/v2".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationDispatchAgentIngress
