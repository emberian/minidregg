/-
The exact signed carrier for a Mini-owned application lifecycle BEGIN. Its
event records the pending physical request; a DRC invocation with the same
state write but the ordinary event is not a lifecycle pending record.
-/
import Kernel.ApplicationLifecycleBegin
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.ApplicationLifecycleBeginIngress

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationLifecycleBegin

set_option autoImplicit false

structure Ingress where
  domain : Digest
  semantics : Digest
  source : Source
  signed : DeclaredResourceController.SignedCommand
  packageObservationEnvelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product sourceStream
          (StreamCodec.product NativeHostCodec.signedInvocationStream bytesStream))))
    (fun ingress => (ingress.domain, ingress.semantics, ingress.source,
      ingress.signed, ingress.packageObservationEnvelope))
    (fun (domain, semantics, source, signed, packageObservationEnvelope) =>
      ⟨domain, semantics, source, signed, packageObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v1".toUTF8.toList

private def rawCodec : LawfulCodec Ingress where
  encode ingress := frame ++ ingressStream.encode ingress
  decode bytes := if bytes.take frame.length = frame then
    ingressStream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def codec : LawfulCodec Ingress := strictCodec rawCodec

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes := strictCodec_canonical rawCodec decoded

def event (ingress : Ingress) : StableEvent where
  codecVersion := 12
  domain := ingress.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

def Ingress.transactionId (ingress : Ingress) : Digest :=
  ⟨DeclaredResourceController.operationMarker ingress.domain ingress.semantics
    (command ingress.domain ingress.semantics ingress.source)⟩

end Minidregg.Kernel.ApplicationLifecycleBeginIngress
