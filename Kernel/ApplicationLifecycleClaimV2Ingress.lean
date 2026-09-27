/-
Versioned one-shot claim of a descriptor-bound lifecycle BEGIN. The complete
v2 BEGIN carrier is repeated so the current signed claim cannot substitute a
bare v1 historical BEGIN at the same resource and generation. Its canonical
event remains in the allocated lifecycle claim family (16).
-/
import Kernel.ApplicationLifecycleClaimIngress
import Kernel.ApplicationLifecycleBeginV2Ingress

namespace Minidregg.Kernel.ApplicationLifecycleClaimV2Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  base : ApplicationLifecycleClaimIngress.Ingress
  originalBegin : ApplicationLifecycleBeginV2Ingress.Ingress
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimIngress.ingressStream
      ApplicationLifecycleBeginV2Ingress.ingressStream)
    (fun ingress => (ingress.base, ingress.originalBegin))
    (fun (base, originalBegin) => ⟨base, originalBegin⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v2".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

/-- The source-derived original v1 projection must be exactly the base of the
descriptor-bearing BEGIN. The BEGIN descriptor root is already bound to its
signed `packageDigest` by v2 BEGIN admission. -/
def Ingress.originalExact (ingress : Ingress) : Bool :=
  decide (ingress.base.source.begin = ingress.originalBegin.base)

def event (ingress : Ingress) : StableEvent where
  codecVersion := 16
  domain := ingress.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-CLAIM-EVENT/v2".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationLifecycleClaimV2Ingress
