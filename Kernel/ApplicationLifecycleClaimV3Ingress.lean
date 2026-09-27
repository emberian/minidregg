/-
One-shot claim of an exact launch-bound v3 BEGIN. The original START choice,
command digest, volume lineage and signed package command list are repeated
inside this canonical event; a v1/v2 BEGIN cannot be substituted. A first
create claim additionally consumes a stable first-attempt marker in its
checked native intent, so an uncertain execution cannot silently rearm it.
-/
import Kernel.ApplicationLifecycleClaimIngress
import Kernel.ApplicationLifecycleBeginV3Ingress

namespace Minidregg.Kernel.ApplicationLifecycleClaimV3Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  base : ApplicationLifecycleClaimIngress.Ingress
  originalBegin : ApplicationLifecycleBeginV3Ingress.Ingress
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimIngress.ingressStream
      ApplicationLifecycleBeginV3Ingress.ingressStream)
    (fun ingress => (ingress.base, ingress.originalBegin))
    (fun (base, originalBegin) => ⟨base, originalBegin⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v3".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

def Ingress.originalExact (ingress : Ingress) : Bool :=
  decide (ingress.base.source.begin = ingress.originalBegin.base) &&
    ingress.originalBegin.shape

def event (ingress : Ingress) : StableEvent where
  codecVersion := 24
  domain := ingress.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-CLAIM-EVENT/v3".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def firstAttemptNullifier (domain : Digest)
    (binding : ApplicationLifecycleLaunchBinding.Binding) : StableNullifier where
  codecVersion := 24
  domain := domain
  nullifierId := ApplicationLifecycleLaunchBinding.firstAttemptKey domain binding
  canonicalBytes :=
    "DREGG/APPLICATION/FIRST-START-ATTEMPT-BYTES/v1".toUTF8.toList ++
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat digestStream)).encode
        (domain, binding.app, binding.volume)

/-- Installed only by an admitted successful first-create completion. Claim
preparation checks its current presence for continue and absence for create;
Verified history additionally supplies the original completed-create proof. -/
def createdNullifier (domain : Digest)
    (binding : ApplicationLifecycleLaunchBinding.Binding) : StableNullifier where
  codecVersion := 25
  domain := domain
  nullifierId := ApplicationLifecycleLaunchBinding.createdKey domain binding
  canonicalBytes :=
    "DREGG/APPLICATION/VOLUME-CREATED-BYTES/v1".toUTF8.toList ++
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat digestStream)).encode
        (domain, binding.app, binding.volume)

def Ingress.createAttempt (ingress : Ingress) : Option StableNullifier :=
  match ingress.originalBegin.start with
  | some binding => match binding.choice with
      | .create _ => some (firstAttemptNullifier ingress.base.domain binding)
      | .continue => none
  | none => none

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationLifecycleClaimV3Ingress
