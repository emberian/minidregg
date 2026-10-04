/- Versioned retry CLAIM carries the full versioned BEGIN and recovery proof
selector. A receiver may consume its retry token once; no created marker is
emitted and no old first-attempt marker is cleared. -/
import Kernel.ApplicationLifecycleRetryBeginV4Ingress

namespace Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Ingress where
  base : ApplicationLifecycleClaimIngress.Ingress
  originalBegin : ApplicationLifecycleRetryBeginV4Ingress.Ingress
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimIngress.ingressStream
      ApplicationLifecycleRetryBeginV4Ingress.ingressStream)
    (fun ingress => (ingress.base, ingress.originalBegin))
    (fun (base, begin) => ⟨base, begin⟩)
    (by intro ingress; cases ingress; rfl)

def codec : LawfulCodec Ingress := NativeHostCodec.framed
  "DREGG/APPLICATION/RETRY-CREATE-CLAIM-INGRESS/v4".toUTF8.toList ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

def Ingress.originalExact (ingress : Ingress) : Bool :=
  decide (ingress.base.source.begin = ingress.originalBegin.begin.base) &&
    ingress.originalBegin.shape

def Ingress.retryToken (ingress : Ingress) :
    Minidregg.Kernel.DurableDataIntent.StableNullifier :=
  ApplicationFailedCreateRetryEvidence.retryToken ingress.originalBegin.retry

theorem originalExact_source {ingress : Ingress}
    (exact : ingress.originalExact = true) :
    ingress.base.source.begin = ingress.originalBegin.begin.base := by
  simp only [Ingress.originalExact, Bool.and_eq_true, decide_eq_true_eq] at exact
  exact exact.1

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) : ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical
    "DREGG/APPLICATION/RETRY-CREATE-CLAIM-INGRESS/v4".toUTF8.toList ingressStream decoded

end Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Ingress
