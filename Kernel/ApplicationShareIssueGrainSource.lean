/-
An additive grain-backed share-ticket carrier. The inner birth is the existing
joint factory/Book/tool/parent command, not a bare resource birth. The outer
frame retains the app's independent delegation envelope and complete ticket
spec for one special durable issue event.
-/
import Kernel.ApplicationShareIssueSource
import Kernel.GrainResourceBirthPolicyController

namespace Minidregg.Kernel.ApplicationShareIssueGrainSource

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.ApplicationShareIssueSource

set_option autoImplicit false

structure Ingress where
  spec : Spec
  grainIngress : List UInt8
  appEnvelope : List UInt8
  deriving DecidableEq, Repr

private def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.spec, ingress.grainIngress, ingress.appEnvelope))
    (fun (spec, grainIngress, appEnvelope) =>
      ⟨spec, grainIngress, appEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/GRAIN-SHARE-ISSUE-INGRESS/v1".toUTF8.toList

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

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec decoded

theorem bytes_injective : Function.Injective codec.encode := by
  intro left right same
  have decoded := congrArg codec.decode same
  exact Option.some.inj (by simpa only [codec.decode_encode] using decoded)

def Ingress.decodeGrain (ingress : Ingress) :
    Option GrainResourceBirthPolicyController.DecodedIngress :=
  GrainResourceBirthPolicyController.decodeIngress ingress.grainIngress

theorem decoded_grain_bytes {ingress : Ingress}
    {grain : GrainResourceBirthPolicyController.DecodedIngress}
    (decoded : ingress.decodeGrain = some grain) :
    grain.bytes = ingress.grainIngress :=
  GrainResourceBirthPolicyController.decodeIngress_canonical decoded

end Minidregg.Kernel.ApplicationShareIssueGrainSource
