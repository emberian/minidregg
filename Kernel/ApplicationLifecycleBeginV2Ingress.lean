/-
Versioned lifecycle BEGIN carrier for a full signed-SPK descriptor preimage.
The v1 BEGIN codec and event bytes remain unchanged for historical replay.
This v2 carrier still records pending physical work, never its completion.
-/
import Kernel.ApplicationLifecycleBeginIngress
import Kernel.ApplicationSpkPackageIdentity

namespace Minidregg.Kernel.ApplicationLifecycleBeginV2Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  base : ApplicationLifecycleBeginIngress.Ingress
  descriptor : ApplicationSpkPackageIdentity.Descriptor
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBeginIngress.ingressStream
      ApplicationSpkPackageIdentity.descriptorStream)
    (fun ingress => (ingress.base, ingress.descriptor))
    (fun (base, descriptor) => ⟨base, descriptor⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v2".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

def event (ingress : Ingress) : StableEvent where
  codecVersion := 12
  domain := ingress.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-BEGIN-EVENT/v2".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

/-- Install and upgrade name the package version that checked completion must
install; start/stop name the currently installed version. -/
def prospectiveVersion (source : ApplicationLifecycleBegin.Source) : Int :=
  match source.kind with
  | .install | .upgrade => source.before.packageVersion + 1
  | .start | .stop => source.before.packageVersion

def prospectiveManifest (ingress : Ingress) : ApplicationDispatchManifest.Manifest :=
  { app := ingress.base.source.app
    packageVersion := prospectiveVersion ingress.base.source
    packageRoot := ingress.descriptor.root
    interfaces := ingress.descriptor.interfaces }

/-- Full descriptor validity, app/version/schema identity, and the source's
signed package commitment are checked together. For install/upgrade this is
the prospective manifest, not an assertion that it is already installed. -/
def descriptorBound (ingress : Ingress) : Bool :=
  ingress.descriptor.matchesManifest (prospectiveManifest ingress) &&
  decide (ingress.base.source.packageDigest = ingress.descriptor.root)

end Minidregg.Kernel.ApplicationLifecycleBeginV2Ingress
