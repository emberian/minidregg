/-
Strict completion ingress for the launch-bound lifecycle. Event25 is distinct
from historical event18. A successful physical running report for the
first-create action adds the stable created-volume marker in the same atomic
intent as the app phase change. Its presence alone is never a launch permit:
later continue admission also selects the exact native-admitted creation
completion from verified history.
-/
import Kernel.ApplicationLifecycleCompletionV2Source
import Kernel.ApplicationLifecycleCompletionIngress

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Ingress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  domain : Digest
  semantics : Digest
  source : ApplicationLifecycleCompletionV2Source.Source
  signed : DeclaredResourceController.SignedCommand
  packageObservationEnvelope : List UInt8
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ApplicationLifecycleCompletionV2Source.sourceStream
          (StreamCodec.product NativeHostCodec.signedInvocationStream bytesStream))))
    (fun ingress => (ingress.domain, ingress.semantics, ingress.source,
      ingress.signed, ingress.packageObservationEnvelope))
    (fun (domain, semantics, source, signed, packageObservationEnvelope) =>
      ⟨domain, semantics, source, signed, packageObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v2".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

def event (ingress : Ingress) : StableEvent where
  codecVersion := 25
  domain := ingress.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-EVENT/v2".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def nullifierKey (ingress : Ingress) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream StreamCodec.nat))).encode
    (ingress.domain, ingress.semantics,
      ingress.source.physical.report.claim.core.claimReceipt.transactionId,
      ingress.source.physical.report.nonce)

def stableNullifier (ingress : Ingress) : StableNullifier where
  codecVersion := 25
  domain := ingress.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-NULLIFIER/v2".toUTF8.toList
    (nullifierKey ingress)).digest
  canonicalBytes :=
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-NULLIFIER-BYTES/v2".toUTF8.toList ++
      nullifierKey ingress

def Ingress.creationMarker (ingress : Ingress) : Option StableNullifier :=
  if ingress.source.kind == .start &&
      ingress.source.physical.report.outcome == .running then
    match ingress.source.originalBegin.start with
    | some binding => match binding.choice with
        | .create _ => some
            (ApplicationLifecycleClaimV3Ingress.createdNullifier ingress.domain binding)
        | .continue => none
    | none => none
  else none

theorem nonstart_has_no_creation_marker (ingress : Ingress)
    (kind : ingress.source.kind ≠ .start) : ingress.creationMarker = none := by
  simp [Ingress.creationMarker, kind]

theorem continue_has_no_creation_marker (ingress : Ingress)
    (start : ingress.source.kind = .start)
    (binding : ApplicationLifecycleLaunchBinding.Binding)
    (selected : ingress.source.originalBegin.start = some binding)
    (choice : binding.choice = .continue) : ingress.creationMarker = none := by
  simp [Ingress.creationMarker, start, selected, choice]

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Ingress
