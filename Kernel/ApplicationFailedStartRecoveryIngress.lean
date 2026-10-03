/- Canonical event66 failed START reconciliation ingress. A stable original-claim nullifier prevents repeated reconciliation under distinct audit reports. Recovery creates no volume witness. -/
import Kernel.ApplicationFailedStartRecoverySource
import Kernel.ApplicationLifecycleCompletionIngress

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryIngress

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
  source : ApplicationFailedStartRecoverySource.Source
  signed : DeclaredResourceController.SignedCommand
  packageObservationEnvelope : List UInt8
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ApplicationFailedStartRecoverySource.sourceStream
          (StreamCodec.product NativeHostCodec.signedInvocationStream bytesStream))))
    (fun ingress => (ingress.domain, ingress.semantics, ingress.source,
      ingress.signed, ingress.packageObservationEnvelope))
    (fun (domain, semantics, source, signed, packageObservationEnvelope) =>
      ⟨domain, semantics, source, signed, packageObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

def event (ingress : Ingress) : StableEvent where
  codecVersion := 66
  domain := ingress.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/FAILED-START-RECOVERY-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def nullifierKey (ingress : Ingress) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product digestStream digestStream)).encode
    (ingress.domain, ingress.semantics,
      ingress.source.physical.report.claim.core.claimReceipt.transactionId)

def stableNullifier (ingress : Ingress) : StableNullifier where
  codecVersion := 66
  domain := ingress.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/FAILED-START-RECOVERY-NULLIFIER/v1".toUTF8.toList
    (nullifierKey ingress)).digest
  canonicalBytes :=
    "DREGG/APPLICATION/FAILED-START-RECOVERY-NULLIFIER-BYTES/v1".toUTF8.toList ++
      nullifierKey ingress

/-- Recovery neither establishes a successful launch nor creates a volume witness. -/
def Ingress.creationMarker (_ingress : Ingress) : Option StableNullifier := none

theorem recovery_has_no_creation_marker (ingress : Ingress) :
    ingress.creationMarker = none := rfl

theorem decode_encode (ingress : Ingress) :
    codec.decode ingress.canonicalBytes = some ingress := codec.decode_encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

theorem event_retains_full_ingress (ingress : Ingress) :
    (event ingress).canonicalBytes = ingress.canonicalBytes := rfl

theorem same_claim_same_recovery_nullifier (left right : Ingress)
    (domain : left.domain = right.domain) (semantics : left.semantics = right.semantics)
    (claim : left.source.physical.report.claim.core.claimReceipt.transactionId =
      right.source.physical.report.claim.core.claimReceipt.transactionId) :
    stableNullifier left = stableNullifier right := by
  simp only [stableNullifier, nullifierKey, domain, semantics, claim]

end Minidregg.Kernel.ApplicationFailedStartRecoveryIngress
