/-
Strict signed carrier for a checked lifecycle completion. Event family 18 is
separate from pending BEGIN family 12 and one-shot claim family 16. A replay
of the same physical report cannot mint another completion nullifier.
-/
import Kernel.ApplicationLifecycleCompletionSource

namespace Minidregg.Kernel.ApplicationLifecycleCompletionIngress

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Ingress where
  domain : Digest
  semantics : Digest
  source : ApplicationLifecycleCompletionSource.Source
  signed : DeclaredResourceController.SignedCommand
  /-- A separate package observation is required when start/stop do not
  mutate the package as a joint DRC target. -/
  packageObservationEnvelope : List UInt8
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product ApplicationLifecycleCompletionSource.sourceStream
          (StreamCodec.product NativeHostCodec.signedInvocationStream bytesStream))))
    (fun ingress => (ingress.domain, ingress.semantics, ingress.source,
      ingress.signed, ingress.packageObservationEnvelope))
    (fun (domain, semantics, source, signed, packageObservationEnvelope) =>
      ⟨domain, semantics, source, signed, packageObservationEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v1".toUTF8.toList

def codec : LawfulCodec Ingress := NativeHostCodec.framed frame ingressStream

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 := codec.encode ingress

theorem decoded_canonical {bytes : List UInt8} {ingress : Ingress}
    (decoded : codec.decode bytes = some ingress) :
    ingress.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame ingressStream decoded

def event (ingress : Ingress) : StableEvent where
  codecVersion := 18
  domain := ingress.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-EVENT/v1".toUTF8.toList
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
  codecVersion := 18
  domain := ingress.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-NULLIFIER/v1".toUTF8.toList
    (nullifierKey ingress)).digest
  canonicalBytes :=
    "DREGG/APPLICATION/LIFECYCLE-COMPLETION-NULLIFIER-BYTES/v1".toUTF8.toList ++
      nullifierKey ingress

theorem stableNullifier_same_claim_nonce (left right : Ingress)
    (domain : left.domain = right.domain)
    (semantics : left.semantics = right.semantics)
    (claim : left.source.physical.report.claim.core.claimReceipt.transactionId =
      right.source.physical.report.claim.core.claimReceipt.transactionId)
    (nonce : left.source.physical.report.nonce = right.source.physical.report.nonce) :
    stableNullifier left = stableNullifier right := by
  simp [stableNullifier, nullifierKey, domain, semantics, claim, nonce]

end Minidregg.Kernel.ApplicationLifecycleCompletionIngress
