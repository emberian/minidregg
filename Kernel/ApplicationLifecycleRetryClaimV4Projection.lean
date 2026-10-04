/-
Source-owned physical handoff after an exact versioned repeat-CREATE claim. The complete
signed package action descriptor and grain launch binding are retained through
the full original v4 BEGIN/recovery witness and claim. A native claim receipt identifies a durable
reservation; this projection alone does not attest a process or allow a retry.
-/
import Kernel.ApplicationLifecycleClaimProjection
import Kernel.ApplicationLifecycleRetryClaimV4Core

namespace Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Projection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Committed where
  core : ApplicationLifecycleClaimProjection.Committed
  originalClaim : ApplicationLifecycleRetryClaimV4Ingress.Ingress
  deriving DecidableEq

def committedStream : StreamCodec Committed :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleClaimProjection.committedStream
      ApplicationLifecycleRetryClaimV4Ingress.ingressStream)
    (fun committed => (committed.core, committed.originalClaim))
    (fun (core, originalClaim) => ⟨core, originalClaim⟩)
    (by intro committed; cases committed; rfl)

def frame : List UInt8 :=
  "DREGG/APPLICATION/RETRY-CREATE-CLAIM-COMMITTED/v4".toUTF8.toList

def codec : LawfulCodec Committed := NativeHostCodec.framed frame committedStream

def Committed.canonicalBytes (committed : Committed) : List UInt8 :=
  codec.encode committed

def Committed.valid (committed : Committed) : Bool :=
  let claim := committed.originalClaim
  let begin := claim.originalBegin
  claim.originalExact &&
    decide (committed.core.source = claim.base.source) &&
    decide (committed.core.originalTransaction = begin.base.transactionId) &&
    decide (committed.core.originalEvent =
      (ApplicationLifecycleRetryBeginV4Admission.event begin).eventId) &&
    decide (committed.core.claimReceipt.transactionId = claim.base.transactionId) &&
    decide (committed.core.claimReceipt.eventId =
      (ApplicationLifecycleRetryClaimV4Core.event claim).eventId)

def Committed.volume (committed : Committed) : Digest :=
  committed.originalClaim.originalBegin.volume

def Committed.selectedCommandDigest (committed : Committed) : Option Digest :=
  committed.originalClaim.originalBegin.start.map (·.commandDigest)

theorem decode_encode (committed : Committed) :
    codec.decode committed.canonicalBytes = some committed :=
  codec.decode_encode committed

theorem decoded_canonical {bytes : List UInt8} {committed : Committed}
    (decoded : codec.decode bytes = some committed) :
    committed.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical frame committedStream decoded

theorem canonical_injective : Function.Injective Committed.canonicalBytes :=
  lawful_encode_injective codec

end Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Projection
