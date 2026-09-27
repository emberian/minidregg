/-
Canonical host handoff for a committed one-shot lifecycle reservation. This
codec describes Mini's checked identity and post-claim physical tip. It does
not by itself attest a systemd process, package SHA-256 conversion, or a
completed lifecycle operation; only the exact-CAS receiver may emit it.
-/
import Kernel.ApplicationLifecycleClaimIngress
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.ApplicationLifecycleClaimProjection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationLifecycleClaim

set_option autoImplicit false

structure Committed where
  source : Source
  originalTransaction : Digest
  originalEvent : Digest
  originalNullifier : Digest
  claimReceipt : NativeHostCodec.Receipt
  claimNullifier : Digest
  appPhysicalRoot : Digest
  packagePhysicalRoot : Digest
  authorityPhysicalRoot : Digest
  postImageBoundary : Digest
  deriving DecidableEq

def committedStream : StreamCodec Committed :=
  StreamCodec.xmap
    (StreamCodec.product sourceStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product NativeHostCodec.receiptStream
              (StreamCodec.product digestStream
                (StreamCodec.product digestStream
                  (StreamCodec.product digestStream
                    (StreamCodec.product digestStream digestStream)))))))))
    (fun value => (value.source, value.originalTransaction,
      value.originalEvent, value.originalNullifier, value.claimReceipt,
      value.claimNullifier, value.appPhysicalRoot, value.packagePhysicalRoot,
      value.authorityPhysicalRoot, value.postImageBoundary))
    (fun (source, originalTransaction, originalEvent, originalNullifier,
          claimReceipt, claimNullifier, appPhysicalRoot, packagePhysicalRoot,
          authorityPhysicalRoot, postImageBoundary) =>
      ⟨source, originalTransaction, originalEvent, originalNullifier,
        claimReceipt, claimNullifier, appPhysicalRoot, packagePhysicalRoot,
        authorityPhysicalRoot, postImageBoundary⟩)
    (by intro value; cases value; rfl)

private def frame : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v1".toUTF8.toList

def codec : LawfulCodec Committed := NativeHostCodec.framed frame committedStream

def Committed.canonicalBytes (value : Committed) : List UInt8 :=
  codec.encode value

theorem decode_encode (value : Committed) :
    codec.decode value.canonicalBytes = some value :=
  codec.decode_encode value

theorem decoded_canonical {bytes : List UInt8} {value : Committed}
    (decoded : codec.decode bytes = some value) :
    value.canonicalBytes = bytes :=
  strictCodec_canonical (NativeHostCodec.framedRaw frame committedStream) decoded

end Minidregg.Kernel.ApplicationLifecycleClaimProjection
