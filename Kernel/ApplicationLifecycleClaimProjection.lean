/-
Canonical host handoff for a committed one-shot lifecycle reservation. This
codec describes Mini's checked identity and post-claim physical tip. It does
not by itself attest a systemd process, package SHA-256 conversion, or a
completed lifecycle operation; only the exact-CAS receiver may emit it.
-/
import Kernel.ApplicationLifecycleClaimIngress
import Kernel.ApplicationSpkPackageIdentity
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
  postWorldRoot : Digest
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
      value.authorityPhysicalRoot, value.postWorldRoot))
    (fun (source, originalTransaction, originalEvent, originalNullifier,
          claimReceipt, claimNullifier, appPhysicalRoot, packagePhysicalRoot,
          authorityPhysicalRoot, postWorldRoot) =>
      ⟨source, originalTransaction, originalEvent, originalNullifier,
        claimReceipt, claimNullifier, appPhysicalRoot, packagePhysicalRoot,
        authorityPhysicalRoot, postWorldRoot⟩)
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

/-- V2 host handoff includes the full signed-SPK descriptor preimage. The v1
projection is retained only for historical source compatibility and cannot
qualify a physical SPK launch. -/
structure CommittedV2 where
  core : Committed
  descriptor : ApplicationSpkPackageIdentity.Descriptor
  deriving DecidableEq

def committedV2Stream : StreamCodec CommittedV2 :=
  StreamCodec.xmap
    (StreamCodec.product committedStream
      ApplicationSpkPackageIdentity.descriptorStream)
    (fun value => (value.core, value.descriptor))
    (fun (core, descriptor) => ⟨core, descriptor⟩)
    (by intro value; cases value; rfl)

private def frameV2 : List UInt8 :=
  "DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v2".toUTF8.toList

def codecV2 : LawfulCodec CommittedV2 :=
  NativeHostCodec.framed frameV2 committedV2Stream

def CommittedV2.canonicalBytes (value : CommittedV2) : List UInt8 :=
  codecV2.encode value

def CommittedV2.valid (value : CommittedV2) : Bool :=
  value.descriptor.valid &&
    decide (value.core.source.begin.source.packageDigest = value.descriptor.root)

theorem decode_encode_v2 (value : CommittedV2) :
    codecV2.decode value.canonicalBytes = some value := codecV2.decode_encode value

theorem decoded_canonical_v2 {bytes : List UInt8} {value : CommittedV2}
    (decoded : codecV2.decode bytes = some value) :
    value.canonicalBytes = bytes :=
  strictCodec_canonical
    (NativeHostCodec.framedRaw frameV2 committedV2Stream) decoded

end Minidregg.Kernel.ApplicationLifecycleClaimProjection
