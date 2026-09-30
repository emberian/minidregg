/-
General canonicality of the selected SPK package and launch profiles. The
receiving modules retain their historical codec and root bytes. This proof
module is outside the native host import closure.

Lean 4.30 does not kernel-reduce String.toUTF8, so each finite comparison of
the two literal frame strings is named as a compiled fact. The general codec
arguments below use those facts and kernel-checked reasoning. `#print axioms`
makes the compiler trust visible; there are no silent `#guard` checks.
-/
import Kernel.ApplicationSpkPackageIdentity
import Kernel.ApplicationSpkLaunchDescriptor

namespace Minidregg.Kernel.ApplicationSpkProfileProofs

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

private theorem framed_distinct_decode_none {α : Type} (stream : StreamCodec α)
    (first second : List UInt8) (sameLength : first.length = second.length)
    (different : first ≠ second) (value : α) :
    (NativeHostCodec.framed first stream).decode
      ((NativeHostCodec.framed second stream).encode value) = none := by
  cases decoded : (NativeHostCodec.framed first stream).decode
      ((NativeHostCodec.framed second stream).encode value) with
  | none => rfl
  | some other =>
      have exact := NativeHostCodec.framed_canonical first stream decoded
      change first ++ stream.encode other = second ++ stream.encode value at exact
      have prefixes := congrArg (fun bytes : List UInt8 => bytes.take first.length) exact
      have equal : first = second := by simpa [sameLength] using prefixes
      exact False.elim (different equal)

private def packageV1 : List UInt8 :=
  "DREGG/APPLICATION/SPK-PACKAGE-IDENTITY/v1".toUTF8.toList

private def packageV2 : List UInt8 :=
  "DREGG/APPLICATION/SPK-PACKAGE-IDENTITY/v2".toUTF8.toList

theorem package_frame_lengths_equal_compiled : packageV1.length = packageV2.length := by
  native_decide
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.package_frame_lengths_equal_compiled' depends on axioms: [propext, package_frame_lengths_equal_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms package_frame_lengths_equal_compiled

theorem package_frames_distinct_compiled : packageV1 ≠ packageV2 := by
  native_decide
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.package_frames_distinct_compiled' depends on axioms: [propext, package_frames_distinct_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms package_frames_distinct_compiled

private theorem package_v1_rejects_v2
    (descriptor : ApplicationSpkPackageIdentity.Descriptor) :
    ApplicationSpkPackageIdentity.codec.decode
      (ApplicationSpkPackageIdentity.codecV2.encode descriptor) = none := by
  exact framed_distinct_decode_none
    ApplicationSpkPackageIdentity.descriptorStream packageV1 packageV2
    package_frame_lengths_equal_compiled package_frames_distinct_compiled descriptor

theorem package_decode_encode_selected
    (descriptor : ApplicationSpkPackageIdentity.Descriptor) :
    ApplicationSpkPackageIdentity.decodeCanonical descriptor.canonicalBytes =
      some descriptor := by
  cases profile : descriptor.legacyProfile with
  | false =>
      simp [ApplicationSpkPackageIdentity.Descriptor.canonicalBytes,
        ApplicationSpkPackageIdentity.decodeCanonical, profile,
        package_v1_rejects_v2, ApplicationSpkPackageIdentity.codecV2.decode_encode]
  | true =>
      simp [ApplicationSpkPackageIdentity.Descriptor.canonicalBytes,
        ApplicationSpkPackageIdentity.decodeCanonical, profile,
        ApplicationSpkPackageIdentity.codec.decode_encode]

theorem package_decoded_canonical {bytes : List UInt8}
    {descriptor : ApplicationSpkPackageIdentity.Descriptor}
    (decoded : ApplicationSpkPackageIdentity.decodeCanonical bytes = some descriptor) :
    descriptor.canonicalBytes = bytes := by
  unfold ApplicationSpkPackageIdentity.decodeCanonical at decoded
  cases old : ApplicationSpkPackageIdentity.codec.decode bytes with
  | some candidate =>
      cases profile : candidate.legacyProfile with
      | false => simp [old, profile] at decoded
      | true =>
          simp [old, profile] at decoded
          have same : candidate = descriptor := decoded
          subst descriptor
          simpa [ApplicationSpkPackageIdentity.Descriptor.canonicalBytes, profile] using
            ApplicationSpkPackageIdentity.decoded_canonical old
  | none =>
      cases new : ApplicationSpkPackageIdentity.codecV2.decode bytes with
      | none => simp [old, new] at decoded
      | some candidate =>
          cases profile : candidate.legacyProfile with
          | true => simp [old, new, profile] at decoded
          | false =>
              simp [old, new, profile] at decoded
              have same : candidate = descriptor := decoded
              subst descriptor
              simpa [ApplicationSpkPackageIdentity.Descriptor.canonicalBytes, profile] using
                ApplicationSpkPackageIdentity.decoded_canonical_v2 new

theorem package_canonical_bytes_injective :
    Function.Injective ApplicationSpkPackageIdentity.Descriptor.canonicalBytes := by
  intro left right same
  have leftRead := package_decode_encode_selected left
  have rightRead := package_decode_encode_selected right
  rw [same] at leftRead
  exact Option.some.inj (leftRead.symm.trans rightRead)
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.package_canonical_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound, package_frame_lengths_equal_compiled._native.native_decide.ax_1_1, package_frames_distinct_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms package_canonical_bytes_injective

private def launchV2 : List UInt8 :=
  "DREGG/APPLICATION/SPK-LAUNCH-DESCRIPTOR/v2".toUTF8.toList

private def launchV3 : List UInt8 :=
  "DREGG/APPLICATION/SPK-LAUNCH-DESCRIPTOR/v3".toUTF8.toList

theorem launch_frame_lengths_equal_compiled : launchV2.length = launchV3.length := by
  native_decide
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.launch_frame_lengths_equal_compiled' depends on axioms: [propext, launch_frame_lengths_equal_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms launch_frame_lengths_equal_compiled

theorem launch_frames_distinct_compiled : launchV2 ≠ launchV3 := by
  native_decide
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.launch_frames_distinct_compiled' depends on axioms: [propext, launch_frames_distinct_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms launch_frames_distinct_compiled

private theorem launch_v2_rejects_v3
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor) :
    ApplicationSpkLaunchDescriptor.codec.decode
      (ApplicationSpkLaunchDescriptor.codecV3.encode descriptor) = none := by
  exact framed_distinct_decode_none
    ApplicationSpkLaunchDescriptor.descriptorStream launchV2 launchV3
    launch_frame_lengths_equal_compiled launch_frames_distinct_compiled descriptor

theorem launch_decode_encode_selected
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor) :
    ApplicationSpkLaunchDescriptor.decodeCanonical descriptor.canonicalBytes =
      some descriptor := by
  cases profile : descriptor.legacyProfile with
  | false =>
      simp [ApplicationSpkLaunchDescriptor.Descriptor.canonicalBytes,
        ApplicationSpkLaunchDescriptor.decodeCanonical, profile,
        launch_v2_rejects_v3, ApplicationSpkLaunchDescriptor.codecV3.decode_encode]
  | true =>
      simp [ApplicationSpkLaunchDescriptor.Descriptor.canonicalBytes,
        ApplicationSpkLaunchDescriptor.decodeCanonical, profile,
        ApplicationSpkLaunchDescriptor.codec.decode_encode]

theorem launch_decoded_canonical {bytes : List UInt8}
    {descriptor : ApplicationSpkLaunchDescriptor.Descriptor}
    (decoded : ApplicationSpkLaunchDescriptor.decodeCanonical bytes = some descriptor) :
    descriptor.canonicalBytes = bytes := by
  unfold ApplicationSpkLaunchDescriptor.decodeCanonical at decoded
  cases old : ApplicationSpkLaunchDescriptor.codec.decode bytes with
  | some candidate =>
      cases profile : candidate.legacyProfile with
      | false => simp [old, profile] at decoded
      | true =>
          simp [old, profile] at decoded
          have same : candidate = descriptor := decoded
          subst descriptor
          simpa [ApplicationSpkLaunchDescriptor.Descriptor.canonicalBytes, profile] using
            ApplicationSpkLaunchDescriptor.decoded_canonical old
  | none =>
      cases new : ApplicationSpkLaunchDescriptor.codecV3.decode bytes with
      | none => simp [old, new] at decoded
      | some candidate =>
          cases profile : candidate.legacyProfile with
          | true => simp [old, new, profile] at decoded
          | false =>
              simp [old, new, profile] at decoded
              have same : candidate = descriptor := decoded
              subst descriptor
              simpa [ApplicationSpkLaunchDescriptor.Descriptor.canonicalBytes, profile] using
                ApplicationSpkLaunchDescriptor.decoded_canonical_v3 new

theorem launch_canonical_bytes_injective :
    Function.Injective ApplicationSpkLaunchDescriptor.Descriptor.canonicalBytes := by
  intro left right same
  have leftRead := launch_decode_encode_selected left
  have rightRead := launch_decode_encode_selected right
  rw [same] at leftRead
  exact Option.some.inj (leftRead.symm.trans rightRead)
/-- info: 'Minidregg.Kernel.ApplicationSpkProfileProofs.launch_canonical_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound, launch_frame_lengths_equal_compiled._native.native_decide.ax_1_1, launch_frames_distinct_compiled._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms launch_canonical_bytes_injective

end Minidregg.Kernel.ApplicationSpkProfileProofs
