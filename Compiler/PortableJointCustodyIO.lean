/- Source-bound custody for an actual appended joint reservation.
This preserves full source images/control envelope, historical quorum context
and exact checked commit. It is not a worker-transfer or overwrite capability.
No independent protocol journal or PENDING-to-YES shortcut is introduced.
-/
import Kernel.JointReceiver
import Compiler.PortableContinuationArchiveIO

namespace Minidregg.Compiler.PortableJointCustodyIO
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.JointReceiver
open Minidregg.Kernel.JointReceiverAdmission
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
set_option autoImplicit false

variable {config : Config} {opened : Opened config} {expected : Context}
  {reservation : Reserved config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable}

/-- Complete private source capsule. The full physical ResourceCell control
wrapper is retained within each whole source image, not replaced with a decoded
control payload. Context retains roster/config/epoch/instance/seed anchor.
Replica-local storage MACs remain physical artifacts of their existing owner. -/
def pendingFrame (receipt : Pending config opened expected reservation) : Bytes :=
  "DREGG.PORTABLE.JOINT-PENDING/v1".toUTF8.toList ++
    (StreamCodec.list bytesStream).encode [
      contextStream.encode expected,
      JointControlFrame.pinStream.encode reservation.pin,
      DurableReceiverCodec.encode opened.durable.image,
      DurableReceiverCodec.encode receipt.appended.next.image,
      reserveSourceBytes reservation.source,
      JointReceiver.sourcePayload reservation.intent,
      receipt.ordered.commitment.bytes]

/-- The only producer below captures and verifies actual immutable chunk custody
for this exact opaque Pending source receipt. It does not claim completeness of
other service/private-provider inventories or authorize their disclosure. -/
structure RetainedPending (archive : PortableContinuationArchiveIO.NativeConfig)
    (receipt : Pending config opened expected reservation) where
  private mk ::
  artifact : Artifact
  coordinate : String
  contentSha256 : String
  coordinateExact : artifact.coordinate = coordinate.toUTF8.toList

/-- Consume actual source append/readback/order authority, then retain its exact
capsule before it may join a portable manifest's required custody list. -/
def capturePending (archive : PortableContinuationArchiveIO.NativeConfig)
    (receipt : Pending config opened expected reservation) :
    IO (Except String (RetainedPending archive receipt)) := do
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "joint-pending.bin"
      IO.FS.writeBinFile path (pendingFrame receipt).toByteArray
      let mode ← IO.Process.output { cmd := "/usr/bin/chmod", args := #["0600",path.toString] }
      if mode.exitCode != 0 || mode.stderr != "" then
        return .error "joint pending private capture mode refused"
      let content ← IO.ofExcept (← RetainedArtifactIO.fileSha256 path)
      let coordinate := s!"native/joint-pending/v1/{content}"
      match ← PortableContinuationArchiveIO.captureArtifact archive coordinate.toUTF8.toList path with
      | .error detail => return .error detail
      | .ok artifact =>
        if exact : artifact.coordinate = coordinate.toUTF8.toList then
          return .ok ⟨artifact,coordinate,content,exact⟩
        else return .error "joint pending custody coordinate differs"
  catch _ => return .error "joint pending custody capture uncertain or refused"

/-- The caller cannot erase the appended reservation by supplying [] here.
This is the joint obligation only; existing service/private receivers must add
their own source-derived pending effects, spent anchors and retained outboxes. -/
def required (archive : PortableContinuationArchiveIO.NativeConfig)
    (receipt : Pending config opened expected reservation)
    (retained : RetainedPending archive receipt) : List Artifact := [retained.artifact]

/-- Quarantine manifest derives the entire next durable source image. Custody
generation is linkage only and does not change the source generation/roster. -/
def fromPending (receipt : Pending config opened expected reservation)
    (generation : Nat) (predecessor : Bytes) (artifacts : List Artifact) : Manifest :=
  PortableContinuationManifestCodec.fromImage
    ⟨config.deployment.domain,config.profile.semantics,config.expectedSeed⟩
    receipt.appended.next.image generation predecessor artifacts

theorem pending_manifest_exact (receipt : Pending config opened expected reservation)
    (generation : Nat) (predecessor : Bytes) (artifacts : List Artifact) :
    (fromPending receipt generation predecessor artifacts).image =
      DurableReceiverCodec.encode (opened.durable.image.append reservation.intent) := by
  change DurableReceiverCodec.encode receipt.appended.next.image = _
  rw [receipt.appended.image]

theorem pending_manifest_prefix (receipt : Pending config opened expected reservation)
    (generation : Nat) (predecessor : Bytes) (artifacts : List Artifact) :
    (fromPending receipt generation predecessor artifacts).prefix =
      PortableContinuationManifestCodec.prefixOf
        ⟨config.deployment.domain,config.profile.semantics,config.expectedSeed⟩
        receipt.appended.next.image := rfl

theorem repair_retains_pending (archive : PortableContinuationArchiveIO.NativeConfig)
    (receipt : Pending config opened expected reservation)
    (retained : RetainedPending archive receipt) (pin : ParticipantPin)
    (offered accepted : Manifest) (extension : ReceiptContinuity.Extension)
    (checked : acceptRepair pin (required archive receipt retained) offered extension = some accepted) :
    retained.artifact ∈ accepted.artifacts :=
  repair_retains_obligation checked (by simp [required])

#assert_axioms pending_manifest_exact
#assert_axioms pending_manifest_prefix
#assert_axioms repair_retains_pending
end Minidregg.Compiler.PortableJointCustodyIO
