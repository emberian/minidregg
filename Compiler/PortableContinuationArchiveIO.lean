/- Physical archive-before-ACK seam. Uses the shared exact chunk archive,
then reconstructs and compares the WHOLE canonical private manifest before
minting opaque readback. The manifest is not exported to participants.
Native helper/OS/disk durability remain explicit physical assumptions.
-/
import Compiler.PortableContinuationManifestCodec
import Compiler.CredentialSignatureIO
import Compiler.RetainedArtifactIO

namespace Minidregg.Compiler.PortableContinuationArchiveIO
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Compiler.PortableContinuationManifestCodec
set_option autoImplicit false

structure NativeConfig where
  binary : System.FilePath
  binarySha256 : String
  /-- Independently provisioned private archive directory, not selected by request. -/
  root : System.FilePath

/-- No caller can mint this from a hash string, successful send, or ACK Boolean. -/
structure Readback (config : NativeConfig) (manifest : Manifest) where
  private mk ::
  inventory : System.FilePath
  exactInventory : Bytes

private def readBounded (handle : IO.FS.Handle) (bound : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size ≤ bound do
    let part ← handle.read (min 65536 (bound + 1 - bytes.size)).toUSize
    if part.isEmpty then return bytes
    bytes := bytes ++ part
  throw (IO.userError "portable archive executable exceeds bound")

private def run (config : NativeConfig) (args : Array String) (response : String) : IO Unit := do
  -- Execute the exact verified private snapshot, not a mutable path checked
  -- before spawning. This pins code/config without claiming semantic authority.
  IO.FS.withTempDir fun directory => do
    let snapshot := directory / "archive-helper"
    IO.FS.withFile config.binary .read fun handle => do
      let bytes ← readBounded handle (64 * 1024 * 1024)
      IO.FS.writeBinFile snapshot bytes
    let mode ← IO.Process.output { cmd := "/usr/bin/chmod", args := #["0500", snapshot.toString] }
    if mode.exitCode != 0 || mode.stderr != "" then
      throw (IO.userError "portable archive executable snapshot mode failed")
    match ← RetainedArtifactIO.checkedFile snapshot config.binarySha256 with
    | .error detail => throw (IO.userError detail)
    | .ok () => pure ()
    let output ← IO.Process.output { cmd := snapshot.toString, args }
    if output.exitCode != 0 || output.stderr != "" || output.stdout != response then
      throw (IO.userError "portable archive helper refused or reply uncertain")

private def privateMode (path : System.FilePath) : IO Unit := do
  let output ← IO.Process.output { cmd := "/usr/bin/chmod", args := #["0600", path.toString] }
  if output.exitCode != 0 || output.stderr != "" then
    throw (IO.userError "portable private custody mode failed")

/-- All physical artifacts share the chunk inventory mechanics. The existing
owner selects the coordinate/file under its source pause or driver lock. This
function does not derive permission to read that file or publish its bytes. -/
def captureArtifact (config : NativeConfig) (coordinate : Bytes) (source : System.FilePath) :
    IO (Except String Artifact) := do
  try
    let some label := String.fromUTF8? coordinate.toByteArray
      | return .error "portable source coordinate must be canonical UTF-8"
    let contentPin ← IO.ofExcept (← RetainedArtifactIO.fileSha256 source)
    IO.FS.withTempDir fun directory => do
      let coordinatePath := directory / "coordinate"
      IO.FS.writeBinFile coordinatePath coordinate.toByteArray
      let coordinatePin ← IO.ofExcept (← RetainedArtifactIO.fileSha256 coordinatePath)
      let inventory := config.root / s!"artifact-{coordinatePin}-{contentPin}.json"
      run config #["capture", (config.root / "chunks").toString, label,
        source.toString, inventory.toString] "retained\n"
      run config #["verify", (config.root / "chunks").toString, inventory.toString] "retained\n"
      return .ok ⟨coordinate, (← IO.FS.readBinFile inventory).toList⟩
  catch _ => return .error "portable artifact capture uncertain or refused"

private def verifyArtifacts (config : NativeConfig) (manifest : Manifest) : IO Unit := do
  IO.FS.withTempDir fun directory => do
    for artifact in manifest.artifacts do
      let inventory := directory / "artifact.json"
      IO.FS.writeBinFile inventory artifact.exactInventory.toByteArray
      privateMode inventory
      run config #["verify", (config.root / "chunks").toString, inventory.toString] "retained\n"

/-- Immutable capture plus full independent readback precedes this returned token.
A failed/uncertain response exposes no acknowledgement and no activation right.
Repeated exact capture uses the same inventory; substitution refuses. -/
def retain (config : NativeConfig) (manifest : Manifest) : IO (Except String (Readback config manifest)) := do
  try
    verifyArtifacts config manifest
    IO.FS.withTempDir fun directory => do
      let source := directory / "manifest.bin"
      let restored := directory / "readback.bin"
      let bytes := PortableContinuationManifestCodec.encode manifest
      IO.FS.writeBinFile source bytes.toByteArray
      privateMode source
      let fingerprint ← IO.ofExcept (← RetainedArtifactIO.fileSha256 source)
      let inventory := config.root / s!"manifest-{fingerprint}.json"
      let chunks := config.root / "chunks"
      run config #["capture", chunks.toString, "native/portable/canonical-manifest-v1",
        source.toString, inventory.toString] "retained\n"
      run config #["verify", chunks.toString, inventory.toString] "retained\n"
      run config #["restore-new", chunks.toString, inventory.toString, restored.toString] "retained\n"
      if (← IO.FS.readBinFile restored).toList != bytes then
        return .error "portable archive exact manifest readback differs"
      return .ok ⟨inventory, (← IO.FS.readBinFile inventory).toList⟩
  catch _ => return .error "portable archive retention uncertain or refused"

/-- Restart rechecks the exact retained inventory and reconstructs canonical
bytes. This is custody recovery, never new source authority or secret release. -/
def reopen (config : NativeConfig) (manifest : Manifest) (inventory : System.FilePath)
    (exactInventory : Bytes) : IO (Except String (Readback config manifest)) := do
  try
    verifyArtifacts config manifest
    if (← IO.FS.readBinFile inventory).toList != exactInventory then
      return .error "portable retained inventory differs"
    IO.FS.withTempDir fun directory => do
      let restored := directory / "manifest.bin"
      let chunks := config.root / "chunks"
      run config #["verify", chunks.toString, inventory.toString] "retained\n"
      run config #["restore-new", chunks.toString, inventory.toString, restored.toString] "retained\n"
      if (← IO.FS.readBinFile restored).toList != PortableContinuationManifestCodec.encode manifest then
        return .error "portable recovered manifest differs"
      return .ok ⟨inventory, exactInventory⟩
  catch _ => return .error "portable archive reopen uncertain or refused"

/-- A newly created private quarantine file is reconstructed only after fresh
readback. Existing files refuse; the native helper fsyncs file and parent and
rechecks exact bytes. This exports no execution or worker activation permit. -/
def exportQuarantined (config : NativeConfig) (manifest : Manifest)
    (readback : Readback config manifest) (destination : System.FilePath) :
    IO (Except String Unit) := do
  match ← reopen config manifest readback.inventory readback.exactInventory with
  | .error detail => return .error detail
  | .ok _ => pure ()
  try
    run config #["restore-new", (config.root / "chunks").toString,
      readback.inventory.toString, destination.toString] "retained\n"
    if (← IO.FS.readBinFile destination).toList != PortableContinuationManifestCodec.encode manifest then
      return .error "portable exported quarantine bytes differ"
    return .ok ()
  catch _ => return .error "portable quarantine export uncertain or refused"

/-- Participant verification is only an independently pinned public commitment.
The archive token makes the durability-before-ACK order structural in this API.
It does not carry any source-authorized overwrite or transfer token. -/
structure CheckedAcknowledgement (pin : ParticipantPin) (manifest : Manifest) where
  private mk ::
  next : ParticipantPin
  acknowledgement : Acknowledgement
  extension : Minidregg.Kernel.ReceiptContinuity.Extension
  exact : acknowledge pin acknowledgement extension = some next
  manifestIdentity : acknowledgement.identity = manifest.prefix.identity
  manifestPoint : acknowledgement.point = manifest.point

def acknowledgeRetained (archive : NativeConfig) (signature : CredentialSignatureIO.NativeConfig)
    (pin : ParticipantPin) (manifest : Manifest) (readback : Readback archive manifest)
    (extension : Minidregg.Kernel.ReceiptContinuity.Extension) (detached : Bytes) :
    IO (Except String (CheckedAcknowledgement pin manifest)) := do
  match ← reopen archive manifest readback.inventory readback.exactInventory with
  | .error detail => return .error detail
  | .ok _ => pure ()
  let ack : Acknowledgement := ⟨pin.participant, pin.publicKey, manifest.prefix.identity, manifest.point⟩
  match ← CredentialSignatureIO.verify signature pin.publicKey (acknowledgementFrame ack) detached with
  | .ok true =>
    match checked : acknowledge pin ack extension with
    | none => return .error "portable participant history refused"
    | some next => return .ok ⟨next, ack, extension, checked, rfl, rfl⟩
  | .ok false => return .error "portable participant signature refused"
  | .error _ => return .error "portable participant signature verification unavailable"

end Minidregg.Compiler.PortableContinuationArchiveIO
