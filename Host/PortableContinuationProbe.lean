/- Operator-local quarantined portable custody experiment.
The existing retained source capsule re-admits the entire native journal and
pins original code/profile/config/genesis. It never starts a public service.
Physical inventory completeness is supplied by the existing service manager;
this probe does not mint a source transfer or worker activation permit.
-/
import Compiler.CarriedSegmentIO
import Compiler.PortableContinuationArchiveIO

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.PortableContinuationManifestCodec
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Theory.TypedAuthorization

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def stringField (value : Json) (name : String) : Except String String :=
  (field value name).bind Json.getStr?
private def natural (value : Json) : Except String Nat := do
  let text ← value.getStr?
  let some result := text.toNat? | throw "canonical decimal required"
  if toString result != text then throw "canonical decimal required"
  return result
private def digest (value : Json) : Except String Digest := do
  let result ← natural value
  if result ≥ 2^256 then throw "digest exceeds bound"
  return ⟨result⟩
private def unhex (text : String) : Except String Bytes := do
  let input := text.toUTF8
  if input.size % 2 != 0 then throw "even-length hexadecimal required"
  let nibble := fun (byte : UInt8) =>
    if byte ≥ 48 && byte ≤ 57 then some (byte.toNat - 48)
    else if byte ≥ 97 && byte ≤ 102 then some (byte.toNat - 87)
    else none
  let mut result := ByteArray.empty
  for i in [:input.size / 2] do
    let some high := nibble input[2*i]! | throw "canonical lowercase hexadecimal required"
    let some low := nibble input[2*i+1]! | throw "canonical lowercase hexadecimal required"
    result := result.push (UInt8.ofNat (16 * high + low))
  return result.toList

private def pinBytes (value : Json) : Except String Bytes := do
  let text ← value.getStr?
  let bytes ← unhex text
  if bytes.length != 32 then throw "artifact pin must be SHA256"
  return bytes
private def capsule (value : Json) : Except String CarriedSegmentIO.SourceCapsule := do
  let path := fun name => System.FilePath.mk <$> stringField value name
  let identity ← field value "identity"
  let pins ← field value "pins"
  return {
    host := ← path "host"
    configuration := ← path "configuration"
    profile := ← path "profile"
    signatureVerifier := ← path "signatureVerifier"
    storage := {
      binary := ← path "storageBinary"
      root := ← path "storageRoot"
      key := ← path "checkpointKey" }
    identity := ⟨← digest (← field identity "domain"), ← digest (← field identity "semantics"),
      ← digest (← field identity "expectedSeed")⟩
    pins := ⟨← pinBytes (← field pins "host"), ← pinBytes (← field pins "storageHelper"),
      ← pinBytes (← field pins "signatureVerifier"), ← pinBytes (← field pins "configuration"),
      ← pinBytes (← field pins "profile")⟩ }

private def archiveConfig (value : Json) : Except String PortableContinuationArchiveIO.NativeConfig := do
  return ⟨System.FilePath.mk (← stringField value "binary"), ← stringField value "binarySha256",
    System.FilePath.mk (← stringField value "root")⟩

private def artifactInputs (value : Json) : Except String (List (Bytes × System.FilePath)) := do
  let array ← value.getArr?
  if array.size > 4096 then throw "physical custody inventory exceeds bound"
  array.toList.mapM fun entry => do
    return ((← stringField entry "coordinate").toUTF8.toList,
      System.FilePath.mk (← stringField entry "source"))

/-- The held endpoint comes from the participant's independently retained
public pin file. Identity/key/subject are pinned in operator config; none comes
from the restored manifest or source archive. Bootstrap custody is external. -/
private def heldPin (value : Json) (identity : Identity) : IO ParticipantPin := do
  let subject : SubjectId := ⟨← IO.ofExcept (natural (← IO.ofExcept (field value "subject")))⟩
  let key ← IO.ofExcept (pinBytes (← IO.ofExcept (field value "publicKey")))
  let path ← IO.ofExcept (stringField value "heldPin")
  let bytes := (← IO.FS.readBinFile path).toList
  let tag := "DREGG.PORTABLE.PARTICIPANT-ACK/v1".toUTF8.toList
  let some ack := acknowledgementStream.toLawful.decode (bytes.drop tag.length)
    | throw (IO.userError "participant held public pin malformed")
  if acknowledgementFrame ack != bytes || ack.participant != subject ||
      ack.publicKey != key || ack.identity != identity then
    throw (IO.userError "participant held identity/key/subject differs")
  return ⟨ack.participant,ack.publicKey,ack.identity,ack.point⟩

private def report (manifest : Manifest) : Json :=
  Json.mkObj [
    ("type", .str "mini-portable-quarantined-custody-v1"),
    ("sourceIdentity", Json.mkObj [("domain",.str (toString manifest.prefix.identity.domain.value)),
      ("semantics",.str (toString manifest.prefix.identity.semantics.value)),
      ("expectedSeed",.str (toString manifest.prefix.identity.expectedSeed.value))]),
    ("height",.str (toString manifest.point.height)),
    ("worldRoot",.str (toString manifest.point.worldRoot.value)),
    ("custodyGeneration",.str (toString manifest.generation)),
    ("artifactCount",.str (toString manifest.artifacts.length)),
    ("activation",.str "not-authorized")]

/-- Operator-supplied config may relocate physical source paths but must retain
all independently pinned original capsule bytes/identity. Source config parses
remain owned by the actual source executable, never this transport probe. -/
def portableProbe (configuration : System.FilePath) (mode : String) : IO Unit := do
  let value ← IO.ofExcept (Json.parse (← IO.FS.readFile configuration))
  let sourceConfig ← IO.ofExcept (capsule (← IO.ofExcept (field value "source")))
  let archive ← IO.ofExcept (archiveConfig (← IO.ofExcept (field value "archive")))
  let source ← IO.ofExcept (← CarriedSegmentIO.auditSource sourceConfig)
  let identity : Identity := ⟨sourceConfig.identity.domain, sourceConfig.identity.semantics,
    sourceConfig.identity.genesis⟩
  let manifestPath ← IO.ofExcept (stringField value "manifest")
  match mode with
  | "capture" =>
    let inputs ← IO.ofExcept (artifactInputs (← IO.ofExcept (field value "artifacts")))
    let artifacts ← inputs.mapM fun input => do
      IO.ofExcept (← PortableContinuationArchiveIO.captureArtifact archive input.1 input.2)
    let generation ← IO.ofExcept (natural (← IO.ofExcept (field value "generation")))
    let predecessorText ← IO.ofExcept (stringField value "predecessorHex")
    let predecessor ← IO.ofExcept (unhex predecessorText)
    let manifest := fromImage identity source.durable.image generation predecessor artifacts
    let readback ← IO.ofExcept (← PortableContinuationArchiveIO.retain archive manifest)
    let _ ← IO.ofExcept (← PortableContinuationArchiveIO.exportQuarantined archive manifest readback manifestPath)
    let inventoryPin ← IO.ofExcept (← RetainedArtifactIO.fileSha256 readback.inventory)
    IO.println ((report manifest).setObjVal! "manifestInventory" (.str readback.inventory.toString)
      |>.setObjVal! "manifestInventorySha256" (.str inventoryPin)).compress
  | "check-restored" =>
    let some manifest := decode (← IO.FS.readBinFile manifestPath).toList
      | throw (IO.userError "portable canonical manifest refused")
    if manifest.prefix != prefixOf identity source.durable.image ||
        manifest.point != pointOf identity source.durable.image ||
        manifest.image != DurableReceiverCodec.encode source.durable.image then
      throw (IO.userError "portable whole source image identity/cut differs")
    let participant ← IO.ofExcept (field value "participant")
    let pin ← heldPin participant identity
    let extensionPath ← IO.ofExcept (stringField participant "extension")
    let extensionJson ← IO.ofExcept (Json.parse (← IO.FS.readFile extensionPath))
    let extension ← IO.ofExcept (Minidregg.Host.ReceiptContinuity.parseExtension extensionJson)
    let proposed : Acknowledgement := ⟨pin.participant,pin.publicKey,manifest.prefix.identity,manifest.point⟩
    if (acknowledge pin proposed extension).isNone then
      throw (IO.userError "portable repair conflicts with independently held participant history")
    let inventoryPath ← IO.ofExcept (stringField value "manifestInventory")
    let inventoryPin ← IO.ofExcept (stringField value "manifestInventorySha256")
    IO.ofExcept (← RetainedArtifactIO.checkedFile inventoryPath inventoryPin)
    let inventory := (← IO.FS.readBinFile inventoryPath).toList
    let _ ← IO.ofExcept (← PortableContinuationArchiveIO.reopen archive manifest inventoryPath inventory)
    IO.println (report manifest).compress
  | _ => throw (IO.userError "portable probe mode must be capture or check-restored")

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [configuration, mode] =>
      portableProbe configuration mode
      return (0 : UInt32)
    | _ =>
      IO.eprintln "usage: portable-continuation-probe OPERATOR_CONFIG capture|check-restored"
      return (2 : UInt32)
  catch error =>
    IO.eprintln s!"portable custody candidate refused: {error}"
    return (1 : UInt32)
