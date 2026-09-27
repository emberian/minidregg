/-
Read-only presentation of a descriptor-bound committed lifecycle claim frame.
The JSON is not authority: the physical host must retain the raw op26 callback
bytes, compare the echoed frame byte-for-byte, and check the descriptor
against one signature-verified SPK parse before launching its pinned unit.
-/
import Kernel.ApplicationLifecycleClaimProjection
import Kernel.ApplicationLifecycleResidentProfile
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleClaimInspection

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationLifecycleClaimProjection
open Minidregg.Kernel.ApplicationSpkPackageIdentity
open Minidregg.Kernel.ApplicationDispatchManifest
open Minidregg.Compiler.ResourceBirthCodec

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signedDecimal (value : Int) : Json := .str (toString value)

private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'

private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def kind : ApplicationLifecycleBegin.Kind → Json
  | .install => "install"
  | .start => "start"
  | .stop => "stop"
  | .upgrade => "upgrade"

private def interface (value : Interface) : Json := .mkObj
  [("id", decimal value.id), ("version", decimal value.version),
   ("kind", match value.kind with | .web => "web" | .api => "api"),
   ("root", decimal value.root.value),
   ("schemaRoot", decimal value.schema.root.value),
   ("canonicalHex", hex <| interfaceCodec.encode value)]

/-- Strictly decode v2 only. This is a structural view of the full canonical
frame, not proof that a caller obtained it from a fresh-tip op26 response. -/
def inspect (bytes : List UInt8) : Except String Json := do
  let some value := codecV2.decode bytes
    | throw "noncanonical descriptor-bound lifecycle claim frame"
  unless value.valid do
    throw "descriptor-bound lifecycle claim source shape refused"
  unless ApplicationLifecycleResidentProfile.claimMatches value do
    throw "claim is outside the resident signed-SPK physical hosting profile"
  let core := value.core
  let source := core.source.begin.source
  let descriptor := value.descriptor
  pure <| .mkObj
    [("type", "application-lifecycle-claim-committed-v2"),
     ("frameByteCount", decimal bytes.length),
     ("frameHex", hex bytes),
     ("app", decimal source.app),
     ("kind", kind source.kind),
     ("operationId", decimal source.operationId),
     ("processGeneration", signedDecimal source.processGeneration),
     ("processIdentityHex", hex source.processIdentity),
     ("imageIdentityHex", hex source.imageIdentity),
     ("packageManifest", decimal source.packageManifest),
     ("snapshotManifest", decimal source.snapshotManifest),
     ("packageDigest", decimal source.packageDigest.value),
     ("originalTransaction", decimal core.originalTransaction.value),
     ("originalEvent", decimal core.originalEvent.value),
     ("originalNullifier", decimal core.originalNullifier.value),
     ("claimNullifier", decimal core.claimNullifier.value),
     ("appPhysicalRoot", decimal core.appPhysicalRoot.value),
     ("packagePhysicalRoot", decimal core.packagePhysicalRoot.value),
     ("authorityPhysicalRoot", decimal core.authorityPhysicalRoot.value),
     ("postImageBoundary", decimal core.postImageBoundary.value),
     ("receipt", .mkObj
       [("transactionId", decimal core.claimReceipt.transactionId.value),
        ("eventId", decimal core.claimReceipt.eventId.value),
        ("acceptedCount", decimal core.claimReceipt.acceptedCount),
        ("imageBoundary", decimal core.claimReceipt.imageBoundary.value)]),
     ("descriptor", .mkObj
       [("canonicalHex", hex descriptor.canonicalBytes),
        ("root", decimal descriptor.root.value),
        ("rawSha256Hex", hex descriptor.rawSha256),
        ("rawLength", decimal descriptor.rawLength),
        ("signedAppIdHex", hex descriptor.signedAppId),
        ("signedAppVersion", decimal descriptor.signedAppVersion),
        ("manifestSha256Hex", hex descriptor.manifestSha256),
        ("bridgeConfigSha256Hex", hex descriptor.bridgeConfigSha256),
        ("bridgeApiPathHex", hex descriptor.bridgeApiPath),
        ("interfaces", .arr <| descriptor.interfaces.toArray.map interface)])]

end Minidregg.Host.ApplicationLifecycleClaimInspection
