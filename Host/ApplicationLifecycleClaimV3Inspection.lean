/-
Read-only presentation of the exact event24 committed frame. Decoding this
frame does not establish that it came from a fresh op26 callback; the physical
host must compare the echoed bytes with its retained native response.
-/
import Kernel.ApplicationLifecycleClaimV3Projection
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleClaimV3Inspection

open Lean
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
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

def inspect (bytes : List UInt8) : Except String Json := do
  let some value := ApplicationLifecycleClaimV3Projection.codec.decode bytes
    | throw "noncanonical launch-bound committed claim frame"
  unless value.valid do throw "launch-bound committed claim shape refused"
  let claim := value.originalClaim
  let begin := claim.originalBegin
  let source := begin.base.source
  let descriptor := begin.descriptor
  let core := value.core
  let selected := match begin.start with
    | none => Json.null
    | some binding => .mkObj
        [("choice", match binding.choice with
           | .create _ => "create" | .continue => "continue"),
         ("createIndex", match binding.choice with
           | .create index => decimal index | .continue => Json.null),
         ("commandDigest", decimal binding.commandDigest.value),
         ("priorCreate", match binding.priorCreate with
           | none => Json.null
           | some (receipt, custody) => .mkObj
               [("receiptHex", hex <| NativeHostCodec.receiptStream.encode receipt),
                ("custodyHex", hex <|
                  ApplicationLifecycleLaunchBinding.custodyStream.encode custody)])]
  pure <| .mkObj
    [("type", "application-lifecycle-claim-committed-v3"),
     ("frameByteCount", decimal bytes.length),
     ("frameHex", hex bytes),
     ("originalClaimHex", hex claim.canonicalBytes),
     ("originalBeginHex", hex begin.canonicalBytes),
     ("app", decimal source.app),
     ("kind", kind source.kind),
     ("clientOperationId", decimal begin.clientOperationId),
     ("authorizationOperationId", decimal source.operationId),
     ("processGeneration", signed source.processGeneration),
     ("processIdentityHex", hex source.processIdentity),
     ("imageIdentityHex", hex source.imageIdentity),
     ("packageManifest", decimal source.packageManifest),
     ("snapshotManifest", decimal source.snapshotManifest),
     ("descriptorHex", hex descriptor.canonicalBytes),
     ("descriptorRoot", decimal descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       begin.base.domain source.app),
     ("binding", selected),
     ("originalTransaction", decimal core.originalTransaction.value),
     ("originalEvent", decimal core.originalEvent.value),
     ("originalNullifier", decimal core.originalNullifier.value),
     ("claimNullifier", decimal core.claimNullifier.value),
     ("appPhysicalRoot", decimal core.appPhysicalRoot.value),
     ("packagePhysicalRoot", decimal core.packagePhysicalRoot.value),
     ("authorityPhysicalRoot", decimal core.authorityPhysicalRoot.value),
     ("postWorldRoot", decimal core.postWorldRoot.value),
     ("receipt", .mkObj
       [("transactionId", decimal core.claimReceipt.transactionId.value),
        ("eventId", decimal core.claimReceipt.eventId.value),
        ("acceptedCount", decimal core.claimReceipt.acceptedCount),
        ("worldRoot", decimal core.claimReceipt.worldRoot.value)])]

end Minidregg.Host.ApplicationLifecycleClaimV3Inspection
