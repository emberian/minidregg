/-
Read-only event26 committed-frame presentation. Only the native receiver can
mint the fresh-CAS permit; decoding this frame or JSON is not delivery
authority. Historical session origin and current execution generation are
shown separately.
-/
import Kernel.ApplicationAgentLifetimeDispatchReceiver
import Lean.Data.Json

namespace Minidregg.Host.ApplicationAgentLifetimeDispatchInspection

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]
private def receiptJson (receipt : NativeHostCodec.Receipt) : Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value),
   ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("imageBoundary", decimal receipt.imageBoundary.value)]

def inspect (bytes : List UInt8) : Except String Json := do
  let some (paid, receipt) :=
      ApplicationAgentLifetimeDispatchReceiver.inspectCommittedBytes bytes
    | throw "noncanonical lifetime agent dispatch committed frame"
  let base := paid.candidate.base
  let parent := paid.candidate.parent
  let app := base.dispatch.app
  let session := base.dispatch.session
  let identity := base.dispatch.identity
  let request := base.dispatch.request
  let context := paid.context
  pure <| .mkObj
    [("type", "application-agent-lifetime-dispatch-committed-inspection-v3"),
     ("frameByteCount", decimal bytes.length),
     ("frameHex", hex bytes),
     ("originalIssue", .mkObj
       [("index", decimal paid.originalIssueIndex),
        ("receipt", receiptJson paid.originalIssueReceipt),
        ("descriptorHex", hex paid.originalIssueDescriptor)]),
     ("grant", .mkObj
       [("resource", decimal context.grantResource),
        ("issueIndex", decimal context.grantIssueIndex),
        ("digest", decimal context.grantDigest.value),
        ("issueReceipt", receiptJson paid.grantIssueReceipt),
        ("initializedRoot", decimal paid.grantInitializedRoot.value),
        ("currentPhysicalRoot", decimal paid.grantPhysicalRoot.value)]),
     ("app", .mkObj
       [("resource", decimal app.resource),
        ("generation", signed app.generation),
        ("packageManifest", decimal app.packageManifest),
        ("packageVersion", signed app.packageVersion),
        ("snapshotVersion", signed app.snapshotVersion),
        ("packageRoot", decimal app.packageRoot.value),
        ("manifestRoot", decimal app.manifestRoot.value),
        ("interfaceId", decimal app.interfaceId),
        ("interfaceVersion", decimal app.interfaceVersion),
        ("interfaceRoot", decimal app.interfaceRoot.value),
        ("capability", decimal app.capability.value)]),
     ("session", .mkObj
       [("resource", decimal session.resource),
        ("appResource", decimal session.appResource),
        ("appGeneration", signed session.appGeneration),
        ("generation", signed session.generation),
        ("subject", decimal session.subject.value),
        ("kind", match session.kind with | .web => "web" | .api => "api"),
        ("originalOrigin", match session.origin with
          | .human => .mkObj [("type", "human")]
          | .agent task generation => .mkObj
              [("type", "agent"), ("task", decimal task),
               ("generation", signed generation)])]),
     ("identity", .mkObj
       [("principalHex", hex identity.principal),
        ("permissionSchemaRoot", decimal identity.permissionSchemaRoot.value),
        ("permissionBits", decimal identity.permissionBits)]),
     ("effectiveBits", .arr <| base.effectiveBits.toArray.map Json.bool),
     ("sessionFingerprint", decimal base.sessionFingerprint.value),
     ("request", .mkObj
       [("operationId", decimal request.operationId),
        ("canonicalHex", hex <| requestStream.encode request),
        ("methodHex", hex request.method),
        ("pathHex", hex request.path),
        ("queryHex", hex request.query),
        ("bodyHex", hex request.body),
        ("physicalDigest", decimal base.physicalRequestDigest.value)]),
     ("currentImage", .mkObj
       [("authorityRoot", decimal base.authorityRoot.value),
        ("appRoot", decimal base.appRoot.value),
        ("sessionRoot", decimal base.sessionRoot.value),
        ("ticketRoot", decimal base.ticketRoot.value),
        ("enrollmentRoot", decimal base.enrollmentRoot.value),
        ("boundary", decimal base.currentImageBoundary.value)]),
     ("parent", .mkObj
       [("task", decimal parent.task),
        ("generation", signed parent.generation),
        ("status", signed parent.status),
        ("remaining", signed parent.remaining),
        ("reserved", signed parent.reserved),
        ("innerRoot", decimal parent.innerRoot.value),
        ("physicalRoot", decimal parent.physicalRoot.value)]),
     ("purse", .mkObj
       [("task", decimal context.base.purseTask),
        ("generation", signed context.base.purseGeneration),
        ("payerSubject", decimal context.base.payerSubject.value),
        ("reserveAmount", signed context.base.reserveAmount),
        ("maximumCharge", signed context.base.maximumCharge),
        ("physicalRoot", decimal paid.pursePhysicalRoot.value),
        ("reserveOperationId", decimal context.base.reserveOperationId),
        ("reserveIndex", decimal paid.reserveIndex),
        ("reserveReceipt", receiptJson paid.reserveReceipt),
        ("reserveNonce", decimal paid.reserveNonce)]),
     ("reserveContextHex", hex context.canonicalBytes),
     ("dispatchReceipt", receiptJson receipt)]

end Minidregg.Host.ApplicationAgentLifetimeDispatchInspection
