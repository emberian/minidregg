/-
Read-only presentation of an event21 committed permit frame. Only the private
op46 receiver may provide delivery provenance; decoding arbitrary bytes into
this JSON is never authority.
-/
import Kernel.ApplicationDispatchAgentReceiver
import Lean.Data.Json

namespace Minidregg.Host.ApplicationDispatchAgentInspection

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

private def headerJson (header : Header) : Json := .mkObj
  [("nameHex", hex header.name), ("valueHex", hex header.value),
   ("generated", .bool header.generated)]

private def receiptJson (receipt : NativeHostCodec.Receipt) : Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value),
   ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("worldRoot", decimal receipt.worldRoot.value)]

def inspect (bytes : List UInt8) : Except String Json := do
  let some (paid, receipt) :=
      ApplicationDispatchAgentReceiver.inspectCommittedBytes bytes
    | throw "noncanonical paid agent dispatch committed frame"
  let base := paid.candidate.base
  let app := base.dispatch.app
  let session := base.dispatch.session
  let identity := base.dispatch.identity
  let request := base.dispatch.request
  let context := paid.context
  let parent := paid.candidate.parent
  pure <| .mkObj
    [("type", "application-agent-dispatch-committed-inspection-v2"),
     ("frameByteCount", decimal bytes.length),
     ("frameHex", hex bytes),
     ("app", .mkObj
       [("resource", decimal app.resource),
        ("packageManifest", decimal app.packageManifest),
        ("generation", signed app.generation),
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
        ("origin", match session.origin with
          | .human => .mkObj [("type", "human")]
          | .agent task generation => .mkObj
              [("type", "agent"), ("task", decimal task),
               ("generation", signed generation)])]),
     ("identity", .mkObj
       [("principalHex", hex identity.principal),
        ("permissionSchemaRoot", decimal identity.permissionSchemaRoot.value),
        ("permissionBits", decimal identity.permissionBits)]),
     ("request", .mkObj
       [("operationId", decimal request.operationId),
        ("methodHex", hex request.method),
        ("pathHex", hex request.path),
        ("queryHex", hex request.query),
        ("headers", .arr <| request.headers.toArray.map headerJson),
        ("bodyHex", hex request.body)]),
     ("canonicalRequestHex", hex <| requestStream.encode request),
     ("physicalRequestDigest", decimal base.physicalRequestDigest.value),
     ("effectiveBits", .arr <| base.effectiveBits.toArray.map Json.bool),
     ("sessionFingerprint", decimal base.sessionFingerprint.value),
     ("ticketResource", decimal base.ticketResource),
     ("ticketRoot", decimal base.ticketRoot.value),
     ("enrollmentResource", decimal base.enrollmentResource),
     ("enrollmentRoot", decimal base.enrollmentRoot.value),
     ("authorityRoot", decimal base.authorityRoot.value),
     ("appRoot", decimal base.appRoot.value),
     ("sessionRoot", decimal base.sessionRoot.value),
     ("currentWorldRoot", decimal base.currentWorldRoot.value),
     ("issueTransaction", decimal base.issueTransaction.value),
     ("issueEvent", decimal base.issueEvent.value),
     ("dispatchTransaction", decimal base.dispatchTransaction.value),
     ("dispatchEvent", decimal base.dispatchEvent.value),
     ("parent", .mkObj
       [("task", decimal parent.task),
        ("generation", signed parent.generation),
        ("status", signed parent.status),
        ("remaining", signed parent.remaining),
        ("reserved", signed parent.reserved),
        ("innerRoot", decimal parent.innerRoot.value),
        ("physicalRoot", decimal parent.physicalRoot.value)]),
     ("purse", .mkObj
       [("task", decimal context.purseTask),
        ("generation", signed context.purseGeneration),
        ("payerSubject", decimal context.payerSubject.value),
        ("reserveAmount", signed context.reserveAmount),
        ("maximumCharge", signed context.maximumCharge),
        ("physicalRoot", decimal paid.pursePhysicalRoot.value),
        ("reserveOperationId", decimal context.reserveOperationId),
        ("reserveIndex", decimal paid.reserveIndex),
        ("originalReceipt", receiptJson paid.reserveReceipt)]),
     ("reserveContextHex", hex context.canonicalBytes),
     ("receipt", receiptJson receipt)]

end Minidregg.Host.ApplicationDispatchAgentInspection
