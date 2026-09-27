/-
Read-only presentation of an application dispatch committed frame. Decoding a
frame does not establish that it came from the exact post-CAS op34 callback;
the physical host must retain that private transport provenance separately.
-/
import Kernel.ApplicationDispatchReceiver
import Lean.Data.Json

namespace Minidregg.Host.ApplicationDispatchInspection

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationDispatchCodec

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signedDecimal (value : Int) : Json := .str (toString value)

private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'

private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def originJson : Origin → Json
  | .human => .mkObj [("type", "human")]
  | .agent task generation => .mkObj
      [("type", "agent"), ("task", decimal task),
       ("generation", signedDecimal generation)]

private def kindJson : InterfaceKind → Json
  | .web => "web"
  | .api => "api"

private def headerJson (header : Header) : Json := .mkObj
  [("nameHex", hex header.name), ("valueHex", hex header.value),
   ("generated", .bool header.generated)]

/-- Strict projection of a committed-frame *shape*. It is safe for an
operator-private inspector, but its JSON is never a delivery authority. -/
def inspect (bytes : List UInt8) : Except String Json := do
  let some (candidate, receipt) :=
      ApplicationDispatchReceiver.inspectCommittedBytes bytes
    | throw "noncanonical application dispatch committed frame"
  let dispatch := candidate.dispatch
  let app := dispatch.app
  let session := dispatch.session
  let identity := dispatch.identity
  let request := dispatch.request
  pure <| .mkObj
    [("type", "application-dispatch-committed-inspection-v1"),
     ("frameByteCount", decimal bytes.length),
     ("frameHex", hex bytes),
     ("app", .mkObj
       [("resource", decimal app.resource),
        ("packageManifest", decimal app.packageManifest),
        ("generation", signedDecimal app.generation),
        ("packageVersion", signedDecimal app.packageVersion),
        ("snapshotVersion", signedDecimal app.snapshotVersion),
        ("packageRoot", decimal app.packageRoot.value),
        ("manifestRoot", decimal app.manifestRoot.value),
        ("interfaceId", decimal app.interfaceId),
        ("interfaceVersion", decimal app.interfaceVersion),
        ("interfaceRoot", decimal app.interfaceRoot.value),
        ("capability", decimal app.capability.value)]),
     ("session", .mkObj
       [("kind", kindJson session.kind),
        ("resource", decimal session.resource),
        ("appResource", decimal session.appResource),
        ("appGeneration", signedDecimal session.appGeneration),
        ("generation", signedDecimal session.generation),
        ("subject", decimal session.subject.value),
        ("capability", decimal session.capability.value),
        ("origin", originJson session.origin)]),
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
     ("effectiveBits", .arr <| candidate.effectiveBits.toArray.map Json.bool),
     ("sessionFingerprint", decimal candidate.sessionFingerprint.value),
     ("ticketResource", decimal candidate.ticketResource),
     ("ticketRoot", decimal candidate.ticketRoot.value),
     ("enrollmentResource", decimal candidate.enrollmentResource),
     ("enrollmentRoot", decimal candidate.enrollmentRoot.value),
     ("authorityRoot", decimal candidate.authorityRoot.value),
     ("appRoot", decimal candidate.appRoot.value),
     ("sessionRoot", decimal candidate.sessionRoot.value),
     ("issueTransaction", decimal candidate.issueTransaction.value),
     ("issueEvent", decimal candidate.issueEvent.value),
     ("dispatchTransaction", decimal candidate.dispatchTransaction.value),
     ("dispatchEvent", decimal candidate.dispatchEvent.value),
     ("currentImageBoundary", decimal candidate.currentImageBoundary.value),
     ("physicalRequestDigest", decimal candidate.physicalRequestDigest.value),
     ("receipt", .mkObj
       [("transactionId", decimal receipt.transactionId.value),
        ("eventId", decimal receipt.eventId.value),
        ("acceptedCount", decimal receipt.acceptedCount),
        ("imageBoundary", decimal receipt.imageBoundary.value)])]

end Minidregg.Host.ApplicationDispatchInspection
