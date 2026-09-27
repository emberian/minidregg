/- Read-only operator presentation of one source-authored v3 launch claim plan. -/
import Host.ApplicationLifecycleLaunchClaimAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleLaunchClaimInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleLaunchClaimAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def slotJson (slot : SigningSlot) : Json :=
  let signing := match CredentialSignedEnvelopeController.headerCodec.decode
      slot.header with
    | none => .mkObj [("decoded", .bool false)]
    | some header => .mkObj
        [("decoded", .bool true),
         ("keyId", decimal header.keyId),
         ("keyEpoch", decimal header.keyEpoch),
         ("algorithm", decimal header.algorithm),
         ("authorityRoot", decimal header.authorityRoot.value),
         ("domainHex", hex header.domain),
         ("messageHex", hex header.message),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signing)]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch claim request"
  pure <| .mkObj
    [("type", "application-lifecycle-launch-claim-request-v1"),
     ("canonicalRequestHex", hex bytes),
     ("originalIndex", decimal request.originalIndex),
     ("queryNonce", decimal request.queryNonce)]

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical launch claim plan"
  let some source := ApplicationLifecycleClaim.codec.decode plan.sourceBytes
    | throw "noncanonical launch claim source"
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode plan.originalBeginBytes
    | throw "noncanonical original v3 launch BEGIN"
  unless source.valid && source.begin == begin.base && begin.shape &&
      plan.invocation.domain == begin.base.domain &&
      plan.invocation.semantics == begin.base.semantics &&
      plan.originalBeginReceipt.transactionId == begin.base.transactionId &&
      plan.originalBeginReceipt.eventId ==
        (ApplicationLifecycleBeginV3Ingress.event begin).eventId &&
      plan.originalBeginReceipt.acceptedCount == source.originalIndex + 1 &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (ApplicationLifecycleClaim.command plan.invocation.domain
            plan.invocation.semantics source)) do
    throw "launch claim plan differs from original BEGIN or signed command"
  let request : Request :=
    { originalIndex := source.originalIndex, queryNonce := source.queryNonce }
  let bindingJson := match begin.start with
    | none => Json.null
    | some binding => Json.mkObj
        [("choice", match binding.choice with
           | .create _ => Json.str "create" | .continue => Json.str "continue"),
         ("createIndex", match binding.choice with
           | .create index => decimal index | .continue => Json.null),
         ("commandDigest", decimal binding.commandDigest.value),
         ("priorCreate", match binding.priorCreate with
           | none => Json.null
           | some (receipt, custody) => Json.mkObj
               [("receiptHex", hex <| NativeHostCodec.receiptStream.encode receipt),
                ("custodyHex", hex <|
                  ApplicationLifecycleLaunchBinding.custodyStream.encode custody)])]
  pure <| .mkObj
    [("type", "application-lifecycle-launch-claim-plan-v1"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("sourceHex", hex plan.sourceBytes),
     ("originalBeginHex", hex plan.originalBeginBytes),
     ("originalBeginReceiptHex", hex <|
       NativeHostCodec.receiptStream.encode plan.originalBeginReceipt),
     ("originalBeginTransactionId", decimal
       plan.originalBeginReceipt.transactionId.value),
     ("originalBeginEventId", decimal plan.originalBeginReceipt.eventId.value),
     ("originalBeginAcceptedCount", decimal plan.originalBeginReceipt.acceptedCount),
     ("originalBeginImageBoundary", decimal
       plan.originalBeginReceipt.imageBoundary.value),
     ("descriptorHex", hex begin.descriptor.canonicalBytes),
     ("descriptorRoot", decimal begin.descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       begin.base.domain source.begin.source.app),
     ("binding", bindingJson),
     ("clientOperationId", decimal begin.clientOperationId),
     ("authorizationOperationId", decimal begin.base.source.operationId),
     ("originalIndex", decimal source.originalIndex),
     ("queryNonce", decimal source.queryNonce),
     ("app", decimal source.begin.source.app),
     ("managementSubject", decimal source.begin.source.managementSubject.value),
     ("beforeGeneration", signed source.before.generation),
     ("beforePhase", signed source.before.phase),
     ("currentAuthorityRoot", decimal source.currentAuthorityRoot.value),
     ("currentAppRoot", decimal source.currentAppRoot.value),
     ("currentPackageRoot", decimal source.currentPackageRoot.value),
     ("currentImageBoundary", decimal source.currentImageBoundary.value),
     ("imageBoundary", decimal plan.invocation.imageBoundary.value),
     ("height", decimal plan.invocation.height),
     ("slots", .arr <| (plan.invocation.slots ++
       [plan.appObservationSlot, plan.packageObservationSlot]).toArray.map slotJson)]

end Minidregg.Host.ApplicationLifecycleLaunchClaimInspection
