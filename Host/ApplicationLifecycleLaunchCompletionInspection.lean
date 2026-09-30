/- Read-only custody presentation for a launch-bound event25 completion plan. -/
import Host.ApplicationLifecycleLaunchCompletionAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleLaunchCompletionInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleLaunchCompletionAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
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
         ("validUntil", decimal header.validUntil),
         ("domainHex", hex header.domain),
         ("messageHex", hex header.message),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signing)]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch completion operator request"
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode request.beginBytes
    | throw "noncanonical original v3 BEGIN"
  let some claim := ApplicationLifecycleClaimV3Ingress.codec.decode
      request.claimIngressBytes
    | throw "noncanonical original v3 claim"
  let some report := ApplicationLifecycleCompletionV2Report.signedCodec.decode
      request.signedReportBytes
    | throw "noncanonical signed v2 physical report"
  unless claim.originalBegin == begin && report.report.claim.originalClaim == claim do
    throw "completion originals differ"
  pure <| .mkObj
    [("type", "application-lifecycle-launch-completion-request-v1"),
     ("canonicalRequestHex", hex bytes),
     ("originalBeginHex", hex request.beginBytes),
     ("originalClaimHex", hex request.claimIngressBytes),
     ("signedReportHex", hex request.signedReportBytes),
     ("app", decimal begin.base.source.app),
     ("descriptorRoot", decimal begin.descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       begin.base.domain begin.base.source.app)]

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical launch completion operator plan"
  let some source := ApplicationLifecycleCompletionV2Source.codec.decode plan.sourceBytes
    | throw "noncanonical v2 completion source"
  unless source.valid &&
      plan.invocation.domain == source.originalBegin.base.domain &&
      plan.invocation.semantics == source.originalBegin.base.semantics &&
      plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (source.command plan.invocation.domain plan.invocation.semantics)) do
    throw "completion plan differs from source command"
  let request : Request :=
    { beginBytes := source.originalBegin.canonicalBytes
      claimIngressBytes := source.originalClaim.canonicalBytes
      signedReportBytes :=
        ApplicationLifecycleCompletionV2Report.signedCodec.encode source.physical }
  pure <| .mkObj
    [("type", "application-lifecycle-launch-completion-plan-v1"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("sourceHex", hex plan.sourceBytes),
     ("originalBeginHex", hex request.beginBytes),
     ("originalClaimHex", hex request.claimIngressBytes),
     ("signedReportHex", hex request.signedReportBytes),
     ("app", decimal source.app),
     ("descriptorRoot", decimal source.originalBegin.descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       source.originalBegin.base.domain source.app),
     ("currentAppRoot", decimal source.currentAppRoot.value),
     ("currentPackageRoot", decimal source.currentPackageRoot.value),
     ("imageBoundary", decimal plan.invocation.imageBoundary.value),
     ("height", decimal plan.invocation.height),
     ("slots", .arr <| (plan.invocation.slots ++
       [plan.packageObservationSlot]).toArray.map slotJson)]

end Minidregg.Host.ApplicationLifecycleLaunchCompletionInspection
