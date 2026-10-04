/- Read-only custody presentation for a retry-CREATE event72 completion plan. -/
import Host.ApplicationLifecycleRetryCompletionV4Authoring
import Host.ApplicationLifecycleRetryBeginV4Inspection
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleRetryCompletionV4Inspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleRetryCompletionV4Authoring

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
    | throw "noncanonical retry completion operator request"
  let some begin := ApplicationLifecycleRetryBeginV4Ingress.codec.decode request.beginBytes
    | throw "noncanonical original retry BEGIN-v4"
  let some claim := ApplicationLifecycleRetryClaimV4Ingress.codec.decode
      request.claimIngressBytes
    | throw "noncanonical original retry claim-v4"
  let some report := ApplicationLifecycleRetryCompletionV4Report.signedCodec.decode
      request.signedReportBytes
    | throw "noncanonical signed v4 physical report"
  unless claim.originalBegin == begin && report.report.claim.originalClaim == claim do
    throw "retry completion originals differ"
  pure <| .mkObj <|
    ([("type", "application-lifecycle-retry-completion-request-v4"),
     ("canonicalRequestHex", hex bytes),
     ("originalBeginHex", hex request.beginBytes),
     ("originalClaimHex", hex request.claimIngressBytes),
     ("signedReportHex", hex request.signedReportBytes),
     ("app", decimal begin.begin.base.source.app),
     ("descriptorRoot", decimal begin.begin.descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       begin.begin.base.domain begin.begin.base.source.app)] : List (String × Json)) ++
    ApplicationLifecycleRetryBeginV4Inspection.selectorFields begin.retry

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical retry completion operator plan"
  let some source := ApplicationLifecycleRetryCompletionV4Source.codec.decode plan.sourceBytes
    | throw "noncanonical v4 retry completion source"
  let begin := source.originalBegin.begin
  unless source.valid &&
      plan.invocation.domain == begin.base.domain &&
      plan.invocation.semantics == begin.base.semantics &&
      plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (source.command plan.invocation.domain plan.invocation.semantics)) do
    throw "retry completion plan differs from source command"
  let request : Request :=
    { beginBytes := source.originalBegin.canonicalBytes
      claimIngressBytes := source.originalClaim.canonicalBytes
      signedReportBytes :=
        ApplicationLifecycleRetryCompletionV4Report.signedCodec.encode source.physical }
  pure <| .mkObj <|
    ([("type", "application-lifecycle-retry-completion-plan-v4"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("sourceHex", hex plan.sourceBytes),
     ("originalBeginHex", hex request.beginBytes),
     ("originalClaimHex", hex request.claimIngressBytes),
     ("signedReportHex", hex request.signedReportBytes),
     ("app", decimal source.app),
     ("descriptorRoot", decimal begin.descriptor.root.value),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       begin.base.domain source.app),
     ("currentAppRoot", decimal source.currentAppRoot.value),
     ("currentPackageRoot", decimal source.currentPackageRoot.value),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("slots", .arr <| (plan.invocation.slots ++
       [plan.packageObservationSlot]).toArray.map slotJson)] : List (String × Json)) ++
    ApplicationLifecycleRetryBeginV4Inspection.selectorFields source.originalBegin.retry

end Minidregg.Host.ApplicationLifecycleRetryCompletionV4Inspection
