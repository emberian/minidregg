/-
Read-only custody presentation for source-authored event21 signing plans. JSON
and decoded canonical bytes are never authority; native op46 re-admits the
assembled ingress at the current verified tip before CAS.
-/
import Kernel.ApplicationDispatchAgentPaidAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationDispatchAgentPaidInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationDispatchAgentPaidAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def slotJson (slot : SigningSlot) : Json :=
  let signed := match CredentialSignedEnvelopeController.headerCodec.decode
      slot.header with
    | none => .mkObj [("decoded", .bool false)]
    | some header => .mkObj
        [("decoded", .bool true), ("keyId", decimal header.keyId),
         ("keyEpoch", decimal header.keyEpoch),
         ("algorithm", decimal header.algorithm),
         ("authorityRoot", decimal header.authorityRoot.value),
         ("messageHex", hex header.message),
         ("domainHex", hex header.domain),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signed)]

private def contextJson (context : ApplicationDispatchAgentReserveContext.Context) : Json :=
  .mkObj
    [("canonicalHex", hex context.canonicalBytes),
     ("nonce", decimal <| ApplicationDispatchAgentReserveContext.nonce context),
     ("domain", decimal context.domain.value),
     ("semantics", decimal context.semantics.value),
     ("appResource", decimal context.app.resource),
     ("appGeneration", signed context.app.generation),
     ("sessionResource", decimal context.session.resource),
     ("sessionGeneration", signed context.session.generation),
     ("participantSubject", decimal context.session.subject.value),
     ("ticketResource", decimal context.ticketResource),
     ("ticketRoot", decimal context.ticketRoot.value),
     ("parentTask", decimal context.parentTask),
     ("parentGeneration", signed context.parentGeneration),
     ("purseTask", decimal context.purseTask),
     ("purseGeneration", signed context.purseGeneration),
     ("payerSubject", decimal context.payerSubject.value),
     ("reserveAmount", signed context.reserveAmount),
     ("maximumCharge", signed context.maximumCharge),
     ("reserveOperationId", decimal context.reserveOperationId),
     ("httpOperationId", decimal context.httpOperationId),
     ("requestDigest", decimal context.requestDigest.value)]

private def fixedJson (request : Request) : Json :=
  let fixed := request.fixedSelectors
  .mkObj
    [("issueIndex", decimal fixed.issueIndex),
     ("ticketResource", decimal fixed.ticketResource),
     ("packageManifest", decimal fixed.packageManifest),
     ("snapshotManifest", decimal fixed.snapshotManifest),
     ("sessionObserve", decimal fixed.sessionObserve.value),
     ("manifestObserve", decimal fixed.manifestObserve.value),
     ("enrollmentObserve", decimal fixed.enrollmentObserve.value),
     ("parentTask", decimal fixed.parentTask),
     ("parentCapability", decimal fixed.parentCapability.value),
     ("parentObserve", decimal fixed.parentObserve.value),
     ("purseTask", decimal fixed.purseTask),
     ("purseCapability", decimal fixed.purseCapability.value),
     ("purseObserve", decimal fixed.purseObserve.value),
     ("payerSubject", decimal fixed.payerSubject.value),
     ("reserveAmount", signed fixed.reserveAmount),
     ("maximumCharge", signed fixed.maximumCharge)]

def inspectReservePlan (bytes : List UInt8) : Except String Json := do
  let some plan := reservePlanCodec.decode bytes
    | throw "noncanonical agent reserve plan"
  pure <| .mkObj
    [("type", "application-agent-reserve-plan-v2"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode plan.request),
     ("fixedSelectors", fixedJson plan.request),
     ("context", contextJson plan.context),
     ("canonicalHttpHex", hex <|
       ApplicationDispatchCodec.requestStream.encode plan.request.base.base.http),
     ("invocationWorldRoot", decimal plan.invocation.worldRoot.value),
     ("invocationHeight", decimal plan.invocation.height),
     ("slots", .arr <| plan.invocation.slots.toArray.map slotJson)]

def inspectPaidPlan (bytes : List UInt8) : Except String Json := do
  let some plan := paidPlanCodec.decode bytes
    | throw "noncanonical agent paid dispatch plan"
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode
      plan.app.unsignedIngress
    | throw "noncanonical app plan within paid dispatch"
  let dispatch := unsigned.dispatch.dispatch
  pure <| .mkObj
    [("type", "application-agent-paid-dispatch-plan-v2"),
     ("canonicalPlanHex", hex bytes),
     ("compactSelectorRequestHex", hex <| paidRequestCodec.encode plan.request),
     ("fixedSelectors", fixedJson plan.request.fixed),
     ("context", contextJson plan.request.context),
     ("reserveIndex", decimal plan.request.reserveIndex),
     ("canonicalHttpHex", hex <| ApplicationDispatchCodec.requestStream.encode
       dispatch.request),
     ("unsignedAppIngressHex", hex plan.app.unsignedIngress),
     ("appWorldRoot", decimal plan.app.invocation.worldRoot.value),
     ("payerWorldRoot", decimal plan.payer.worldRoot.value),
     ("appSlots", .arr <|
       (plan.app.invocation.slots ++ plan.app.observationSlots).toArray.map slotJson),
     ("payerSlots", .arr <| plan.payer.slots.toArray.map slotJson)]

end Minidregg.Host.ApplicationDispatchAgentPaidInspection
