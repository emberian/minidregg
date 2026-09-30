/-
Read-only presentation of source-authored event26 signing plans. Decoded JSON
is custody data, not a permit: the native event26 receiver rechecks the
original grant and reserve history and current image before CAS.
-/
import Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationAgentLifetimeDispatchPaidInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def receiptJson (receipt : Receipt) : Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value),
   ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("imageBoundary", decimal receipt.imageBoundary.value)]

private def slotJson (slot : SigningSlot) : Json :=
  let signing := match CredentialSignedEnvelopeController.headerCodec.decode slot.header with
    | none => .mkObj [("decoded", .bool false)]
    | some header => .mkObj
        [("decoded", .bool true), ("keyId", decimal header.keyId),
         ("keyEpoch", decimal header.keyEpoch),
         ("algorithm", decimal header.algorithm),
         ("validUntil", decimal header.validUntil),
         ("messageHex", hex header.message),
         ("domainHex", hex header.domain),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signing)]

private def bindingsJson (bindings : SourceBindings) : Json := .mkObj
  [("originalIssueReceipt", receiptJson bindings.originalIssueReceipt),
   ("grantIssueReceipt", receiptJson bindings.grantIssueReceipt),
   ("grantInitializedRoot", decimal bindings.grantInitializedRoot.value),
   ("grantPhysicalRoot", decimal bindings.grantPhysicalRoot.value),
   ("appPhysicalRoot", decimal bindings.appPhysicalRoot.value),
   ("sessionPhysicalRoot", decimal bindings.sessionPhysicalRoot.value),
   ("parentPhysicalRoot", decimal bindings.parentPhysicalRoot.value),
   ("pursePhysicalRoot", decimal bindings.pursePhysicalRoot.value)]

private def headerJson (header : ApplicationDispatchCodec.Header) : Json := .mkObj
  [("nameHex", hex header.name), ("valueHex", hex header.value),
   ("generated", .bool header.generated)]

private def httpJson (http : ApplicationDispatchCodec.Request) : Json := .mkObj
  [("operationId", decimal http.operationId),
   ("methodHex", hex http.method),
   ("pathHex", hex http.path),
   ("queryHex", hex http.query),
   ("headers", .arr <| http.headers.toArray.map headerJson),
   ("bodyHex", hex http.body)]

private def contextJson
    (context : ApplicationAgentLifetimeDispatchReserveContext.Context) : Json :=
  let base := context.base
  .mkObj
    [("canonicalHex", hex context.canonicalBytes),
     ("reserveNonce", decimal <|
       ApplicationAgentLifetimeDispatchReserveContext.reserveNonce context),
     ("payerNonce", decimal <|
       ApplicationAgentLifetimeDispatchReserveContext.payerNonce context),
     ("domain", decimal base.domain.value),
     ("semantics", decimal base.semantics.value),
     ("appResource", decimal base.app.resource),
     ("appGeneration", signed base.app.generation),
     ("sessionResource", decimal base.session.resource),
     ("sessionGeneration", signed base.session.generation),
     ("sessionOrigin", match base.session.origin with
       | .human => .mkObj [("type", "human")]
       | .agent task generation => .mkObj
           [("type", "agent"), ("task", decimal task),
            ("generation", signed generation)]),
     ("participantSubject", decimal base.session.subject.value),
     ("ticketResource", decimal base.ticketResource),
     ("ticketRoot", decimal base.ticketRoot.value),
     ("grantResource", decimal context.grantResource),
     ("grantIssueIndex", decimal context.grantIssueIndex),
     ("grantDigest", decimal context.grantDigest.value),
     ("parentTask", decimal base.parentTask),
     ("parentGeneration", signed base.parentGeneration),
     ("purseTask", decimal base.purseTask),
     ("purseGeneration", signed base.purseGeneration),
     ("payerSubject", decimal base.payerSubject.value),
     ("reserveAmount", signed base.reserveAmount),
     ("maximumCharge", signed base.maximumCharge),
     ("reserveOperationId", decimal base.reserveOperationId),
     ("httpOperationId", decimal base.httpOperationId),
     ("requestDigest", decimal base.requestDigest.value)]

private def fixedJson (request : Request) : Json :=
  let fixed := request.fixedSelectors
  let old := fixed.legacy
  .mkObj
    [("issueIndex", decimal old.issueIndex),
     ("ticketResource", decimal old.ticketResource),
     ("packageManifest", decimal old.packageManifest),
     ("snapshotManifest", decimal old.snapshotManifest),
     ("sessionObserve", decimal old.sessionObserve.value),
     ("manifestObserve", decimal old.manifestObserve.value),
     ("enrollmentObserve", decimal old.enrollmentObserve.value),
     ("parentTask", decimal old.parentTask),
     ("parentCapability", decimal old.parentCapability.value),
     ("parentObserve", decimal old.parentObserve.value),
     ("purseTask", decimal old.purseTask),
     ("purseCapability", decimal old.purseCapability.value),
     ("purseObserve", decimal old.purseObserve.value),
     ("payerSubject", decimal old.payerSubject.value),
     ("reserveAmount", signed old.reserveAmount),
     ("maximumCharge", signed old.maximumCharge),
     ("grantIssueIndex", decimal fixed.grantIssueIndex),
     ("grantResource", decimal fixed.grantResource),
     ("grantObserveCapability", decimal fixed.grantObserveCapability.value)]

/-- Operator custody projection before any signer receives a header. Full HTTP
bytes are retained here and in the reserve request, never duplicated in a
compact paid selector request. -/
def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical lifetime author request"
  let http := request.fixed.base.base.http
  pure <| .mkObj
    [("type", "application-agent-lifetime-author-request-v3"),
     ("canonicalRequestHex", hex bytes),
     ("fixedSelectors", fixedJson request),
     ("canonicalHttpHex", hex <| ApplicationDispatchCodec.requestStream.encode http),
     ("http", httpJson http),
     ("httpOperationId", decimal http.operationId),
     ("requestDigest", decimal <| (ApplicationDispatchCodec.requestDigest http).value)]

def inspectReservePlan (bytes : List UInt8) : Except String Json := do
  let some plan := reservePlanCodec.decode bytes
    | throw "noncanonical lifetime reserve plan"
  pure <| .mkObj
    [("type", "application-agent-lifetime-reserve-plan-v3"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode plan.request),
     ("fixedSelectors", fixedJson plan.request),
     ("context", contextJson plan.context),
     ("bindings", bindingsJson plan.bindings),
     ("canonicalHttpHex", hex <|
       ApplicationDispatchCodec.requestStream.encode plan.request.fixed.base.base.http),
     ("http", httpJson plan.request.fixed.base.base.http),
     ("invocationImageBoundary", decimal plan.invocation.imageBoundary.value),
     ("invocationHeight", decimal plan.invocation.height),
     ("slots", .arr <| plan.invocation.slots.toArray.map slotJson)]

def inspectPaidPlan (bytes : List UInt8) : Except String Json := do
  let some plan := paidPlanCodec.decode bytes
    | throw "noncanonical lifetime paid plan"
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode
      plan.app.unsignedIngress
    | throw "noncanonical app ingress in lifetime paid plan"
  pure <| .mkObj
    [("type", "application-agent-lifetime-paid-plan-v3"),
     ("canonicalPlanHex", hex bytes),
     ("compactSelectorRequestHex", hex <| paidRequestCodec.encode plan.request),
     ("fixedSelectors", fixedJson plan.request.fixed),
     ("context", contextJson plan.request.context),
     ("bindings", bindingsJson plan.bindings),
     ("reserveIndex", decimal plan.request.reserveIndex),
     ("reserveReceipt", receiptJson plan.reserveReceipt),
     ("canonicalHttpHex", hex <|
       ApplicationDispatchCodec.requestStream.encode unsigned.dispatch.dispatch.request),
     ("http", httpJson unsigned.dispatch.dispatch.request),
     ("unsignedAppIngressHex", hex plan.app.unsignedIngress),
     ("grantRoot", decimal plan.grantRoot.value),
     ("grantObservationSlot", slotJson plan.grantObservationSlot),
     ("appImageBoundary", decimal plan.app.invocation.imageBoundary.value),
     ("payerImageBoundary", decimal plan.payer.imageBoundary.value),
     ("appSlots", .arr <|
       (plan.app.invocation.slots ++ plan.app.observationSlots).toArray.map slotJson),
     ("payerSlots", .arr <| plan.payer.slots.toArray.map slotJson)]

end Minidregg.Host.ApplicationAgentLifetimeDispatchPaidInspection
