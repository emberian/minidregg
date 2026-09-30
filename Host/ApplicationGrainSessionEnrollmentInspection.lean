/- Read-only canonical presentation of event28 custody bytes. This is not admission. -/
import Host.ApplicationGrainSessionEnrollmentAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationGrainSessionEnrollmentInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource
open Minidregg.Host.ApplicationGrainSessionEnrollmentAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def receiptJson (receipt : Receipt) : Json :=
  .mkObj [("transactionId", decimal receipt.transactionId.value),
    ("eventId", decimal receipt.eventId.value),
    ("acceptedCount", decimal receipt.acceptedCount),
    ("worldRoot", decimal receipt.worldRoot.value)]

private def basisJson : RoleBasis → Json
  | .none => .mkObj [("type", "none")]
  | .allAccess => .mkObj [("type", "allAccess")]
  | .role id => .mkObj [("type", "role"), ("id", decimal id)]

private def roleJson (role : RoleAssignment) : Json :=
  .mkObj [("basis", basisJson role.basis),
    ("addedHex", .arr <| role.added.toArray.map hex),
    ("removedHex", .arr <| role.removed.toArray.map hex),
    ("roleSchemaRoot", decimal role.roleSchemaRoot.value),
    ("roleVersion", decimal role.roleVersion)]

private def requestJson (request : Request) : Json :=
  .mkObj [("type", "application-session-enrollment-request-v1"),
    ("canonicalRequestHex", hex <| requestCodec.encode request),
    ("issueIndex", decimal request.issueIndex),
    ("ticketResource", decimal request.ticketResource),
    ("packageManifest", decimal request.packageManifest),
    ("role", roleJson request.role),
    ("descriptorCapability", decimal request.descriptorCapability.value),
    ("sessionObserveCapability", decimal request.sessionObserveCapability.value),
    ("descriptorObserveCapability", decimal request.descriptorObserveCapability.value),
    ("manifestObserveCapability", decimal request.manifestObserveCapability.value),
    ("nonce", decimal request.nonce)]

private def slotJson (slot : SigningSlot) : Except String Json := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical enrollment signing header"
  pure <| .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header),
    ("signing", .mkObj [("decoded", .bool true),
      ("codecVersion", decimal header.codecVersion),
      ("algorithm", decimal header.algorithm),
      ("keyId", decimal header.keyId), ("keyEpoch", decimal header.keyEpoch),
      ("validUntil", decimal header.validUntil),
      ("domainHex", hex header.domain), ("messageHex", hex header.message),
      ("nullifier", decimal header.nullifier)])]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical enrollment request"
  unless requestCodec.encode request == bytes do
    throw "noncanonical enrollment request"
  pure (requestJson request)

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical enrollment plan"
  unless planCodec.encode plan == bytes do
    throw "noncanonical enrollment plan"
  unless plan.observationSlots.length == 3 do
    throw "enrollment plan observation slot count differs"
  let slots ← (plan.invocation.slots ++ plan.observationSlots).mapM slotJson
  pure <| .mkObj [("type", "application-session-enrollment-plan-v1"),
    ("canonicalPlanHex", hex bytes),
    ("canonicalRequestHex", hex <| requestCodec.encode plan.request),
    ("request", requestJson plan.request),
    ("enrollmentHex", hex <| enrollmentCodec.encode plan.enrollment),
    ("issueReceiptHex", hex <| receiptStream.encode plan.issueReceipt),
    ("issueReceipt", receiptJson plan.issueReceipt),
    ("appRoot", decimal plan.appRoot.value),
    ("manifestRoot", decimal plan.manifestRoot.value),
    ("ticketRoot", decimal plan.ticketRoot.value),
    ("previousAtomHex", match plan.previous with
      | none => Json.null
      | some atom => hex <| HyperdocumentCodec.atomRecordStream.encode atom),
    ("invocationDomain", decimal plan.invocation.domain.value),
    ("invocationSemantics", decimal plan.invocation.semantics.value),
    ("invocationBoundary", decimal plan.invocation.worldRoot.value),
    ("invocationHeight", decimal plan.invocation.height),
    ("slots", .arr slots.toArray)]

def inspectIngress (bytes : List UInt8) : Except String Json := do
  let some ingress := ingressCodec.decode bytes
    | throw "noncanonical enrollment ingress"
  unless ingressCodec.encode ingress == bytes do
    throw "noncanonical enrollment ingress"
  pure <| .mkObj [("type", "application-session-enrollment-ingress-v1"),
    ("canonicalIngressHex", hex bytes),
    ("canonicalRequestHex", hex <| requestCodec.encode ingress.request),
    ("request", requestJson ingress.request),
    ("enrollmentHex", hex <| enrollmentCodec.encode ingress.enrollment),
    ("issueReceiptHex", hex <| receiptStream.encode ingress.issueReceipt),
    ("issueReceipt", receiptJson ingress.issueReceipt),
    ("appRoot", decimal ingress.appRoot.value),
    ("manifestRoot", decimal ingress.manifestRoot.value),
    ("ticketRoot", decimal ingress.ticketRoot.value),
    ("signedBytesHex", hex ingress.signedBytes),
    ("appObservationEnvelopeHex", hex ingress.appObservationEnvelope),
    ("manifestObservationEnvelopeHex", hex ingress.manifestObservationEnvelope),
    ("ticketObservationEnvelopeHex", hex ingress.ticketObservationEnvelope)]

end Minidregg.Host.ApplicationGrainSessionEnrollmentInspection
