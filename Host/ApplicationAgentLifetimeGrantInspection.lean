/-
Read-only custody view of the exact event27 request and detached signing plan.
This projection is not a grant receipt or a permission to dispatch an agent.
-/
import Host.ApplicationAgentLifetimeGrantAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationAgentLifetimeGrantInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationAgentLifetimeGrantAuthoring

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
         ("codecVersion", decimal header.codecVersion),
         ("algorithm", decimal header.algorithm),
         ("keyId", decimal header.keyId),
         ("keyEpoch", decimal header.keyEpoch),
         ("authorityRoot", decimal header.authorityRoot.value),
         ("registryCommitment", decimal header.registryCommitment.value),
         ("domainHex", hex header.domain),
         ("messageHex", hex header.message),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signing)]

private def requestJson (request : Request) : Json :=
  let grant := request.spec.grant
  .mkObj
    [("type", "application-agent-lifetime-grant-request-v1"),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("canonicalSpecHex", hex <|
       ApplicationAgentLifetimeGrantSource.specCodec.encode request.spec),
     ("originalEvent22Index", decimal grant.source.issueIndex),
     ("originalEvent22Receipt", .mkObj
       [("acceptedCount", decimal grant.source.issueReceipt.acceptedCount),
        ("transactionId", decimal grant.source.issueReceipt.transactionId.value),
        ("eventId", decimal grant.source.issueReceipt.eventId.value),
        ("imageBoundary", decimal grant.source.issueReceipt.imageBoundary.value)]),
     ("ticketResource", decimal grant.source.ticketResource),
     ("ticketDigest", decimal grant.source.ticketDigest.value),
     ("grantResource", decimal grant.source.resource),
     ("app", decimal grant.participant.app),
     ("session", decimal grant.participant.session),
     ("issuer", decimal grant.approval.issuer.value),
     ("payer", decimal request.payer),
     ("funding", .arr <| request.funding.toArray.map fun item => .mkObj
       [("source", decimal item.source),
        ("destination", decimal item.destination),
        ("asset", decimal item.asset),
        ("amount", decimal item.amount)]),
     ("sourceCapabilities", .arr <| request.sourceCapabilities.toArray.map
       (fun cap => decimal cap.value))]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical agent lifetime grant request"
  unless requestCodec.encode request == bytes do
    throw "noncanonical agent lifetime grant request"
  pure (requestJson request)

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical agent lifetime grant plan"
  unless planCodec.encode plan == bytes do
    throw "noncanonical agent lifetime grant plan"
  unless plan.birth.slots.all (fun slot =>
      (CredentialSignedEnvelopeController.headerCodec.decode slot.header).isSome) &&
      (CredentialSignedEnvelopeController.headerCodec.decode plan.appSlot.header).isSome do
    throw "agent lifetime grant plan has an invalid signing header"
  pure <| .mkObj
    [("type", "application-agent-lifetime-grant-plan-v1"),
     ("canonicalPlanHex", hex bytes),
     ("request", requestJson plan.request),
     ("birthDomain", decimal plan.birth.domain.value),
     ("birthSemantics", decimal plan.birth.semantics.value),
     ("birthBoundary", decimal plan.birth.imageBoundary.value),
     ("birthHeight", decimal plan.birth.height),
     ("finalizedDraftHex", hex <|
       NativeHostCodec.draftStream.encode plan.birth.finalizedDraft),
     ("birthSlots", .arr <| plan.birth.slots.toArray.map slotJson),
     ("appSlot", slotJson plan.appSlot)]

end Minidregg.Host.ApplicationAgentLifetimeGrantInspection
