/-
Read-only custody view of the exact event27 request and detached signing plan.
This projection is not a grant receipt or a permission to dispatch an agent.
-/
import Host.ApplicationAgentLifetimeGrantAuthoring
import Kernel.ApplicationAgentLifetimeGrantLookup
import Kernel.ApplicationAgentLifetimeDispatchReserveContext
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
         ("validUntil", decimal header.validUntil),
         ("footprintHex", hex header.footprint),
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
        ("worldRoot", decimal grant.source.issueReceipt.worldRoot.value)]),
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
     ("birthBoundary", decimal plan.birth.worldRoot.value),
     ("birthHeight", decimal plan.birth.height),
     ("finalizedDraftHex", hex <|
       NativeHostCodec.draftStream.encode plan.birth.finalizedDraft),
     ("birthSlots", .arr <| plan.birth.slots.toArray.map slotJson),
     ("appSlot", slotJson plan.appSlot)]

/-- Historical route provenance comes from the verifier-selected event27,
not a proposed grant plan. This does not authorize a current dispatch. -/
private def inspectAcceptedVerified {config : NativeHost.Config}
    {target : NativeHost.Durable} (verified : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : Except String Json := do
  let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes
    | throw "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    throw "noncanonical agent lifetime grant ingress"
  match ApplicationAgentLifetimeGrantReceiver.lookupVerified verified ingress with
  | none => throw "exact agent lifetime grant has not been accepted"
  | some (.error detail) => throw detail
  | some (.ok original) =>
      let grant := original.ingress.spec.grant
      let receiptJson (receipt : NativeHostCodec.Receipt) := Json.mkObj
        [("acceptedCount", decimal receipt.acceptedCount),
         ("transactionId", decimal receipt.transactionId.value),
         ("eventId", decimal receipt.eventId.value),
         ("worldRoot", decimal receipt.worldRoot.value)]
      pure <| .mkObj
        [("type", "application-agent-lifetime-grant-accepted-v1"),
         ("canonicalIngressHex", hex original.ingress.canonicalBytes),
         ("grantIssueIndex", decimal original.index),
         ("grantIssueReceipt", receiptJson original.receipt),
         ("grantInitializedRoot", decimal original.finalRoot.value),
         ("grantDigest", decimal
           (ApplicationAgentLifetimeDispatchReserveContext.grantDigest grant).value),
         ("grantResource", decimal grant.source.resource),
         ("originalEvent22Index", decimal grant.source.issueIndex),
         ("originalEvent22Receipt", receiptJson grant.source.issueReceipt),
         ("originalDescriptorHex", hex <|
           (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode
             original.ticket.evidence.descriptor),
         ("ticketResource", decimal grant.source.ticketResource),
         ("ticketDigest", decimal grant.source.ticketDigest.value),
         ("app", decimal grant.participant.app),
         ("session", decimal grant.participant.session),
         ("subject", decimal grant.participant.subject.value),
         ("parentTask", decimal grant.participant.parentTask),
         ("originalGeneration", .str (toString grant.participant.originalGeneration)),
         ("grantObserveCapability", decimal grant.participant.grantObserveCapability.value)]

def inspectAcceptedCurrent (config : NativeHost.Config) (bytes : List UInt8) :
    IO (Except String Json) := do
  -- Reject malformed input before opening and replaying a potentially large
  -- history. The verified lookup below still selects the accepted original.
  let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes
    | return .error "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .error "noncanonical agent lifetime grant ingress"
  match ← NativeHost.openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      match ← NativeHostReplay.verifyLoaded config opened.durable with
      | .error _ => return .error "agent lifetime grant history unverified"
      | .ok verified => return inspectAcceptedVerified verified bytes

end Minidregg.Host.ApplicationAgentLifetimeGrantInspection
