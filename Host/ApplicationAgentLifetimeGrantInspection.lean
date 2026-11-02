/-
Read-only custody view of the exact event27 request and detached signing plan.
This projection is not a grant receipt or a permission to dispatch an agent.
-/
module

public import Host.ApplicationAgentLifetimeGrantAuthoring
public import Kernel.ApplicationAgentLifetimeGrantReceiver
public import Kernel.ApplicationAgentLifetimeDispatchReserveContext
public import Lean.Data.Json

@[expose] public section

namespace Minidregg.Host.ApplicationAgentLifetimeGrantInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
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
  pure (requestJson request)

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical agent lifetime grant plan"
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
def inspectAcceptedLight (config : NativeHost.Config)
    (light : NativeHostLight.Light config) (bytes : List UInt8) :
    IO (Except String Json) := do
  let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes
    | return .error "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .error "noncanonical agent lifetime grant ingress"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let tx := ApplicationAgentLifetimeGrantReceiver.transaction config ingress
  match ← reader.byTx tx with
  | .error refusal => return .error refusal.message
  | .ok (.absent _) => return .error "exact agent lifetime grant has not been accepted"
  | .ok (.present found) =>
      if found.height == 0 then
        return .error "agent lifetime grant transaction is not an admitted event27"
      let grantIndex := found.height - 1
      let grantReceipt := NativeHost.receiptOfRecord found.read
      let selected ← match ← NativeHistorySelection.select config reader light.opening.head.height grantIndex
          (ApplicationAgentLifetimeGrantReceiver.keys config ingress) with
        | .error _ => return .error "agent lifetime grant transaction is not an admitted event27"
        | .ok selected => pure selected
      let issueIndex := ingress.spec.grant.source.issueIndex
      let issue ← match ← NativeHostReplay.selectIssue config reader light.opened.pins
          grantIndex issueIndex with
        | .error _ => return .error "agent lifetime grant transaction is not an admitted event27"
        | .ok issue => pure issue
      unless issue.evidence.record.event.codecVersion == 22 &&
          issue.receipt == ingress.spec.grant.source.issueReceipt &&
          ingress.spec.grant.matchesIssued issue.evidence.spec issueIndex issue.receipt do
        return .error "agent lifetime grant transaction is not an admitted event27"
      let ⟨decoded, accepted⟩ ← match ← ApplicationAgentLifetimeGrantAdmission.admitNative
          config.profile config light.opened.pins config.signature selected.ground
          (config.genesisHeight + selected.ground.height)
          (NativeHostReplay.sourceBytes selected.record) with
        | .error _ => return .error "agent lifetime grant transaction is not an admitted event27"
        | .ok admitted => pure admitted
      match NativeHistorySelection.matchIntent selected
          (ApplicationAgentLifetimeGrantIntentTemplate.template accepted) with
      | .error _ => return .error "agent lifetime grant transaction is not an admitted event27"
      | .ok _ =>
          unless decoded.canonicalBytes.toByteArray == ingress.canonicalBytes.toByteArray do
            return .error "agent lifetime grant original ingress differs"
          let grant := decoded.spec.grant
          let finalRoot := (ResourceBirthController.birthWrite accepted.sourceReady.birth.create).exactPost
          let receiptJson (receipt : NativeHostCodec.Receipt) := Json.mkObj
            [("acceptedCount", decimal receipt.acceptedCount),
             ("transactionId", decimal receipt.transactionId.value),
             ("eventId", decimal receipt.eventId.value),
             ("worldRoot", decimal receipt.worldRoot.value)]
          return .ok (.mkObj
            [("type", "application-agent-lifetime-grant-accepted-v1"),
             ("canonicalIngressHex", hex decoded.canonicalBytes),
             ("grantIssueIndex", decimal grantIndex),
             ("grantIssueReceipt", receiptJson grantReceipt),
             ("grantInitializedRoot", decimal finalRoot.value),
             ("grantDigest", decimal
               (ApplicationAgentLifetimeDispatchReserveContext.grantDigest grant).value),
             ("grantResource", decimal grant.source.resource),
             ("originalEvent22Index", decimal grant.source.issueIndex),
             ("originalEvent22Receipt", receiptJson grant.source.issueReceipt),
             ("originalDescriptorHex", hex <|
               (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode
                 issue.evidence.descriptor),
             ("ticketResource", decimal grant.source.ticketResource),
             ("ticketDigest", decimal grant.source.ticketDigest.value),
             ("app", decimal grant.participant.app),
             ("session", decimal grant.participant.session),
             ("subject", decimal grant.participant.subject.value),
             ("parentTask", decimal grant.participant.parentTask),
             ("originalGeneration", .str (toString grant.participant.originalGeneration)),
             ("grantObserveCapability", decimal grant.participant.grantObserveCapability.value)])

def inspectAcceptedCurrent (config : NativeHost.Config) (bytes : List UInt8) :
    IO (Except String Json) := do
  -- Reject malformed input before opening the Store.
  let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes
    | return .error "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .error "noncanonical agent lifetime grant ingress"
  match ← NativeHostLight.start config with
  | .error detail => return .error detail
  | .ok light => inspectAcceptedLight config light bytes

end Minidregg.Host.ApplicationAgentLifetimeGrantInspection
