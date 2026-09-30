/-
Read-only operator custody projection for a source-authored event-22
grain-backed share request and detached signing plan. Neither JSON nor a
decoded signing header is native admission or signer authority.
-/
import Kernel.ApplicationShareIssueGrainAuthoring
import Kernel.ApplicationAgentLifetimeGrant
import Lean.Data.Json

namespace Minidregg.Host.ApplicationShareIssueGrainInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationShareIssueGrainAuthoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def selectorJson (selector : GrainSelector) : Json := .mkObj
  [("task", decimal selector.task),
   ("capability", decimal selector.capability.value),
   ("observeCapability", decimal selector.observeCapability.value)]

private def ticketJson (ticket : ApplicationDispatchAuthority.Ticket) : Json :=
  let scope := ticket.scope
  let participant := ticket.participant
  let origin := match participant.origin with
    | .human => Json.mkObj [("type", "human")]
    | .agent task generation => Json.mkObj
        [("type", "agent"), ("task", decimal task),
         ("generation", signed generation)]
  .mkObj
    [("canonicalTicket", hex <| ApplicationDispatchAuthority.ticketCodec.encode ticket),
     ("ticketDigest", decimal (ApplicationAgentLifetimeGrant.ticketDigest ticket).value),
     ("resource", decimal ticket.resource),
     ("issueNonce", decimal ticket.issueNonce),
     ("scope", .mkObj
       [("app", decimal scope.app),
        ("packageVersion", signed scope.packageVersion),
        ("packageRoot", decimal scope.packageRoot.value),
        ("interfaceId", decimal scope.interfaceId),
        ("interfaceVersion", decimal scope.interfaceVersion),
        ("interfaceRoot", decimal scope.interfaceRoot.value),
        ("schemaRoot", decimal scope.schemaRoot.value),
        ("schemaVersion", decimal scope.schemaVersion)]),
     ("participant", .mkObj
       [("session", decimal participant.session),
        ("descriptorResource", decimal participant.descriptorResource),
        ("kind", match participant.kind with | .web => "web" | .api => "api"),
        ("subject", decimal participant.subject.value),
        ("origin", origin),
        ("sessionCapability", decimal participant.sessionCapability.value),
        ("appObserveCapability", decimal participant.appObserveCapability.value),
        ("ticketObserveCapability", decimal participant.ticketObserveCapability.value)]),
     ("ceilingCanonical", hex <|
       ApplicationGrainSessionEnrollment.roleAssignmentStream.encode ticket.ceiling)]

private def requestJson (request : Request) : Json :=
  let spec := request.spec
  .mkObj
    [("type", "application-grain-share-issue-request-v1"),
     ("canonicalRequest", hex <| requestCodec.encode request),
     ("canonicalSpec", hex <| ApplicationShareIssueSource.specCodec.encode spec),
     ("spec", .mkObj
       [("ticket", ticketJson spec.ticket),
        ("issuer", decimal spec.issuer.value),
        ("appDelegateCapability", decimal spec.appDelegateCapability.value),
        ("ticketOwnerCapability", decimal spec.ticketOwnerCapability.value),
        ("ticketControlCapability", decimal spec.ticketControlCapability.value)]),
     ("payer", decimal request.payer),
     ("funding", .arr <| request.funding.toArray.map fun item => .mkObj
       [("source", decimal item.source),
        ("destination", decimal item.destination),
        ("asset", decimal item.asset),
        ("amount", decimal item.amount)]),
     ("sourceCapabilities", .arr <| request.sourceCapabilities.toArray.map
       (fun cap => decimal cap.value)),
     ("tool", selectorJson request.tool),
     ("parent", selectorJson request.parent)]

private def slotJson (slot : SigningSlot) : Json :=
  let signing := match CredentialSignedEnvelopeController.headerCodec.decode slot.header with
    | none => Json.mkObj [("decoded", .bool false)]
    | some header =>
        let canonical := CredentialSignedEnvelopeController.headerCodec.encode header
        if canonical == slot.header then Json.mkObj
          [("decoded", .bool true),
           ("canonical", hex canonical),
           ("codecVersion", decimal header.codecVersion),
           ("algorithm", decimal header.algorithm),
           ("keyId", decimal header.keyId),
           ("keyEpoch", decimal header.keyEpoch),
           ("validUntil", decimal header.validUntil),
           ("domain", hex header.domain),
           ("message", hex header.message),
           ("nullifier", decimal header.nullifier)]
        else Json.mkObj [("decoded", .bool false)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("header", hex slot.header), ("signing", signing)]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical grain-backed share request"
  pure (requestJson request)

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical grain-backed share plan"
  let .birth finalized capabilities := plan.birth.finalizedDraft
    | throw "grain-backed share plan does not finalize a birth"
  let some draft := GrainResourceBirthHostCodec.finalizedCodec.decode finalized
    | throw "noncanonical finalized grain-backed birth"
  let some source := GrainResourceBirthHostCodec.sourceCodec.decode draft.sourceBytes
    | throw "noncanonical finalized grain-backed source"
  unless capabilities == plan.request.sourceCapabilities do
    throw "finalized grain birth capabilities differ from request"
  let beforeJson := fun (state : AgentGrain.State) => Json.mkObj
    [("generation", signed state.generation),
     ("status", signed state.status),
     ("remaining", signed state.remaining),
     ("reserved", signed state.reserved)]
  pure <| .mkObj
    [("type", "application-grain-share-issue-plan-v1"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequest", hex <| requestCodec.encode plan.request),
     ("request", requestJson plan.request),
     ("domain", decimal plan.birth.domain.value),
     ("semantics", decimal plan.birth.semantics.value),
     ("worldRoot", decimal plan.birth.worldRoot.value),
     ("height", decimal plan.birth.height),
     ("finalizedGrainBirth", .mkObj
       [("source", hex draft.sourceBytes),
        ("command", hex draft.commandBytes),
        ("descriptor", hex <|
          (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode source.birth),
        ("sourceCapabilities", .arr <| capabilities.toArray.map
          (fun cap => decimal cap.value)),
        ("tool", .mkObj
          [("task", decimal source.toolTask),
           ("capability", decimal source.toolCapability.value),
           ("observeCapability", decimal source.toolObserveCapability.value),
           ("root", decimal source.toolRoot.value),
           ("before", beforeJson source.toolBefore)]),
        ("parent", .mkObj
          [("task", decimal source.parentTask),
           ("capability", decimal source.parentCapability.value),
           ("observeCapability", decimal source.parentObserveCapability.value),
           ("root", decimal source.parentRoot.value),
           ("before", beforeJson source.parentBefore)])]),
     ("birthSlots", .arr <| plan.birth.slots.toArray.map slotJson),
     ("appSlot", slotJson plan.appSlot),
     ("slots", .arr <|
       (plan.birth.slots ++ [plan.appSlot]).toArray.map slotJson)]

end Minidregg.Host.ApplicationShareIssueGrainInspection
