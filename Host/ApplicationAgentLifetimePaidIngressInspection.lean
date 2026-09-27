/-
Read-only structural join of an exact op78 paid plan and assembled event26
ingress. Signatures are recovered only from canonical source envelopes and
reassembled through the original Lean authoring codec. This does not verify
signatures, recheck current law, admit event26, or mint a physical permit.
-/
import Host.ApplicationAgentLifetimeDispatchPaidInspection
import Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationAgentLifetimePaidIngressInspection

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

private def receiptJson (receipt : NativeHostCodec.Receipt) : Json := .mkObj
  [("transactionId", decimal receipt.transactionId.value),
   ("eventId", decimal receipt.eventId.value),
   ("acceptedCount", decimal receipt.acceptedCount),
   ("imageBoundary", decimal receipt.imageBoundary.value)]

private def envelopeSignature
    (slot : SigningSlot) (bytes : List UInt8) : Except String (List UInt8) := do
  let some envelope := CredentialSignedEnvelopeController.envelopeCodec.decode bytes
    | throw "noncanonical lifetime paid signature envelope"
  unless CredentialSignedEnvelopeController.envelopeCodec.encode envelope == bytes &&
      CredentialSignedEnvelopeController.headerCodec.encode envelope.header == slot.header &&
      envelope.signature.length == 64 do
    throw "lifetime paid signature envelope differs from source plan slot"
  pure envelope.signature

private def signatures
    (slots : List SigningSlot) (envelopes : List (List UInt8)) :
    Except String (List (List UInt8)) := do
  unless slots.length == envelopes.length do
    throw "lifetime paid signature envelope count differs from source plan"
  (slots.zip envelopes).mapM fun (slot, bytes) => envelopeSignature slot bytes

private def invocationEnvelopes
    (signedCommand : DeclaredResourceController.SignedCommand) : List (List UInt8) :=
  signedCommand.targetEnvelopes ++ signedCommand.observeEnvelopes ++
    [signedCommand.authorityEnvelope]

/-- A strict paired presentation of the exact retained plan and ingress. The
reassembly equality rejects even canonical ingress bytes that were assembled
from another plan. It says nothing about signature validity or live admission. -/
def inspect (planBytes ingressBytes : List UInt8) : Except String Json := do
  let some plan := paidPlanCodec.decode planBytes
    | throw "noncanonical lifetime paid plan"
  unless paidPlanCodec.encode plan == planBytes do
    throw "lifetime paid plan bytes are not canonical"
  let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode ingressBytes
    | throw "noncanonical lifetime paid ingress"
  unless ApplicationAgentLifetimeDispatchIngress.codec.encode ingress == ingressBytes do
    throw "lifetime paid ingress bytes are not canonical"
  let dispatch := ingress.dispatch.dispatch
  let appEnvelopes := invocationEnvelopes dispatch.signed ++
    [dispatch.appObservationEnvelope, dispatch.manifestObservationEnvelope,
     dispatch.enrollmentObservationEnvelope,
     ingress.dispatch.ticketObservationEnvelope]
  let appSignatures ← signatures
    (plan.app.invocation.slots ++ plan.app.observationSlots) appEnvelopes
  let grantSignature ← envelopeSignature plan.grantObservationSlot
    ingress.grantObservationEnvelope
  let payerSignatures ← signatures plan.payer.slots
    (invocationEnvelopes ingress.payerSigned)
  let reconstructed ← assemblePaid plan appSignatures grantSignature payerSignatures
  unless reconstructed == ingressBytes do
    throw "lifetime paid ingress differs from exact retained plan assembly"
  let inspectedPlan ←
    ApplicationAgentLifetimeDispatchPaidInspection.inspectPaidPlan planBytes
  let context ← inspectedPlan.getObjVal? "context"
  let bindings ← inspectedPlan.getObjVal? "bindings"
  let fixedSelectors ← inspectedPlan.getObjVal? "fixedSelectors"
  let canonicalHttpHex ← inspectedPlan.getObjVal? "canonicalHttpHex"
  let http ← inspectedPlan.getObjVal? "http"
  let appSlots ← inspectedPlan.getObjVal? "appSlots"
  let grantSlot ← inspectedPlan.getObjVal? "grantObservationSlot"
  let payerSlots ← inspectedPlan.getObjVal? "payerSlots"
  let base := ingress.reserveContext.base
  let session := base.session
  pure <| .mkObj
    [("type", "application-agent-lifetime-paid-ingress-inspection-v3"),
     ("authority", "structural-only-not-fresh-admission"),
     ("canonicalPlanHex", hex planBytes),
     ("canonicalIngressHex", hex ingressBytes),
     ("reserveContextHex", hex ingress.reserveContext.canonicalBytes),
     ("reserveIndex", decimal ingress.reserveIndex),
     ("reserveReceipt", receiptJson plan.reserveReceipt),
     ("context", context),
     ("bindings", bindings),
     ("fixedSelectors", fixedSelectors),
     ("canonicalHttpHex", canonicalHttpHex),
     ("http", http),
     ("app", .mkObj
       [("resource", decimal base.app.resource),
        ("generation", signed base.app.generation)]),
     ("session", .mkObj
       [("resource", decimal session.resource),
        ("generation", signed session.generation),
        ("originalOrigin", match session.origin with
          | .human => .mkObj [("type", "human")]
          | .agent task generation => .mkObj
              [("type", "agent"), ("task", decimal task),
               ("generation", signed generation)])]),
     ("grantRoot", decimal ingress.grantRoot.value),
     ("grantObserveCapability", decimal ingress.grantObserveCapability.value),
     ("payerCapability", decimal ingress.payerCapability.value),
     ("payerObserve", decimal ingress.payerObserve.value),
     ("payerSignedHex", hex <| signedInvocationStream.encode ingress.payerSigned),
     ("appSlots", appSlots),
     ("grantObservationSlot", grantSlot),
     ("payerSlots", payerSlots)]

end Minidregg.Host.ApplicationAgentLifetimePaidIngressInspection
