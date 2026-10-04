/-
Read-only custody presentation of the source-authored retry BEGIN-v4 request
and plan. The JSON is not an admission witness. The plan inspection repeats
the exact request, the failed-start recovery selector and all signing headers
so the operator can compare the repeated create action, descriptor, volume and
recovery before signing.
-/
import Host.ApplicationLifecycleRetryBeginV4Authoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleRetryBeginV4Inspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleRetryBeginV4Authoring

set_option autoImplicit false

private def decimal (value : Nat) : Json := .str (toString value)
private def signed (value : Int) : Json := .str (toString value)
private def nibble (value : Nat) : Char :=
  "0123456789abcdef".toList[value]?.getD '0'
private def hex (bytes : List UInt8) : Json :=
  .str <| String.ofList <| bytes.flatMap fun byte =>
    [nibble (byte.toNat / 16), nibble (byte.toNat % 16)]

private def kindName : ApplicationLifecycleBegin.Kind → String
  | .install => "install"
  | .start => "start"
  | .stop => "stop"
  | .upgrade => "upgrade"

/-- Selector presentation shared by every retry inspection: the recovery
index and the exact canonical recovery ingress bytes it names. -/
def selectorFields (selector : ApplicationFailedCreateRetryEvidence.Selector) :
    List (String × Json) :=
  [("retryRecoveryIndex", decimal selector.recoveryIndex),
   ("retryRecoveryIngressHex", hex selector.recovery.canonicalBytes),
   ("retrySelectorHex", hex selector.canonicalBytes)]

private def requestJson (request : Request) : Json := .mkObj <|
  ([("type", "application-lifecycle-retry-begin-request-v4"),
   ("canonicalRequestHex", hex <| requestCodec.encode request),
   ("kind", kindName request.launch.kind),
   ("clientOperationId", decimal request.launch.clientOperationId),
   ("descriptorHex", hex request.launch.descriptorBytes),
   ("createIndex", match request.launch.createIndex with
      | none => Json.null | some index => decimal index)] : List (String × Json)) ++
  selectorFields request.retry

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
    | throw "noncanonical retry BEGIN request"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.launch.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  match request.launch.kind, request.launch.createIndex with
  | .start, some index =>
      unless (descriptor.selectedCreate index).isSome do
        throw "selected create action absent from descriptor"
  | _, _ => throw "retry request is not a repeat-CREATE START"
  pure <| .mkObj
    [("request", requestJson request),
     ("descriptorRoot", decimal descriptor.root.value),
     ("descriptorCanonicalHex", hex descriptor.canonicalBytes)]

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical retry BEGIN plan"
  let ingress := plan.unsigned
  let inner := ingress.begin
  unless ingress.shape && ingress.withAuthorizationId == ingress do
    throw "retry BEGIN plan authorization shape refused"
  unless inner.base.signed ==
      (⟨[], [], [], []⟩ : DeclaredResourceController.SignedCommand) &&
      inner.base.packageObservationEnvelope.isEmpty do
    throw "retry BEGIN plan is not unsigned"
  let (binding, createIndex) ← match inner.base.source.kind, inner.start with
    | .start, some binding =>
        match binding.choice, binding.priorCreate with
        | .create index, none => pure (binding, index)
        | _, _ => throw "retry binding is not a first-shape repeat CREATE"
    | _, _ => throw "retry plan is not a START"
  let request : Request :=
    { launch :=
        { kind := .start
          clientOperationId := inner.clientOperationId
          descriptorBytes := inner.descriptor.canonicalBytes
          createIndex := some createIndex }
      retry := ingress.retry }
  let source := inner.base.source
  unless plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (ApplicationLifecycleBegin.command plan.invocation.domain
          plan.invocation.semantics source)) &&
      plan.invocation.domain == inner.base.domain &&
      plan.invocation.semantics == inner.base.semantics do
    throw "retry BEGIN plan command differs from v4 authorization"
  pure <| .mkObj <|
    ([("type", "application-lifecycle-retry-begin-plan-v4"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("request", requestJson request),
     ("unsignedIngressHex", hex ingress.canonicalBytes),
     ("domain", decimal inner.base.domain.value),
     ("semantics", decimal inner.base.semantics.value),
     ("app", decimal source.app),
     ("packageManifest", decimal source.packageManifest),
     ("snapshotManifest", decimal source.snapshotManifest),
     ("managementSubject", decimal source.managementSubject.value),
     ("authorizationOperationId", decimal source.operationId),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       inner.base.domain source.app),
     ("descriptorRoot", decimal inner.descriptor.root.value),
     ("packageRoot", decimal inner.descriptor.root.value),
     ("beforeGeneration", signed source.before.generation),
     ("beforePhase", signed source.before.phase),
     ("processGeneration", signed source.processGeneration),
     ("processIdentityHex", hex source.processIdentity),
     ("imageIdentityHex", hex source.imageIdentity),
     ("worldRoot", decimal plan.invocation.worldRoot.value),
     ("height", decimal plan.invocation.height),
     ("selectedCommandDigest", decimal binding.commandDigest.value),
     ("priorCreate", Json.null),
     ("slots", .arr <| (plan.invocation.slots ++
       [plan.packageObservationSlot]).toArray.map slotJson)] : List (String × Json)) ++
    selectorFields ingress.retry

end Minidregg.Host.ApplicationLifecycleRetryBeginV4Inspection
