/-
Read-only custody presentation of the source-authored v3 launch BEGIN request
and plan. The JSON is not an admission witness. The plan inspection repeats
the exact request and all signing headers so the operator can compare the
selected create action, descriptor and volume before signing.
-/
import Host.ApplicationLifecycleLaunchBeginAuthoring
import Lean.Data.Json

namespace Minidregg.Host.ApplicationLifecycleLaunchBeginInspection

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Host.ApplicationLifecycleLaunchBeginAuthoring

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

private def requestJson (request : Request) : Json := .mkObj
  [("type", "application-lifecycle-launch-begin-request-v1"),
   ("canonicalRequestHex", hex <| requestCodec.encode request),
   ("kind", kindName request.kind),
   ("clientOperationId", decimal request.clientOperationId),
   ("descriptorHex", hex request.descriptorBytes),
   ("createIndex", match request.createIndex with
      | none => Json.null | some index => decimal index)]

private def continueRequestJson (request : ContinueRequest) : Json := .mkObj
  [("type", "application-lifecycle-launch-continue-request-v1"),
   ("canonicalRequestHex", hex <| continueRequestCodec.encode request),
   ("kind", "continue"),
   ("clientOperationId", decimal request.clientOperationId),
   ("descriptorHex", hex request.descriptorBytes),
   ("createdIndex", decimal request.createdIndex)]

/-- STOP and INSTALL share the no-action shape but retain their distinct kind
in the canonical request echoed by plan inspection. -/
def noActionRequest (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) : Request :=
  { kind := ingress.base.source.kind
    clientOperationId := ingress.clientOperationId
    descriptorBytes := ingress.descriptor.canonicalBytes
    createIndex := none }

theorem noActionRequest_kind (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) :
    (noActionRequest ingress).kind = ingress.base.source.kind := rfl

private def slotJson (slot : SigningSlot) : Json :=
  let signing := match CredentialSignedEnvelopeController.headerCodec.decode
      slot.header with
    | none => .mkObj [("decoded", .bool false)]
    | some header => .mkObj
        [("decoded", .bool true),
         ("keyId", decimal header.keyId),
         ("keyEpoch", decimal header.keyEpoch),
         ("algorithm", decimal header.algorithm),
         ("authorityRoot", decimal header.authorityRoot.value),
         ("domainHex", hex header.domain),
         ("messageHex", hex header.message),
         ("nullifier", decimal header.nullifier)]
  .mkObj [("role", decimal slot.role), ("index", decimal slot.index),
    ("headerHex", hex slot.header), ("signing", signing)]

def inspectRequest (bytes : List UInt8) : Except String Json := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch BEGIN request"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  match request.kind, request.createIndex with
  | .install, none | .stop, none => pure ()
  | .start, some index =>
      unless (descriptor.selectedCreate index).isSome do
        throw "selected create action absent from descriptor"
  | _, _ => throw "request is not INSTALL, STOP or first-create START"
  pure <| .mkObj
    [("request", requestJson request),
     ("descriptorRoot", decimal descriptor.root.value),
     ("descriptorCanonicalHex", hex descriptor.canonicalBytes)]

def inspectContinueRequest (bytes : List UInt8) : Except String Json := do
  let some request := continueRequestCodec.decode bytes
    | throw "noncanonical launch continue request"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  pure <| .mkObj
    [("request", continueRequestJson request),
     ("descriptorRoot", decimal descriptor.root.value),
     ("descriptorCanonicalHex", hex descriptor.canonicalBytes)]

def inspectPlan (bytes : List UInt8) : Except String Json := do
  let some plan := planCodec.decode bytes
    | throw "noncanonical launch BEGIN plan"
  let ingress := plan.unsigned
  unless ingress.shape && ingress.withAuthorizationId == ingress do
    throw "launch BEGIN plan authorization shape refused"
  unless ingress.base.signed ==
      (⟨[], [], [], []⟩ : DeclaredResourceController.SignedCommand) &&
      ingress.base.packageObservationEnvelope.isEmpty do
    throw "launch BEGIN plan is not unsigned"
  let (requestProjection, requestBytes) ← match ingress.base.source.kind, ingress.start with
    | .install, none | .stop, none =>
        let request := noActionRequest ingress
        pure (requestJson request, requestCodec.encode request)
    | .start, some binding =>
        match binding.choice, binding.priorCreate with
        | .create index, none =>
            let request : Request :=
              { kind := .start
                clientOperationId := ingress.clientOperationId
                descriptorBytes := ingress.descriptor.canonicalBytes
                createIndex := some index }
            pure (requestJson request, requestCodec.encode request)
        | .continue, some (receipt, _) =>
            unless receipt.acceptedCount > 0 do
              throw "continue receipt has zero accepted count"
            let request : ContinueRequest :=
              { clientOperationId := ingress.clientOperationId
                descriptorBytes := ingress.descriptor.canonicalBytes
                createdIndex := receipt.acceptedCount - 1 }
            pure (continueRequestJson request, continueRequestCodec.encode request)
        | _, _ => throw "launch binding has invalid prior-create shape"
    | _, _ => throw "plan is not INSTALL, STOP or START"
  let source := ingress.base.source
  unless plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (ApplicationLifecycleBegin.command plan.invocation.domain
          plan.invocation.semantics source)) &&
      plan.invocation.domain == ingress.base.domain &&
      plan.invocation.semantics == ingress.base.semantics do
    throw "launch BEGIN plan command differs from v3 authorization"
  pure <| .mkObj
    [("type", "application-lifecycle-launch-begin-plan-v1"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex requestBytes),
     ("request", requestProjection),
     ("unsignedIngressHex", hex ingress.canonicalBytes),
     ("domain", decimal ingress.base.domain.value),
     ("semantics", decimal ingress.base.semantics.value),
     ("app", decimal source.app),
     ("packageManifest", decimal source.packageManifest),
     ("snapshotManifest", decimal source.snapshotManifest),
     ("managementSubject", decimal source.managementSubject.value),
     ("authorizationOperationId", decimal source.operationId),
     ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
       ingress.base.domain source.app),
     ("descriptorRoot", decimal ingress.descriptor.root.value),
     ("packageRoot", decimal ingress.descriptor.root.value),
     ("beforeGeneration", signed source.before.generation),
     ("beforePhase", signed source.before.phase),
     ("processGeneration", signed source.processGeneration),
     ("processIdentityHex", hex source.processIdentity),
     ("imageIdentityHex", hex source.imageIdentity),
     ("imageBoundary", decimal plan.invocation.imageBoundary.value),
     ("height", decimal plan.invocation.height),
     ("selectedCommandDigest", match ingress.start with
       | none => Json.null
       | some binding => decimal binding.commandDigest.value),
     ("priorCreate", match ingress.start with
       | some { priorCreate := some (receipt, custody), .. } => .mkObj
           [("receiptHex", hex <| NativeHostCodec.receiptStream.encode receipt),
            ("custodyHex", hex <|
              ApplicationLifecycleLaunchBinding.custodyStream.encode custody)]
       | _ => Json.null),
     ("slots", .arr <| (plan.invocation.slots ++
       [plan.packageObservationSlot]).toArray.map slotJson)]

/-- STOP inspection echoes the exact verifier-selected prior running event25
receipt and physical incarnation alongside the source-authored v1 base plan.
This is custody presentation, not a caller-supplied historical certificate. -/
def inspectStopPlan (bytes : List UInt8) : Except String Json := do
  let some plan := stopPlanCodec.decode bytes
    | throw "noncanonical launch STOP running-witness plan-v2"
  unless plan.shape do throw "launch STOP running-witness plan shape refused"
  let base ← inspectPlan (planCodec.encode plan.base)
  let source := plan.base.unsigned.base.source
  let request := noActionRequest plan.base.unsigned
  let witness := plan.running
  pure <| .mkObj
    [("type", "application-lifecycle-launch-stop-plan-v2"),
     ("canonicalPlanHex", hex bytes),
     ("canonicalRequestHex", hex <| requestCodec.encode request),
     ("basePlan", base),
     ("app", decimal source.app),
     ("operationGeneration", signed source.processGeneration),
     ("running", .mkObj
       [("index", decimal witness.index),
        ("receiptHex", hex <| NativeHostCodec.receiptStream.encode witness.receipt),
        ("receipt", .mkObj
          [("transactionId", decimal witness.receipt.transactionId.value),
           ("eventId", decimal witness.receipt.eventId.value),
           ("acceptedCount", decimal witness.receipt.acceptedCount),
           ("imageBoundary", decimal witness.receipt.imageBoundary.value)]),
        ("generation", signed witness.generation),
        ("unitHex", hex witness.unit),
        ("imageHex", hex witness.image),
        ("invocationIdHex", hex witness.invocationId),
        ("controlGroupHex", hex witness.controlGroup),
        ("volumeIdHex", hex <| ApplicationLifecycleLaunchBinding.volumeIdBytes
          plan.base.unsigned.base.domain source.app),
        ("custodyHex", hex <|
          ApplicationLifecycleLaunchBinding.custodyStream.encode witness.custody),
        ("physicalWitnessHex", hex witness.custody.physicalWitness)])]

end Minidregg.Host.ApplicationLifecycleLaunchBeginInspection
