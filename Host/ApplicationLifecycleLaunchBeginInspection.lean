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
  let some descriptor := ApplicationSpkLaunchDescriptor.codec.decode
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  match request.kind, request.createIndex with
  | .install, none => pure ()
  | .start, some index =>
      unless (descriptor.selectedCreate index).isSome do
        throw "selected create action absent from descriptor"
  | _, _ => throw "request is not INSTALL or first-create START"
  pure <| .mkObj
    [("request", requestJson request),
     ("descriptorRoot", decimal descriptor.root.value),
     ("descriptorCanonicalHex", hex descriptor.canonicalBytes)]

def inspectContinueRequest (bytes : List UInt8) : Except String Json := do
  let some request := continueRequestCodec.decode bytes
    | throw "noncanonical launch continue request"
  let some descriptor := ApplicationSpkLaunchDescriptor.codec.decode
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
    | .install, none =>
        let request : Request :=
          { kind := .install
            clientOperationId := ingress.clientOperationId
            descriptorBytes := ingress.descriptor.canonicalBytes
            createIndex := none }
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
    | _, _ => throw "plan is not INSTALL or START"
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

end Minidregg.Host.ApplicationLifecycleLaunchBeginInspection
