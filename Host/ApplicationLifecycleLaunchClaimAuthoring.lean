/-
Operator-private current-image signing plan for a launch-bound v3 claim.
The requested index names a BEGIN-v3 in the same verified replay history.
The request never supplies an app state, resource root, grant, or header.
-/
import Host.ApplicationLifecycleClaimOperator
import Kernel.ApplicationLifecycleClaimV3Core

namespace Minidregg.Host.ApplicationLifecycleLaunchClaimAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

abbrev Pin := ApplicationLifecycleClaimOperator.Pin

structure Request where
  originalIndex : Nat
  queryNonce : Nat
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun request => (request.originalIndex, request.queryNonce))
    (fun (originalIndex, queryNonce) => ⟨originalIndex, queryNonce⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-CLAIM-OPERATOR-REQUEST/v1".toUTF8.toList requestStream

structure Plan where
  sourceBytes : List UInt8
  originalBeginBytes : List UInt8
  originalBeginReceipt : NativeHostCodec.Receipt
  invocation : SigningPlan
  appObservationSlot : SigningSlot
  packageObservationSlot : SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream
      (StreamCodec.product NativeHostCodec.receiptStream
        (StreamCodec.product signingPlanStream
          (StreamCodec.product signingSlotStream signingSlotStream)))))
    (fun plan => (plan.sourceBytes, plan.originalBeginBytes,
      plan.originalBeginReceipt, plan.invocation, plan.appObservationSlot,
      plan.packageObservationSlot))
    (fun (sourceBytes, originalBeginBytes, originalBeginReceipt, invocation,
          appObservationSlot, packageObservationSlot) =>
      ⟨sourceBytes, originalBeginBytes, originalBeginReceipt, invocation, appObservationSlot,
        packageObservationSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-CLAIM-OPERATOR-PLAN/v1".toUTF8.toList planStream

private def cellAt (config : Config) (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical claim signing header"
  unless header.keyId == pin.managementKeyId do
    throw "claim signer differs from operator key pin"

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  let some prior := verified.beginsV3.find? (fun begin => begin.index == request.originalIndex)
    | throw "original launch-bound BEGIN absent from verified history"
  let begin := prior.ingress
  let beginSource := begin.base.source
  unless beginSource.app == pin.app &&
      beginSource.packageManifest == pin.packageManifest &&
      beginSource.subject.value == pin.managementSubject &&
      beginSource.managementSubject.value == pin.managementSubject &&
      beginSource.capability == pin.appCapability do
    throw "historical BEGIN differs from fixed claim operator pin"
  unless begin.shape && ApplicationLifecycleResidentProfile.beginMatchesV3 begin do
    throw "historical BEGIN is outside resident host profile"
  let opened := verified.opened
  let some retained := opened.durable.image.accepted[prior.index]?
    | throw "original BEGIN record absent from verified tip"
  unless DurableReceiverCodec.intentStream.encode retained ==
      DurableReceiverCodec.intentStream.encode prior.record do
    throw "original BEGIN record differs from verified history"
  let some originalReceipt := verified.receipts[prior.index]?
    | throw "original BEGIN receipt absent from verified chronology"
  unless originalReceipt.transactionId == prior.record.transactionId &&
      originalReceipt.eventId == prior.record.event.eventId &&
      originalReceipt.acceptedCount == prior.index + 1 do
    throw "original BEGIN receipt differs from verified record/index"
  let some appCell := cellAt config opened pin.app
    | throw "current claim app cell unavailable"
  let some packageCell := cellAt config opened pin.packageManifest
    | throw "current claim package cell unavailable"
  unless packageCell.kind == .content do
    throw "current claim package is not a content resource"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current claim app state unavailable"
  let source : ApplicationLifecycleClaim.Source :=
    { begin := begin.base
      originalIndex := prior.index
      before := before
      currentAuthorityRoot := opened.authority.snapshot.cell.root
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      currentWorldRoot := opened.durable.worldRoot
      appObserveCapability := pin.appObserveCapability
      packageObserveCapability := pin.packageObserveCapability
      queryNonce := request.queryNonce }
  unless source.valid do throw "current app is not at original pending BEGIN state"
  let command := ApplicationLifecycleClaim.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient opened.durable command
    | throw "current claim command preparation refused"
  unless ApplicationLifecycleClaimCurrent.linkedCurrentPolicy config.deployment
      config.profile ambient opened.durable source prepared do
    throw "current claim app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current claim physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let appWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient opened.durable source prepared pin.app
    pin.appObserveCapability source.currentAppRoot
  let .ok appSelected := ResourceObservationAdmission.prepare context config.profile
      appWanted marker pin.appObserveCapability source.canonicalBytes
    | throw "current claim app observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode appSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode appCell do
    throw "claim app observation differs from current image"
  let packageWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient opened.durable source prepared pin.packageManifest
    pin.packageObserveCapability source.currentPackageRoot
  let .ok packageSelected := ResourceObservationAdmission.prepare context config.profile
      packageWanted marker pin.packageObserveCapability source.canonicalBytes
    | throw "current claim package observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode packageSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode packageCell do
    throw "claim package observation differs from current image"
  unless ApplicationLifecycleBeginV3Admission.installedExact config.deployment begin
      packageSelected.observed.before do
    throw "current installed package differs from original signed descriptor"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | throw "current claim invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "claim invocation plan differs from source"
  let .ok appHeader := CredentialSignatureAdmission.signingHeader
      prepared.authority.snapshot marker (⟨.object, appWanted⟩ : PackedEffectRequest)
    | throw "current claim app observation signing key unavailable"
  let .ok packageHeader := CredentialSignatureAdmission.signingHeader
      prepared.authority.snapshot marker (⟨.object, packageWanted⟩ : PackedEffectRequest)
    | throw "current claim package observation signing key unavailable"
  let appSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode appHeader⟩
  let packageSlot : SigningSlot :=
    ⟨10, 0, CredentialSignedEnvelopeController.headerCodec.encode packageHeader⟩
  for slot in invocation.slots do fixedHeader pin slot
  fixedHeader pin appSlot
  fixedHeader pin packageSlot
  return ⟨source.canonicalBytes, begin.canonicalBytes, originalReceipt, invocation,
    appSlot, packageSlot⟩

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical claim operator request"
  prepareVerified config verified pin request

private def envelope (slot : SigningSlot) (signature : List UInt8) :
    Except String (List UInt8) := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical claim observation header"
  unless signature.length == 64 do
    throw "claim observation signature must be 64 bytes"
  return CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩

/-- Detached assembly does not mint current authority. Op26 refreshes the
verified tip and admits the exact three signed incidences again. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 2 do
    throw "claim signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "claim plan is not an invocation"
  let some source := ApplicationLifecycleClaim.codec.decode plan.sourceBytes
    | throw "noncanonical claim plan source"
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode plan.originalBeginBytes
    | throw "noncanonical original launch-bound BEGIN"
  unless source.valid && source.begin == begin.base && begin.shape &&
      plan.invocation.domain == begin.base.domain &&
      plan.invocation.semantics == begin.base.semantics &&
      plan.originalBeginReceipt.transactionId == begin.base.transactionId &&
      plan.originalBeginReceipt.eventId ==
        (ApplicationLifecycleBeginV3Ingress.event begin).eventId &&
      plan.originalBeginReceipt.acceptedCount == source.originalIndex + 1 &&
      ApplicationLifecycleResidentProfile.beginMatchesV3 begin &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (ApplicationLifecycleClaim.command plan.invocation.domain
            plan.invocation.semantics source)) do
    throw "claim plan differs from original BEGIN or source-derived command"
  let some appSignature := signatures[invocationCount]?
    | throw "missing claim app observation signature"
  let some packageSignature := signatures[invocationCount + 1]?
    | throw "missing claim package observation signature"
  let appEnvelope ← envelope plan.appObservationSlot appSignature
  let packageEnvelope ← envelope plan.packageObservationSlot packageSignature
  let base : ApplicationLifecycleClaimIngress.Ingress :=
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      appObservationEnvelope := appEnvelope
      packageObservationEnvelope := packageEnvelope }
  return ApplicationLifecycleClaimV3Ingress.codec.encode
    { base := base, originalBegin := begin }

end Minidregg.Host.ApplicationLifecycleLaunchClaimAuthoring
