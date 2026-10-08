/-
Operator-private current-image signing plan for a versioned retry CLAIM.
The requested index names a retry BEGIN-v4 in the same verified replay history.
The request never supplies an app state, resource root, grant, header, or the
recovery selector: the selector is the one retained in the admitted BEGIN-v4.
-/
import Host.ApplicationLifecycleClaimOperator
import Kernel.ApplicationLifecycleRetryClaimV4Core
import Kernel.NativeHostReplay

namespace Minidregg.Host.ApplicationLifecycleRetryClaimV4Authoring

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
  "DREGG/APPLICATION/RETRY-CREATE-CLAIM-OPERATOR-REQUEST/v4".toUTF8.toList requestStream

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
  "DREGG/APPLICATION/RETRY-CREATE-CLAIM-OPERATOR-PLAN/v4".toUTF8.toList planStream

private def cellAt (config : Config) (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical retry claim signing header"
  unless header.keyId == pin.managementKeyId do
    throw "retry claim signer differs from operator key pin"

/-- The plan repeats the v3 claim plan against the admitted retry BEGIN-v4.
`ApplicationLifecycleRetryClaimV4Core.prepare` admits signed envelopes, so it
runs at op26 on the assembled ingress; here only its unsigned gates (the
exact original projection, the installed descriptor and the retry markers)
are checked before any management header escapes. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  let some prior := verified.retry.beginsV4.find?
      (fun begin => begin.index == request.originalIndex)
    | throw "original retry BEGIN-v4 absent from verified history"
  let begin := prior.ingress
  let beginSource := begin.begin.base.source
  unless beginSource.app == pin.app &&
      beginSource.packageManifest == pin.packageManifest &&
      beginSource.subject.value == pin.managementSubject &&
      beginSource.managementSubject.value == pin.managementSubject &&
      beginSource.capability == pin.appCapability do
    throw "historical retry BEGIN differs from fixed claim operator pin"
  unless begin.shape && ApplicationLifecycleResidentProfile.beginMatchesV3 config.expectedSeed begin.begin do
    throw "historical retry BEGIN is outside resident host profile"
  let opened := verified.opened
  let some retained := opened.durable.image.accepted[prior.index]?
    | throw "original retry BEGIN record absent from verified tip"
  unless DurableReceiverCodec.intentStream.encode retained ==
      DurableReceiverCodec.intentStream.encode prior.record do
    throw "original retry BEGIN record differs from verified history"
  let some originalReceipt := verified.receipts[prior.index]?
    | throw "original retry BEGIN receipt absent from verified chronology"
  unless originalReceipt.transactionId == prior.record.transactionId &&
      originalReceipt.eventId == prior.record.event.eventId &&
      originalReceipt.acceptedCount == prior.index + 1 do
    throw "original retry BEGIN receipt differs from verified record/index"
  unless ApplicationFailedCreateRetryEvidence.markersCurrent config opened.ground begin.retry do
    throw "retry CLAIM first/created/recovery/one-use token markers refuse"
  let some appCell := cellAt config opened pin.app
    | throw "current retry claim app cell unavailable"
  let some packageCell := cellAt config opened pin.packageManifest
    | throw "current retry claim package cell unavailable"
  unless packageCell.kind == .content do
    throw "current retry claim package is not a content resource"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current retry claim app state unavailable"
  let source : ApplicationLifecycleClaim.Source :=
    { begin := begin.begin.base
      originalIndex := prior.index
      before := before
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      currentWorldRoot := opened.durable.worldRoot
      appObserveCapability := pin.appObserveCapability
      packageObserveCapability := pin.packageObserveCapability
      queryNonce := request.queryNonce }
  unless source.valid do throw "current app is not at original pending retry BEGIN state"
  let command := ApplicationLifecycleClaim.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient opened.ground command
    | throw "current retry claim command preparation refused"
  unless ApplicationLifecycleClaimCurrent.linkedCurrentPolicy config.deployment
      config.profile ambient opened.ground source prepared do
    throw "current retry claim app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current retry claim physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let appWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient opened.ground source prepared pin.app
    pin.appObserveCapability source.currentAppRoot
  let .ok appSelected := ResourceObservationAdmission.prepare context config.profile
      appWanted marker pin.appObserveCapability source.canonicalBytes
    | throw "current retry claim app observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode appSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode appCell do
    throw "retry claim app observation differs from current image"
  let packageWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient opened.ground source prepared pin.packageManifest
    pin.packageObserveCapability source.currentPackageRoot
  let .ok packageSelected := ResourceObservationAdmission.prepare context config.profile
      packageWanted marker pin.packageObserveCapability source.canonicalBytes
    | throw "current retry claim package observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode packageSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode packageCell do
    throw "retry claim package observation differs from current image"
  unless ApplicationLifecycleBeginV3Admission.installedExact config.deployment begin.begin
      packageSelected.observed.before do
    throw "current installed package differs from exact retry descriptor"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | throw "current retry claim invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "retry claim invocation plan differs from source"
  let .ok appHeader := CredentialSignatureAdmission.signingHeader
      opened.ground.authority marker (⟨.object, appWanted⟩ : PackedEffectRequest)
    | throw "current retry claim app observation signing key unavailable"
  let .ok packageHeader := CredentialSignatureAdmission.signingHeader
      opened.ground.authority marker (⟨.object, packageWanted⟩ : PackedEffectRequest)
    | throw "current retry claim package observation signing key unavailable"
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
    | throw "noncanonical retry claim operator request"
  prepareVerified config verified pin request

private def envelope (slot : SigningSlot) (signature : List UInt8) :
    Except String (List UInt8) := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical retry claim observation header"
  unless signature.length == 64 do
    throw "retry claim observation signature must be 64 bytes"
  return CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩

/-- Detached assembly does not mint current authority. Op26 refreshes the
verified tip and admits the exact three signed incidences and the one-use
retry token through `ApplicationLifecycleRetryClaimV4Receiver`. -/
def assemble (store : Minidregg.Theory.TypedAuthorization.Digest) (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 2 do
    throw "retry claim signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "retry claim plan is not an invocation"
  let some source := ApplicationLifecycleClaim.codec.decode plan.sourceBytes
    | throw "noncanonical retry claim plan source"
  let some begin := ApplicationLifecycleRetryBeginV4Ingress.codec.decode
      plan.originalBeginBytes
    | throw "noncanonical original retry BEGIN-v4"
  unless source.valid && source.begin == begin.begin.base && begin.shape &&
      plan.invocation.domain == begin.begin.base.domain &&
      plan.invocation.semantics == begin.begin.base.semantics &&
      plan.originalBeginReceipt.transactionId == begin.begin.base.transactionId &&
      plan.originalBeginReceipt.eventId ==
        (ApplicationLifecycleRetryBeginV4Admission.event begin).eventId &&
      plan.originalBeginReceipt.acceptedCount == source.originalIndex + 1 &&
      ApplicationLifecycleResidentProfile.beginMatchesV3 store begin.begin &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (ApplicationLifecycleClaim.command plan.invocation.domain
            plan.invocation.semantics source)) do
    throw "retry claim plan differs from original BEGIN-v4 or source-derived command"
  let some appSignature := signatures[invocationCount]?
    | throw "missing retry claim app observation signature"
  let some packageSignature := signatures[invocationCount + 1]?
    | throw "missing retry claim package observation signature"
  let appEnvelope ← envelope plan.appObservationSlot appSignature
  let packageEnvelope ← envelope plan.packageObservationSlot packageSignature
  let base : ApplicationLifecycleClaimIngress.Ingress :=
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      appObservationEnvelope := appEnvelope
      packageObservationEnvelope := packageEnvelope }
  return ApplicationLifecycleRetryClaimV4Ingress.codec.encode
    { base := base, originalBegin := begin }

end Minidregg.Host.ApplicationLifecycleRetryClaimV4Authoring
