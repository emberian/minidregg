/-
Operator-private current-image signing plan for a launch-bound v3 claim.
The requested index names a BEGIN-v3 in the same verified replay history.
The request never supplies an app state, resource root, grant, or header.
-/
module

public import Host.ApplicationLifecycleClaimOperator
public import Kernel.ApplicationLifecycleClaimV3Core

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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

private def cellAtOn {deployment : CanonicalCellRegistry.Deployment} (ground : ServedBasis.Ground deployment)
    (resource : Nat) : Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical claim signing header"
  unless header.keyId == pin.managementKeyId do
    throw "claim signer differs from operator key pin"

/-- The op68 plan on a ground, for the launch-bound BEGIN at `index` whose original receipt
is `originalReceipt`: every current read (app and package cells, law, observations, signing
keys) is the ground's; the ground must answer the claim's keys. -/
private def sourceOn (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) (begin : ApplicationLifecycleBeginV3Ingress.Ingress) (index : Nat) :
    Except String (ApplicationLifecycleClaim.Source × PackedCell CanonicalCellRegistry.registry ×
      PackedCell CanonicalCellRegistry.registry) := do
  let beginSource := begin.base.source
  unless beginSource.app == pin.app &&
      beginSource.packageManifest == pin.packageManifest &&
      beginSource.subject.value == pin.managementSubject &&
      beginSource.managementSubject.value == pin.managementSubject &&
      beginSource.capability == pin.appCapability do
    throw "historical BEGIN differs from fixed claim operator pin"
  unless begin.shape && ApplicationLifecycleResidentProfile.beginMatchesV3 config.storeIdentity begin do
    throw "historical BEGIN is outside resident host profile"
  let some appCell := cellAtOn ground pin.app
    | throw "current claim app cell unavailable"
  let some packageCell := cellAtOn ground pin.packageManifest
    | throw "current claim package cell unavailable"
  unless packageCell.kind == .content do
    throw "current claim package is not a content resource"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current claim app state unavailable"
  let source : ApplicationLifecycleClaim.Source :=
    { begin := begin.base
      originalIndex := index
      before := before
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      currentWorldRoot := ground.worldRoot
      appObserveCapability := pin.appObserveCapability
      packageObserveCapability := pin.packageObserveCapability
      queryNonce := request.queryNonce }
  unless source.valid do throw "current app is not at original pending BEGIN state"
  return (source, appCell, packageCell)

/-- The keys the op68 plan reads beyond the state: its command's transaction id and operation
marker (`ApplicationLifecycleClaimCurrent.keys`) and the original BEGIN's launch markers. -/
private def planKeys (config : Config) (begin : ApplicationLifecycleBeginV3Ingress.Ingress)
    (source : ApplicationLifecycleClaim.Source) : DurableView.Keys :=
  let current := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics
    (ApplicationLifecycleClaim.command config.deployment.domain config.profile.semantics source)
  ⟨current.transactions, current.nullifiers ++
    ApplicationLifecycleBeginV3Admission.markerNullifiersOf config.deployment.domain begin.start⟩

private def prepareOn (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) (begin : ApplicationLifecycleBeginV3Ingress.Ingress) (index : Nat)
    (originalReceipt : NativeHostCodec.Receipt) : Except String Plan := do
  let (source, appCell, packageCell) ← sourceOn config ground pin request begin index
  let command := ApplicationLifecycleClaim.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, config.genesisHeight + ground.height⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient ground command
    | throw "current claim command preparation refused"
  unless ApplicationLifecycleClaimCurrent.linkedCurrentPolicy config.deployment
      config.profile ambient ground source prepared do
    throw "current claim app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current claim physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let appWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient ground source prepared pin.app
    pin.appObserveCapability source.currentAppRoot
  let .ok appSelected := ResourceObservationAdmission.prepare context config.profile
      appWanted marker pin.appObserveCapability source.canonicalBytes
    | throw "current claim app observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode appSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode appCell do
    throw "claim app observation differs from current image"
  let packageWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient ground source prepared pin.packageManifest
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
  let .ok invocation := NativeHost.prepareInvokeOn config ground (config.genesisHeight + ground.height) commandBytes
    | throw "current claim invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "claim invocation plan differs from source"
  let .ok appHeader := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, appWanted⟩ : PackedEffectRequest)
    | throw "current claim app observation signing key unavailable"
  let .ok packageHeader := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, packageWanted⟩ : PackedEffectRequest)
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

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  let some prior := verified.beginsV3.find? (fun begin => begin.index == request.originalIndex)
    | throw "original launch-bound BEGIN absent from verified history"
  let begin := prior.ingress
  let some retained := verified.opened.durable.image.accepted[prior.index]?
    | throw "original BEGIN record absent from verified tip"
  unless DurableReceiverCodec.intentStream.encode retained ==
      DurableReceiverCodec.intentStream.encode prior.record do
    throw "original BEGIN record differs from verified history"
  let some originalReceipt := verified.receiptAt prior.index
    | throw "original BEGIN receipt absent from verified chronology"
  unless originalReceipt.transactionId == prior.record.transactionId &&
      originalReceipt.eventId == prior.record.event.eventId &&
      originalReceipt.acceptedCount == prior.index + 1 do
    throw "original BEGIN receipt differs from verified record/index"
  prepareOn config verified.opened.ground pin request begin prior.index originalReceipt

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical claim operator request"
  prepareVerified config verified pin request

/-- The op68 plan on the light opening: the launch-bound BEGIN the request names is read at its
height from the Store's history (a verified record; its receipt is that record's), then the
claim is planned on the opening's basis for the claim's keys (`prepareOn`, the derivation the
full image runs). The receiver re-admits that BEGIN at its own prefix
(`ApplicationLifecycleClaimV3Core.prepare`). -/
def prepareRequestLight (config : Config) (light : NativeHostLight.Light config) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical claim operator request"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let read ← match ← reader.atHeight (request.originalIndex + 1) with
    | .error refusal => return .error refusal.message
    | .ok read => pure read
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode (NativeHostReplay.sourceBytes read.record)
    | return .error "original launch-bound BEGIN absent from the Store's history"
  let originalReceipt := NativeHost.receiptOfRecord read
  let cells ← match ← light.basis ⟨[], []⟩ with
    | .error detail => return .error detail
    | .ok basis => pure basis
  match sourceOn config (.ofBasis cells) pin request begin request.originalIndex with
  | .error detail => return .error detail
  | .ok (source, _, _) =>
      match ← light.basis (planKeys config begin source) with
      | .error detail => return .error detail
      | .ok basis => return prepareOn config (.ofBasis basis) pin request begin request.originalIndex originalReceipt

private def envelope (slot : SigningSlot) (signature : List UInt8) :
    Except String (List UInt8) := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical claim observation header"
  unless signature.length == 64 do
    throw "claim observation signature must be 64 bytes"
  return CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩

/-- Detached assembly does not mint current authority. Op26 refreshes the
verified tip and admits the exact three signed incidences again. `store` is
the assembling Host's `Config.storeIdentity`. -/
def assemble (store : Minidregg.Theory.TypedAuthorization.Digest) (plan : Plan) (signatures : List (List UInt8)) :
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
      ApplicationLifecycleResidentProfile.beginMatchesV3 store begin &&
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
