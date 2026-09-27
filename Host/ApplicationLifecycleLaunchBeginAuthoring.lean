/-
Operator-private current-image plan for source-bound INSTALL or first-create
START. Continue is deliberately refused until Verified exposes the admitted
completed-create certificate. A client operation ID is only a correlation
value: the signed ordinary operation ID is derived from the complete v3
descriptor, volume, and selected action before any header is issued.
-/
import Host.ApplicationLifecycleBeginOperator
import Kernel.ApplicationLifecycleBeginV3Admission

namespace Minidregg.Host.ApplicationLifecycleLaunchBeginAuthoring

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

abbrev Pin := ApplicationLifecycleBeginOperator.Pin

structure Request where
  kind : ApplicationLifecycleBegin.Kind
  clientOperationId : Nat
  descriptorBytes : List UInt8
  createIndex : Option Nat
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBegin.kindStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream (StreamCodec.option StreamCodec.nat))))
    (fun request => (request.kind, request.clientOperationId,
      request.descriptorBytes, request.createIndex))
    (fun (kind, clientOperationId, descriptorBytes, createIndex) =>
      ⟨kind, clientOperationId, descriptorBytes, createIndex⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-REQUEST/v1".toUTF8.toList
  requestStream

structure Plan where
  unsigned : ApplicationLifecycleBeginV3Ingress.Ingress
  invocation : SigningPlan
  packageObservationSlot : SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleBeginV3Ingress.ingressStream
      (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.unsigned, plan.invocation, plan.packageObservationSlot))
    (fun (unsigned, invocation, packageObservationSlot) =>
      ⟨unsigned, invocation, packageObservationSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-PLAN/v1".toUTF8.toList
  planStream

private def cellAt {config : Config} (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical launch BEGIN signing header"
  unless header.keyId == pin.managementKeyId do
    throw "launch BEGIN signer differs from fixed operator key"

private def startBinding (domain : Digest) (app : Nat)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor)
    (kind : ApplicationLifecycleBegin.Kind) (index : Option Nat) :
    Except String (Option ApplicationLifecycleLaunchBinding.Binding) := do
  match kind, index with
  | .install, none => pure none
  | .start, some selected =>
      let some command := descriptor.selectedCreate selected
        | throw "launch START create index is absent from signed descriptor"
      let volume := ApplicationLifecycleLaunchBinding.volumeId domain app
      pure (some
        { app := app
          volume := volume
          packageRoot := descriptor.root
          choice := .create selected
          priorCreate := none
          commandDigest := command.digest })
  | .start, none => throw "launch START needs a selected create action"
  | .install, some _ => throw "launch INSTALL cannot select a create action"
  | _, _ => throw "launch BEGIN authoring supports INSTALL or first-create START only"

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  let some descriptor := ApplicationSpkLaunchDescriptor.codec.decode
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  let opened := verified.opened
  let some appCell := cellAt opened pin.app
    | throw "current launch application cell unavailable"
  let some packageCell := cellAt opened pin.packageManifest
    | throw "current launch package manifest unavailable"
  unless packageCell.kind == .content do
    throw "current launch package manifest is not content"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current launch application state unavailable"
  let source : ApplicationLifecycleBegin.Source :=
    { kind := request.kind
      app := pin.app
      packageManifest := pin.packageManifest
      snapshotManifest := pin.snapshotManifest
      operationId := 0
      subject := ⟨pin.managementSubject⟩
      managementSubject := ⟨pin.managementSubject⟩
      capability := pin.appCapability
      packageObserveCapability := pin.packageObserveCapability
      before := before
      authorityRoot := opened.authority.snapshot.cell.root
      appRoot := appCell.payload.root
      packageRoot := packageCell.payload.root
      packageDigest := descriptor.root
      imageIdentity := descriptor.package.imageIdentity
      processGeneration := before.generation + 1
      processIdentity := ApplicationLifecycleResidentProfile.processIdentity
        pin.app (before.generation + 1) }
  let start ← startBinding config.deployment.domain pin.app descriptor
    request.kind request.createIndex
  let base : ApplicationLifecycleBeginIngress.Ingress :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }
  let unsigned : ApplicationLifecycleBeginV3Ingress.Ingress :=
    ({ base := base
       clientOperationId := request.clientOperationId
       descriptor := descriptor
       volume := ApplicationLifecycleLaunchBinding.volumeId
         config.deployment.domain pin.app
       start := start } : ApplicationLifecycleBeginV3Ingress.Ingress).withAuthorizationId
  unless unsigned.shape do
    throw "launch BEGIN authorization, descriptor or action shape refused"
  unless ApplicationLifecycleBeginV3Admission.markersCurrent opened.durable unsigned do
    throw "launch BEGIN first-attempt or created marker refuses action"
  unless ApplicationLifecycleBeginV3Admission.installedExact
      config.deployment unsigned packageCell do
    throw "current installed package differs from signed launch descriptor"
  let source := unsigned.base.source
  let command := ApplicationLifecycleBegin.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient opened.durable command
    | throw "current launch BEGIN command preparation refused"
  unless ApplicationLifecycleBeginReceiver.linkedCurrentPolicy config.deployment
      config.profile ambient opened.durable source prepared do
    throw "current launch BEGIN app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current launch BEGIN physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleBeginReceiver.packageRequest config.deployment
    config.profile ambient opened.durable source prepared
  let .ok selected := ResourceObservationAdmission.prepare context config.profile
      wanted marker source.packageObserveCapability source.canonicalBytes
    | throw "current launch package observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode selected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode packageCell do
    throw "launch package observation differs from current image"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | throw "current launch BEGIN invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "launch BEGIN invocation plan differs from bound action"
  let .ok header := CredentialSignatureAdmission.signingHeader
      prepared.authority.snapshot marker (⟨.object, wanted⟩ : PackedEffectRequest)
    | throw "current launch package observation signing key unavailable"
  let packageSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩
  for slot in invocation.slots do fixedHeader pin slot
  fixedHeader pin packageSlot
  return ⟨unsigned, invocation, packageSlot⟩

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch BEGIN operator request"
  prepareVerified config verified pin request

/-- Detached assembly binds the same authorization ID, descriptor and action.
Fresh event23 admission still rechecks current image, signatures and history. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let unsigned := plan.unsigned
  unless unsigned.shape && unsigned.withAuthorizationId == unsigned &&
      unsigned.base.signed == (⟨[], [], [], []⟩ : DeclaredResourceController.SignedCommand) &&
      unsigned.base.packageObservationEnvelope.isEmpty do
    throw "launch BEGIN plan has noncanonical unsigned action or authorization"
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 1 do
    throw "launch BEGIN signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "launch BEGIN plan is not an invocation"
  let source := unsigned.base.source
  unless plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (ApplicationLifecycleBegin.command plan.invocation.domain
          plan.invocation.semantics source)) &&
      unsigned.base.domain == plan.invocation.domain &&
      unsigned.base.semantics == plan.invocation.semantics do
    throw "launch BEGIN invocation differs from exact v3 authorization"
  let some packageHeader := CredentialSignedEnvelopeController.headerCodec.decode
      plan.packageObservationSlot.header
    | throw "noncanonical launch package observation header"
  let some packageSignature := signatures[invocationCount]?
    | throw "missing launch package observation signature"
  unless packageSignature.length == 64 do
    throw "launch package observation signature must be 64 bytes"
  let packageEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨packageHeader, packageSignature⟩
  let base := { unsigned.base with signed := signedCommand }
  let base := { base with packageObservationEnvelope := packageEnvelope }
  return ApplicationLifecycleBeginV3Ingress.codec.encode
    { unsigned with base := base }

end Minidregg.Host.ApplicationLifecycleLaunchBeginAuthoring
