/-
Operator-private current-image plan for source-bound INSTALL, START and STOP.
Continue selects an admitted completed-create certificate from Verified.
A client operation ID is only a correlation
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

/-- A continue request names a successful completed-create record by its
accepted index. The receipt and physical custody are selected from Verified,
never supplied by the caller. -/
structure ContinueRequest where
  clientOperationId : Nat
  descriptorBytes : List UInt8
  createdIndex : Nat
  deriving DecidableEq

def continueRequestStream : StreamCodec ContinueRequest :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream StreamCodec.nat))
    (fun request => (request.clientOperationId, request.descriptorBytes,
      request.createdIndex))
    (fun (clientOperationId, descriptorBytes, createdIndex) =>
      ⟨clientOperationId, descriptorBytes, createdIndex⟩)
    (by intro request; cases request; rfl)

def continueRequestCodec : LawfulCodec ContinueRequest := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-CONTINUE-OPERATOR-REQUEST/v1".toUTF8.toList
  continueRequestStream

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

/-- Only the verifier-selected latest running event25 may identify a physical
STOP target. The receipt and exact incarnation are operator-private plan data;
the signed BEGIN still binds the unit, and native replay reselects this prior
before admitting STOP. -/
structure RunningWitness where
  index : Nat
  receipt : NativeHostCodec.Receipt
  generation : Int
  unit : List UInt8
  image : List UInt8
  invocationId : List UInt8
  controlGroup : List UInt8
  custody : ApplicationLifecycleLaunchBinding.Custody
  deriving DecidableEq

def runningWitnessStream : StreamCodec RunningWitness :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product NativeHostCodec.receiptStream
        (StreamCodec.product IntStream.intStream
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream
              (StreamCodec.product bytesStream
                (StreamCodec.product bytesStream
                  ApplicationLifecycleLaunchBinding.custodyStream)))))))
    (fun witness => (witness.index, witness.receipt, witness.generation,
      witness.unit, witness.image, witness.invocationId,
      witness.controlGroup, witness.custody))
    (fun (index, receipt, generation, unit, image, invocationId,
          controlGroup, custody) =>
      ⟨index, receipt, generation, unit, image, invocationId,
        controlGroup, custody⟩)
    (by intro witness; cases witness; rfl)

structure StopPlan where
  base : Plan
  running : RunningWitness

def stopPlanStream : StreamCodec StopPlan :=
  StreamCodec.xmap (StreamCodec.product planStream runningWitnessStream)
    (fun plan => (plan.base, plan.running))
    (fun (base, running) => ⟨base, running⟩)
    (by intro plan; cases plan; rfl)

def stopPlanCodec : LawfulCodec StopPlan := NativeHostCodec.framed
  "DREGG/APPLICATION/LAUNCH-STOP-OPERATOR-PLAN/v2".toUTF8.toList
  stopPlanStream

theorem stopPlan_decode_encode (plan : StopPlan) :
    stopPlanCodec.decode (stopPlanCodec.encode plan) = some plan :=
  stopPlanCodec.decode_encode plan


def StopPlan.shape (plan : StopPlan) : Bool :=
  let source := plan.base.unsigned.base.source
  source.kind == .stop && plan.base.unsigned.start == none &&
    plan.running.receipt.acceptedCount == plan.running.index + 1 &&
    plan.running.generation == source.before.generation &&
    plan.running.unit == source.processIdentity &&
    plan.running.image == source.imageIdentity &&
    !plan.running.invocationId.isEmpty &&
    !plan.running.controlGroup.isEmpty &&
    plan.running.custody.validFor plan.base.unsigned.volume

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
  | .stop, none => pure none
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
  | .stop, some _ => throw "launch STOP cannot select a create action"
  | _, _ => throw "launch BEGIN authoring supports INSTALL, START or STOP only"

private def prepareSelectedVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) (descriptor : ApplicationSpkLaunchDescriptor.Descriptor)
    (start : Option ApplicationLifecycleLaunchBinding.Binding) : Except String Plan := do
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
      appRoot := appCell.payload.root
      packageRoot := packageCell.payload.root
      packageDigest := descriptor.root
      imageIdentity := descriptor.package.imageIdentity
      processGeneration := before.generation + 1
      processIdentity := ApplicationLifecycleResidentProfile.processIdentity
        pin.app (if request.kind == .stop then before.generation
                 else before.generation + 1) }
  if request.kind == .stop then
    match verified.selectRunning source with
    | .error detail => throw detail
    | .ok _ => pure ()
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

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  if request.kind == .stop then
    throw "STOP requires the versioned running-witness operator plan"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  let start ← startBinding config.deployment.domain pin.app descriptor
    request.kind request.createIndex
  prepareSelectedVerified config verified pin request descriptor start

/-- The op66 STOP plan carries the exact latest running completion certified
by the same verified tip used for all current-image signing headers. A caller
cannot supply or replace the physical incarnation in this request. -/
def prepareStopVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String StopPlan := do
  unless request.kind == .stop && request.createIndex == none do
    throw "versioned STOP plan requires STOP without create action"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.descriptorBytes
    | throw "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do throw "invalid signed-SPK launch descriptor"
  let base ← prepareSelectedVerified config verified pin request descriptor none
  let running ← verified.selectRunning base.unsigned.base.source
  let prior := running.prior
  let physical := prior.ingress.source.physical.report
  let some custody := physical.volumeCustody
    | throw "admitted running completion has no volume custody"
  let plan : StopPlan :=
    { base := base
      running :=
        { index := prior.index
          receipt := prior.receipt
          generation := prior.ingress.source.originalBegin.base.source.processGeneration
          unit := physical.unit
          image := physical.materializedImage
          invocationId := physical.invocationId
          controlGroup := physical.controlGroup
          custody := custody } }
  unless plan.shape do throw "STOP running-witness plan differs from verified source"
  return plan

def prepareStopRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String StopPlan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch STOP operator request"
  prepareStopVerified config verified pin request

def prepareContinueRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := continueRequestCodec.decode bytes
    | return .error "noncanonical launch continue operator request"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical
      request.descriptorBytes
    | return .error "noncanonical signed-SPK launch descriptor"
  unless descriptor.valid do return .error "invalid signed-SPK launch descriptor"
  let some prior := verified.createdV3.find? (fun prior => prior.index == request.createdIndex)
    | return .error "selected successful create absent from verified history"
  let some custody := prior.ingress.source.physical.report.volumeCustody
    | return .error "selected successful create lacks volume custody"
  let binding : ApplicationLifecycleLaunchBinding.Binding :=
    { app := pin.app
      volume := ApplicationLifecycleLaunchBinding.volumeId config.deployment.domain pin.app
      packageRoot := descriptor.root
      choice := .continue
      priorCreate := some (prior.receipt, custody)
      commandDigest := descriptor.continueCommand.digest }
  match ← verified.selectCreated binding with
  | .error detail => return .error detail
  | .ok _ =>
      let beginRequest : Request :=
        { kind := .start
          clientOperationId := request.clientOperationId
          descriptorBytes := request.descriptorBytes
          createIndex := none }
      return prepareSelectedVerified config verified pin beginRequest descriptor (some binding)

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical launch BEGIN operator request"
  prepareVerified config verified pin request

/-- Detached assembly binds the same authorization ID, descriptor and action.
Fresh event23 admission still rechecks current image, signatures and history. -/
private def assembleBase (plan : Plan) (signatures : List (List UInt8)) :
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

/-- Legacy op67 plan shape remains byte-identical for INSTALL and START.
STOP cannot be assembled from a v1 plan with no running-incarnation witness. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  if plan.unsigned.base.source.kind == .stop then
    throw "STOP requires the versioned running-witness operator plan"
  assembleBase plan signatures

def assembleStop (plan : StopPlan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  unless plan.shape do throw "STOP running-witness plan shape refused"
  assembleBase plan.base signatures

end Minidregg.Host.ApplicationLifecycleLaunchBeginAuthoring
