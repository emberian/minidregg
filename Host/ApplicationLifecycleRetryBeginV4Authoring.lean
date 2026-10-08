/- Exact current-manager authority to repeat CREATE on the same retained volume.
The report certifies a dead incarnation, never absence of previous effects. -/
import Host.ApplicationLifecycleBeginOperator
import Kernel.ApplicationLifecycleRetryBeginV4Admission
import Host.ApplicationLifecycleLaunchBeginAuthoring

namespace Minidregg.Host.ApplicationLifecycleRetryBeginV4Authoring

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
  launch : ApplicationLifecycleLaunchBeginAuthoring.Request
  retry : ApplicationFailedCreateRetryEvidence.Selector
  deriving DecidableEq

def requestStream : StreamCodec Request := StreamCodec.xmap
  (StreamCodec.product ApplicationLifecycleLaunchBeginAuthoring.requestStream
    ApplicationFailedCreateRetryEvidence.selectorStream)
  (fun request => (request.launch, request.retry))
  (fun (launch, retry) => ⟨launch, retry⟩)
  (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/RETRY-CREATE-BEGIN-OPERATOR-REQUEST/v4".toUTF8.toList requestStream

structure Plan where
  unsigned : ApplicationLifecycleRetryBeginV4Ingress.Ingress
  invocation : SigningPlan
  packageObservationSlot : SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationLifecycleRetryBeginV4Ingress.ingressStream
      (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.unsigned, plan.invocation, plan.packageObservationSlot))
    (fun (unsigned, invocation, packageObservationSlot) =>
      ⟨unsigned, invocation, packageObservationSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/RETRY-CREATE-BEGIN-OPERATOR-PLAN/v4".toUTF8.toList
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

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : IO (Except String Plan) := do
  let launch := request.launch
  unless launch.kind == .start && launch.createIndex.isSome do
    return .error "retry BEGIN requires explicit repeat CREATE"
  let some descriptor := ApplicationSpkLaunchDescriptor.decodeCanonical launch.descriptorBytes
    | return .error "noncanonical retry descriptor"
  unless descriptor.valid do return .error "invalid retry descriptor"
  let start ← match startBinding config.deployment.domain pin.app descriptor launch.kind launch.createIndex with
    | .error detail => return .error detail
    | .ok start => pure start
  let opened := verified.opened
  let some appCell := cellAt opened pin.app
    | return .error "current launch application cell unavailable"
  let some packageCell := cellAt opened pin.packageManifest
    | return .error "current launch package manifest unavailable"
  unless packageCell.kind == .content do
    return .error "current launch package manifest is not content"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | return .error "current launch application state unavailable"
  let source : ApplicationLifecycleBegin.Source :=
    { kind := launch.kind
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
        config.expectedSeed pin.app (if launch.kind == .stop then before.generation
                 else before.generation + 1) }
  if launch.kind == .stop then
    match verified.selectRunning source with
    | .error detail => return .error detail
    | .ok _ => pure ()
  let base : ApplicationLifecycleBeginIngress.Ingress :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }
  let inner : ApplicationLifecycleBeginV3Ingress.Ingress :=
    ({ base := base
       clientOperationId := launch.clientOperationId
       descriptor := descriptor
       volume := ApplicationLifecycleLaunchBinding.volumeId
         config.deployment.domain pin.app
       start := start } : ApplicationLifecycleBeginV3Ingress.Ingress)
  let unsigned : ApplicationLifecycleRetryBeginV4Ingress.Ingress :=
    (⟨inner, request.retry⟩ : ApplicationLifecycleRetryBeginV4Ingress.Ingress).withAuthorizationId
  unless unsigned.shape do
    return .error "launch BEGIN authorization, descriptor or action shape refused"
  let grounded ← match ServedBasis.Grounded.ofLoaded verified.reader.head opened.durable
      opened.directory opened.authority with
    | .error detail => return .error s!"retry BEGIN current ground: {detail}"
    | .ok grounded => pure grounded
  let evidence ← match ← ApplicationFailedCreateRetryEvidence.prepare config verified.reader
      grounded request.retry unsigned.begin with
    | .error detail => return .error detail
    | .ok evidence => pure evidence
  let historical := evidence.recovered.historical
  let some prior := verified.claimsV3.find? (fun prior => prior.index == historical.index)
    | return .error "retry original claim absent from admitted chronology"
  unless prior.ingress == request.retry.recovery.source.originalClaim &&
      DurableReceiverCodec.intentStream.encode prior.record ==
        DurableReceiverCodec.intentStream.encode historical.selected.record do
    return .error "retry original claim differs from admitted chronology"
  unless ApplicationLifecycleBeginV3Admission.installedExact
      config.deployment unsigned.begin packageCell do
    return .error "current installed package differs from signed launch descriptor"
  let source := unsigned.begin.base.source
  let command := ApplicationLifecycleBegin.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient opened.ground command
    | return .error "current launch BEGIN command preparation refused"
  unless ApplicationLifecycleBeginReceiver.linkedCurrentPolicy config.deployment
      config.profile ambient opened.ground source prepared do
    return .error "current launch BEGIN app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    return .error "current launch BEGIN physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleBeginReceiver.packageRequest config.deployment
    config.profile ambient opened.ground source prepared
  let .ok selected := ResourceObservationAdmission.prepare context config.profile
      wanted marker source.packageObserveCapability source.canonicalBytes
    | return .error "current launch package observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode selected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode packageCell do
    return .error "launch package observation differs from current image"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | return .error "current launch BEGIN invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    return .error "launch BEGIN invocation plan differs from bound action"
  let .ok header := CredentialSignatureAdmission.signingHeader
      opened.ground.authority marker (⟨.object, wanted⟩ : PackedEffectRequest)
    | return .error "current launch package observation signing key unavailable"
  let packageSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩
  for slot in invocation.slots ++ [packageSlot] do
    match fixedHeader pin slot with
    | .error detail => return .error detail
    | .ok _ => pure ()
  return .ok ⟨unsigned, invocation, packageSlot⟩

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical retry BEGIN operator request"
  prepareVerified config verified pin request

theorem request_decode_encode (request : Request) :
    requestCodec.decode (requestCodec.encode request) = some request := requestCodec.decode_encode request

def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let unsigned := plan.unsigned
  unless unsigned.shape && unsigned.withAuthorizationId == unsigned &&
      unsigned.begin.base.signed == (⟨[], [], [], []⟩ : DeclaredResourceController.SignedCommand) &&
      unsigned.begin.base.packageObservationEnvelope.isEmpty do
    throw "launch BEGIN plan has noncanonical unsigned action or authorization"
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 1 do
    throw "launch BEGIN signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "launch BEGIN plan is not an invocation"
  let source := unsigned.begin.base.source
  unless plan.invocation.finalizedDraft == .invoke
      (DeclaredResourceController.commandCodec.encode
        (ApplicationLifecycleBegin.command plan.invocation.domain
          plan.invocation.semantics source)) &&
      unsigned.begin.base.domain == plan.invocation.domain &&
      unsigned.begin.base.semantics == plan.invocation.semantics do
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
  let base := { unsigned.begin.base with signed := signedCommand }
  let base := { base with packageObservationEnvelope := packageEnvelope }
  return ApplicationLifecycleRetryBeginV4Ingress.codec.encode
    { unsigned with begin := { unsigned.begin with base := base } }


end Minidregg.Host.ApplicationLifecycleRetryBeginV4Authoring
