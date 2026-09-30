/-
Operator-private current-image signing plan for resident INSTALL/START BEGIN-v2.
Only the signed SPK descriptor, kind and operation ID enter the request. Mini
derives the current app state, roots, generation, command and exact headers.
-/
import Kernel.NativeHost
import Kernel.NativeHostReplay
import Kernel.ApplicationLifecycleBeginV2Admission
import Kernel.ApplicationLifecycleResidentProfile
import Kernel.ApplicationLifecycleClaimCurrent

namespace Minidregg.Host.ApplicationLifecycleBeginOperator

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

structure Pin where
  app : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  managementSubject : Nat
  managementKeyId : Nat
  appCapability : CapabilityId
  packageObserveCapability : CapabilityId
  deriving DecidableEq

structure Request where
  kind : ApplicationLifecycleBegin.Kind
  operationId : Nat
  descriptorBytes : List UInt8
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product ApplicationLifecycleBegin.kindStream
    (StreamCodec.product StreamCodec.nat bytesStream))
    (fun request => (request.kind, request.operationId, request.descriptorBytes))
    (fun (kind, operationId, descriptorBytes) =>
      ⟨kind, operationId, descriptorBytes⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/RESIDENT-BEGIN-OPERATOR-REQUEST/v1".toUTF8.toList requestStream

structure Plan where
  sourceBytes : List UInt8
  descriptorBytes : List UInt8
  invocation : SigningPlan
  packageObservationSlot : SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream
      (StreamCodec.product signingPlanStream signingSlotStream)))
    (fun plan => (plan.sourceBytes, plan.descriptorBytes,
      plan.invocation, plan.packageObservationSlot))
    (fun (sourceBytes, descriptorBytes, invocation, packageObservationSlot) =>
      ⟨sourceBytes, descriptorBytes, invocation, packageObservationSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/RESIDENT-BEGIN-OPERATOR-PLAN/v1".toUTF8.toList planStream

private def cellAt (config : Config) (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical resident BEGIN signing header"
  unless header.keyId == pin.managementKeyId do
    throw "resident BEGIN signer differs from operator key pin"

/-- A source-authored current-image plan. Signatures are absent; op22 later
rechecks both the ordinary invocation and separate package observation under
the current authority snapshot before recording a pending BEGIN. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : Except String Plan := do
  unless request.kind == .install || request.kind == .start do
    throw "resident BEGIN plan supports INSTALL or START only"
  let some descriptor := ApplicationSpkPackageIdentity.decodeCanonical request.descriptorBytes
    | throw "noncanonical signed-SPK descriptor"
  unless descriptor.valid do throw "invalid signed-SPK descriptor"
  let opened := verified.opened
  let some appCell := cellAt config opened pin.app
    | throw "current application cell unavailable"
  let some packageCell := cellAt config opened pin.packageManifest
    | throw "current package manifest cell unavailable"
  unless packageCell.kind == .content do
    throw "current package manifest is not a content resource"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current application state unavailable"
  let source : ApplicationLifecycleBegin.Source :=
    { kind := request.kind
      app := pin.app
      packageManifest := pin.packageManifest
      snapshotManifest := pin.snapshotManifest
      operationId := request.operationId
      subject := ⟨pin.managementSubject⟩
      managementSubject := ⟨pin.managementSubject⟩
      capability := pin.appCapability
      packageObserveCapability := pin.packageObserveCapability
      before := before
      appRoot := appCell.payload.root
      packageRoot := packageCell.payload.root
      packageDigest := descriptor.root
      imageIdentity := descriptor.imageIdentity
      processGeneration := before.generation + 1
      processIdentity := ApplicationLifecycleResidentProfile.processIdentity
        pin.app (before.generation + 1) }
  unless source.valid do throw "current application does not admit requested BEGIN phase"
  let command := ApplicationLifecycleBegin.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient opened.durable command
    | throw "current resident BEGIN command preparation refused"
  unless ApplicationLifecycleBeginReceiver.linkedCurrentPolicy config.deployment
      config.profile ambient opened.durable source prepared do
    throw "current resident BEGIN app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current resident BEGIN physical shape refused"
  let base : ApplicationLifecycleBeginIngress.Ingress :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }
  let unsigned : ApplicationLifecycleBeginV2Ingress.Ingress :=
    { base := base, descriptor := descriptor }
  unless ApplicationLifecycleBeginV2Ingress.descriptorBound unsigned do
    throw "resident BEGIN descriptor differs from proposed manifest"
  unless ApplicationLifecycleBeginV2Admission.installedExact
      config.deployment unsigned packageCell do
    throw "current installed package differs from signed SPK descriptor"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleBeginReceiver.packageRequest config.deployment
    config.profile ambient opened.durable source prepared
  let .ok selected := ResourceObservationAdmission.prepare context config.profile
      wanted marker source.packageObserveCapability source.canonicalBytes
    | throw "current package observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode selected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode packageCell do
    throw "package observation differs from current old image"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | throw "current resident BEGIN invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "resident BEGIN invocation plan differs from source"
  let .ok header := CredentialSignatureAdmission.signingHeader
      prepared.authority.snapshot marker (⟨.object, wanted⟩ : PackedEffectRequest)
    | throw "current package observation signing key unavailable"
  let packageSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩
  for slot in invocation.slots do fixedHeader pin slot
  fixedHeader pin packageSlot
  return ⟨source.canonicalBytes, descriptor.canonicalBytes,
    invocation, packageSlot⟩

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical resident BEGIN operator request"
  prepareVerified config verified pin request

/-- Insert the detached signatures in the exact plan order. Decoding a plan
does not make it current; op22 rechecks the complete ingress on a fresh tip. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 1 do
    throw "resident BEGIN signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "resident BEGIN plan is not an invocation"
  let some source := ApplicationLifecycleBegin.sourceCodec.decode plan.sourceBytes
    | throw "noncanonical resident BEGIN plan source"
  let some descriptor := ApplicationSpkPackageIdentity.decodeCanonical plan.descriptorBytes
    | throw "noncanonical resident BEGIN plan descriptor"
  unless source.valid &&
      source.imageIdentity == descriptor.imageIdentity &&
      source.processIdentity ==
        ApplicationLifecycleResidentProfile.processIdentity source.app source.processGeneration &&
      ApplicationLifecycleBeginV2Ingress.descriptorBound
        { base := { domain := plan.invocation.domain
                    semantics := plan.invocation.semantics
                    source := source
                    signed := ⟨[], [], [], []⟩
                    packageObservationEnvelope := [] }
          descriptor := descriptor } &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (ApplicationLifecycleBegin.command plan.invocation.domain
            plan.invocation.semantics source)) do
    throw "resident BEGIN plan differs from source-derived command"
  let some packageHeader := CredentialSignedEnvelopeController.headerCodec.decode
      plan.packageObservationSlot.header
    | throw "noncanonical resident BEGIN package observation header"
  let some packageSignature := signatures[invocationCount]?
    | throw "missing resident BEGIN package observation signature"
  unless packageSignature.length == 64 do
    throw "resident BEGIN package observation signature must be 64 bytes"
  let packageEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨packageHeader, packageSignature⟩
  let base : ApplicationLifecycleBeginIngress.Ingress :=
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      packageObservationEnvelope := packageEnvelope }
  return ApplicationLifecycleBeginV2Ingress.codec.encode
    { base := base, descriptor := descriptor }

end Minidregg.Host.ApplicationLifecycleBeginOperator
