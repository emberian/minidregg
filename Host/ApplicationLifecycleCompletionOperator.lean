/-
Operator-private current-image signing plan for one lifecycle completion.
The fixed Pin is loaded from Host settings, never from the request frame.
This returns exact native credential headers, not an authorization to complete.
-/
import Host.ApplicationLifecycleCompletionAuthoring
import Kernel.ApplicationLifecycleCompletionAdmission
import Kernel.NativeHostReplay
import Kernel.NativeHost

namespace Minidregg.Host.ApplicationLifecycleCompletionOperator

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Pin where
  app : Nat
  packageManifest : Nat
  managementSubject : Nat
  managementKeyId : Nat
  appCapability : CapabilityId
  appObserveCapability : CapabilityId
  packageCapability : CapabilityId
  packageObserveCapability : CapabilityId
  deriving DecidableEq

structure Request where
  beginBytes : List UInt8
  claimIngressBytes : List UInt8
  signedReportBytes : List UInt8
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream bytesStream))
    (fun request => (request.beginBytes, request.claimIngressBytes,
      request.signedReportBytes))
    (fun (beginBytes, claimIngressBytes, signedReportBytes) =>
      ⟨beginBytes, claimIngressBytes, signedReportBytes⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/LIFECYCLE-COMPLETION-OPERATOR-REQUEST/v1".toUTF8.toList
  requestStream

structure Plan where
  sourceBytes : List UInt8
  invocation : SigningPlan
  packageObservationSlot : SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.sourceBytes, plan.invocation, plan.packageObservationSlot))
    (fun (sourceBytes, invocation, packageObservationSlot) =>
      ⟨sourceBytes, invocation, packageObservationSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/LIFECYCLE-COMPLETION-OPERATOR-PLAN/v1".toUTF8.toList
  planStream

private def cellAt (config : Config) (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeaders (pin : Pin) (plan : SigningPlan) : Except String Unit := do
  for slot in plan.slots do
    let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
      | throw "noncanonical completion signing header"
    unless header.keyId == pin.managementKeyId do
      throw "completion signing key differs from operator pin"

/-- Op44 obtains a source-derived plan from the exact admitted current image.
The physical report is verified under Config's distinct custodian key before
any management header escapes. Current grants and law remain decisive in op38. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : IO (Except String Plan) := do
  let opened := verified.opened
  let some begin := ApplicationLifecycleBeginV2Ingress.codec.decode request.beginBytes
    | return .error "noncanonical completion BEGIN-v2 ingress"
  let some claim := ApplicationLifecycleClaimV2Ingress.codec.decode request.claimIngressBytes
    | return .error "noncanonical completion claim-v2 ingress"
  let some physical := ApplicationLifecycleCompletionReport.signedCodec.decode
      request.signedReportBytes
    | return .error "noncanonical signed physical completion report"
  let beginSource := begin.base.source
  if beginSource.app != pin.app ||
      beginSource.packageManifest != pin.packageManifest ||
      beginSource.managementSubject.value != pin.managementSubject then
    return .error "completion subject or resource differs from operator pin"
  if !ApplicationLifecycleResidentProfile.beginMatches begin then
    return .error "completion BEGIN is outside resident host profile"
  let some key := config.completionCustodianKey
    | return .error "pinned physical custodian key unavailable"
  match ← ApplicationLifecycleCompletionReport.check config.signature
      config.deployment.domain config.profile.semantics key begin physical with
  | .error detail => return .error detail
  | .ok _ => pure ()
  let count := physical.report.claim.core.claimReceipt.acceptedCount
  if count == 0 || !(verified.claimsV2.any fun prior =>
      prior.index + 1 == count && prior.ingress == claim &&
      prior.record.transactionId ==
        physical.report.claim.core.claimReceipt.transactionId) then
    return .error "original claim absent from admitted verified history"
  let some appCell := cellAt config opened pin.app
    | return .error "current app cell unavailable"
  let some packageCell := cellAt config opened pin.packageManifest
    | return .error "current package cell unavailable"
  let some atomBefore := ApplicationLifecycleCompletionAdmission.packageAtom
      config.deployment.domain pin.packageManifest pin.app packageCell
    | return .error "current package atom unavailable"
  let current : ApplicationLifecycleCompletionAuthoring.CurrentObservation :=
    { authorityRoot := opened.authority.snapshot.cell.root
      appRoot := appCell.payload.root
      packageRoot := packageCell.payload.root
      appCapability := pin.appCapability
      appObserveCapability := pin.appObserveCapability
      packageCapability := pin.packageCapability
      packageObserveCapability := pin.packageObserveCapability
      packageAtomBefore := atomBefore }
  let .ok source ← pure <| ApplicationLifecycleCompletionAuthoring.sourcePlan
      request.beginBytes request.claimIngressBytes request.signedReportBytes current
    | return .error "completion source identities refused"
  match ← ApplicationLifecycleCompletionHistory.select config opened source with
  | .error detail => return .error detail
  | .ok _ => pure ()
  if ApplicationLifecycleCompletionAdmission.appState pin.app appCell !=
      some source.claimedState then
    return .error "current app is no longer at claimed generation"
  if !ApplicationLifecycleCompletionAdmission.packageMatches config.deployment
      source packageCell then
    return .error "current installed package differs from completion descriptor"
  let command := source.command config.deployment.domain config.profile.semantics
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.durable command
    | return .error "current completion command preparation refused"
  if !ApplicationLifecycleCompletionAdmission.linkedCurrentPolicies config.deployment
      config.profile ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.durable source prepared then
    return .error "current completion management/package law differs"
  if !decide (DeclaredResourceController.PhysicalShape prepared) then
    return .error "current completion physical shape refused"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareLoaded config opened (.invoke commandBytes)
    | return .error "current completion invocation signing plan refused"
  if invocation.finalizedDraft != .invoke commandBytes then
    return .error "completion invocation plan differs from source"
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleCompletionAdmission.packageRequest
    config opened source prepared
  let .ok header := CredentialSignatureAdmission.signingHeader
      prepared.authority.snapshot marker (⟨.object, wanted⟩ : PackedEffectRequest)
    | return .error "current package observation signing key unavailable"
  let packageSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩
  let plan : Plan := ⟨source.canonicalBytes, invocation, packageSlot⟩
  if header.keyId != pin.managementKeyId then
    return .error "completion signer differs from operator key pin"
  match fixedHeaders pin invocation with
  | .error detail => return .error detail
  | .ok _ => pure ()
  return .ok plan

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical completion operator request"
  prepareVerified config verified pin request

/-- Op45 only inserts detached Ed25519 signatures into the exact op44 plan.
Op38 rechecks the current tip, historical claim, physical report, and all
authorization. No client-modified plan becomes an authority by decoding. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 1 do
    throw "completion signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "completion plan is not a management invocation"
  let some source := ApplicationLifecycleCompletionSource.codec.decode plan.sourceBytes
    | throw "noncanonical completion plan source"
  unless source.valid &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (source.command plan.invocation.domain plan.invocation.semantics)) do
    throw "completion plan differs from source-derived command"
  let some packageHeader := CredentialSignedEnvelopeController.headerCodec.decode
      plan.packageObservationSlot.header
    | throw "noncanonical package observation header"
  let some packageSignature := signatures[invocationCount]?
    | throw "missing package observation signature"
  unless packageSignature.length == 64 do
    throw "package observation signature must be 64 bytes"
  let packageEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨packageHeader, packageSignature⟩
  return ApplicationLifecycleCompletionIngress.codec.encode
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      packageObservationEnvelope := packageEnvelope }

end Minidregg.Host.ApplicationLifecycleCompletionOperator
