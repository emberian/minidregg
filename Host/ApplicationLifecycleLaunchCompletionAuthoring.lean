/-
Operator-private current-image signing plan for one lifecycle completion.
The fixed Pin is loaded from Host settings, never from the request frame.
This returns exact native credential headers, not an authorization to complete.
-/
module

public import Host.ApplicationLifecycleCompletionOperator
public import Kernel.ApplicationLifecycleCompletionV2Admission
public import Kernel.NativeHostReplay
public import Kernel.NativeHost
public import Kernel.NativeHostStoreIdentity

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Host.ApplicationLifecycleLaunchCompletionAuthoring

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

abbrev Pin := ApplicationLifecycleCompletionOperator.Pin

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
  "DREGG/APPLICATION/LIFECYCLE-LAUNCH-COMPLETION-OPERATOR-REQUEST/v1".toUTF8.toList
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
  "DREGG/APPLICATION/LIFECYCLE-LAUNCH-COMPLETION-OPERATOR-PLAN/v1".toUTF8.toList
  planStream

private def cellAtOn {deployment : CanonicalCellRegistry.Deployment} (ground : ServedBasis.Ground deployment)
    (resource : Nat) : Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeaders (pin : Pin) (plan : SigningPlan) : Except String Unit := do
  for slot in plan.slots do
    let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
      | throw "noncanonical completion signing header"
    unless header.keyId == pin.managementKeyId do
      throw "completion signing key differs from operator pin"

/-- Op70 obtains a source-derived plan on a ground, its original claim selected and
re-admitted at its own prefix through `reader` (`ApplicationLifecycleCompletionV2History.select`).
The physical report is verified under the platform record's custodian key before
any management header escapes. Current grants and law remain decisive in op38. -/
def prepareOn (config : Config) (ground : ServedBasis.Ground config.deployment)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (pin : Pin) (request : Request) : IO (Except String Plan) := do
  let some begin := ApplicationLifecycleBeginV3Ingress.codec.decode request.beginBytes
    | return .error "noncanonical completion BEGIN-v3 ingress"
  let some claim := ApplicationLifecycleClaimV3Ingress.codec.decode request.claimIngressBytes
    | return .error "noncanonical completion claim-v3 ingress"
  let some physical := ApplicationLifecycleCompletionV2Report.signedCodec.decode
      request.signedReportBytes
    | return .error "noncanonical signed physical completion report"
  let beginSource := begin.base.source
  if beginSource.app != pin.app ||
      beginSource.packageManifest != pin.packageManifest ||
      beginSource.managementSubject.value != pin.managementSubject then
    return .error "completion subject or resource differs from operator pin"
  if !ApplicationLifecycleResidentProfile.beginMatchesV3 config.storeIdentity begin then
    return .error "completion BEGIN is outside resident host profile"
  let some record := PlatformCellDomain.recordOn config.deployment ground.cells
    | return .error "platform cell unavailable (completion custodian key)"
  let some key := record.completionCustodianKey
    | return .error "physical custodian key unavailable in the platform record"
  match ← ApplicationLifecycleCompletionV2Report.check config.signature
      config.deployment.domain config.profile.semantics key begin physical with
  | .error detail => return .error detail
  | .ok _ => pure ()
  if physical.report.claim.core.claimReceipt.acceptedCount == 0 then
    return .error "original claim receipt has zero accepted count"
  let some appCell := cellAtOn ground pin.app
    | return .error "current app cell unavailable"
  let some packageCell := cellAtOn ground pin.packageManifest
    | return .error "current package cell unavailable"
  let some atomBefore := ApplicationLifecycleCompletionV2Admission.packageAtom
      config.deployment.domain pin.packageManifest pin.app packageCell
    | return .error "current package atom unavailable"
  let source : ApplicationLifecycleCompletionV2Source.Source :=
    { originalBegin := begin
      originalClaim := claim
      physical := physical
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      appCapability := pin.appCapability
      appObserveCapability := pin.appObserveCapability
      packageCapability := pin.packageCapability
      packageObserveCapability := pin.packageObserveCapability
      packageAtomBefore := atomBefore }
  unless source.valid do
    return .error "completion source identities refused"
  match ← ApplicationLifecycleCompletionV2History.select config reader ground.height source with
  | .error detail => return .error detail
  | .ok _ => pure ()
  if ApplicationLifecycleCompletionV2Admission.appState pin.app appCell !=
      some source.claimedState then
    return .error "current app is no longer at claimed generation"
  if !ApplicationLifecycleCompletionV2Admission.packageMatches config.deployment
      source packageCell then
    return .error "current installed package differs from completion descriptor"
  let preview : ApplicationLifecycleCompletionV2Ingress.Ingress :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }
  unless ApplicationLifecycleCompletionV2Admission.creationMarkersCurrent
      config ground preview do
    return .error "completion creation marker state refused"
  let command := source.command config.deployment.domain config.profile.semantics
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground command
    | return .error "current completion command preparation refused"
  if !ApplicationLifecycleCompletionV2Admission.linkedCurrentPolicies config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground source prepared then
    return .error "current completion management/package law differs"
  if !decide (DeclaredResourceController.PhysicalShape prepared) then
    return .error "current completion physical shape refused"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareInvokeOn config ground (config.genesisHeight + ground.height) commandBytes
    | return .error "current completion invocation signing plan refused"
  if invocation.finalizedDraft != .invoke commandBytes then
    return .error "completion invocation plan differs from source"
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleCompletionV2Admission.packageRequest
    config ground source prepared
  let .ok header := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, wanted⟩ : PackedEffectRequest)
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

def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (request : Request) : IO (Except String Plan) :=
  prepareOn config verified.opened.ground verified.reader pin request

/-- The keys op70 reads beyond the state, for the request's source on the cells of `ground`:
the completion command's transaction id and operation marker and its creation markers
(`ApplicationLifecycleCompletionV2Admission.keys`); none when the request does not decode. -/
private def planKeys (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) : Option DurableView.Keys := do
  let begin ← ApplicationLifecycleBeginV3Ingress.codec.decode request.beginBytes
  let claim ← ApplicationLifecycleClaimV3Ingress.codec.decode request.claimIngressBytes
  let physical ← ApplicationLifecycleCompletionV2Report.signedCodec.decode request.signedReportBytes
  let appCell ← cellAtOn ground pin.app
  let packageCell ← cellAtOn ground pin.packageManifest
  let atomBefore ← ApplicationLifecycleCompletionV2Admission.packageAtom
      config.deployment.domain pin.packageManifest pin.app packageCell
  let source : ApplicationLifecycleCompletionV2Source.Source :=
    { originalBegin := begin
      originalClaim := claim
      physical := physical
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      appCapability := pin.appCapability
      appObserveCapability := pin.appObserveCapability
      packageCapability := pin.packageCapability
      packageObserveCapability := pin.packageObserveCapability
      packageAtomBefore := atomBefore }
  return ApplicationLifecycleCompletionV2Admission.keys config
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }

/-- The op70 plan on the light opening: planned on the opening's basis for the completion's
keys (`prepareOn`), its original claim selected through the opening's Reader. -/
def prepareRequestLight (config : Config) (light : NativeHostLight.Light config) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical completion operator request"
  let cells ← match ← light.basis ⟨[], []⟩ with
    | .error detail => return .error detail
    | .ok basis => pure basis
  let keys := (planKeys config (.ofBasis cells) pin request).getD ⟨[], []⟩
  match ← light.basis keys with
  | .error detail => return .error detail
  | .ok basis =>
      prepareOn config (.ofBasis basis) (light.opening.reader config.transport ResourceBirthCodec.rootBytes)
        pin request

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical completion operator request"
  prepareVerified config verified pin request

/-- Op71 only inserts detached Ed25519 signatures into the exact op70 plan.
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
  let some source := ApplicationLifecycleCompletionV2Source.codec.decode plan.sourceBytes
    | throw "noncanonical completion plan source"
  unless source.valid &&
      plan.invocation.domain == source.originalBegin.base.domain &&
      plan.invocation.semantics == source.originalBegin.base.semantics &&
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
  return ApplicationLifecycleCompletionV2Ingress.codec.encode
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      packageObservationEnvelope := packageEnvelope }

end Minidregg.Host.ApplicationLifecycleLaunchCompletionAuthoring
