/-
Operator-private current-image signing plan for one retry-CREATE completion.
The fixed Pin is loaded from Host settings, never from the request frame.
This returns exact native credential headers, not an authorization to complete.
-/
module

public import Host.ApplicationLifecycleCompletionOperator
public import Kernel.ApplicationLifecycleRetryCompletionV4Admission
public import Kernel.NativeHostReplay
public import Kernel.NativeHost

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

namespace Minidregg.Host.ApplicationLifecycleRetryCompletionV4Authoring

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
  "DREGG/APPLICATION/RETRY-CREATE-COMPLETION-OPERATOR-REQUEST/v4".toUTF8.toList
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
  "DREGG/APPLICATION/RETRY-CREATE-COMPLETION-OPERATOR-PLAN/v4".toUTF8.toList
  planStream

private def cellAtOn {deployment : CanonicalCellRegistry.Deployment} (ground : ServedBasis.Ground deployment)
    (resource : Nat) : Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeaders (pin : Pin) (plan : SigningPlan) : Except String Unit := do
  for slot in plan.slots do
    let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
      | throw "noncanonical retry completion signing header"
    unless header.keyId == pin.managementKeyId do
      throw "retry completion signing key differs from operator pin"

/-- Op70 (v4 frame) obtains a source-derived plan from the exact admitted
current image. The physical report is verified under Config's distinct
custodian key before any management header escapes. Current grants and law
remain decisive in op38. -/
private def prepareOn (config : Config) {store : DurableHistory.StoreIdentity}
    (ground : ServedBasis.Ground config.deployment)
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store) (pin : Pin)
    (request : Request) : IO (Except String Plan) := do
  let some begin := ApplicationLifecycleRetryBeginV4Ingress.codec.decode request.beginBytes
    | return .error "noncanonical completion retry BEGIN-v4 ingress"
  let some claim := ApplicationLifecycleRetryClaimV4Ingress.codec.decode
      request.claimIngressBytes
    | return .error "noncanonical completion retry claim-v4 ingress"
  let some physical := ApplicationLifecycleRetryCompletionV4Report.signedCodec.decode
      request.signedReportBytes
    | return .error "noncanonical signed retry physical completion report"
  let beginSource := begin.begin.base.source
  if beginSource.app != pin.app ||
      beginSource.packageManifest != pin.packageManifest ||
      beginSource.managementSubject.value != pin.managementSubject then
    return .error "retry completion subject or resource differs from operator pin"
  if !ApplicationLifecycleResidentProfile.beginMatchesV3 config.storeIdentity begin.begin then
    return .error "retry completion BEGIN is outside resident host profile"
  let some record := PlatformCellDomain.recordOn config.deployment ground.cells
    | return .error "platform cell unavailable (completion custodian key)"
  let some key := record.completionCustodianKey
    | return .error "physical custodian key unavailable in the platform record"
  match ← ApplicationLifecycleRetryCompletionV4Report.check config.signature
      config.deployment.domain config.profile.semantics key begin physical with
  | .error detail => return .error detail
  | .ok _ => pure ()
  if physical.report.claim.core.claimReceipt.acceptedCount == 0 then
    return .error "original retry claim absent from admitted verified history"
  let some appCell := cellAtOn ground pin.app
    | return .error "current app cell unavailable"
  let some packageCell := cellAtOn ground pin.packageManifest
    | return .error "current package cell unavailable"
  let some atomBefore := ApplicationLifecycleRetryCompletionV4Admission.packageAtom
      config.deployment.domain pin.packageManifest pin.app packageCell
    | return .error "current package atom unavailable"
  let source : ApplicationLifecycleRetryCompletionV4Source.Source :=
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
    return .error "retry completion source identities refused"
  match ← ApplicationLifecycleRetryCompletionV4History.select config reader ground.height source with
  | .error detail => return .error detail
  | .ok _ => pure ()
  if ApplicationLifecycleRetryCompletionV4Admission.appState pin.app appCell !=
      some source.claimedState then
    return .error "current app is no longer at claimed generation"
  if !ApplicationLifecycleRetryCompletionV4Admission.packageMatches config.deployment
      source packageCell then
    return .error "current installed package differs from retry completion descriptor"
  let preview : ApplicationLifecycleRetryCompletionV4Ingress.Ingress :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }
  unless ApplicationLifecycleRetryCompletionV4Admission.creationMarkersCurrent
      config ground preview do
    return .error "retry completion token/creation marker state refused"
  let command := source.command config.deployment.domain config.profile.semantics
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground command
    | return .error "current retry completion command preparation refused"
  if !ApplicationLifecycleRetryCompletionV4Admission.linkedCurrentPolicies config.deployment
      config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
      ground source prepared then
    return .error "current retry completion management/package law differs"
  if !decide (DeclaredResourceController.PhysicalShape prepared) then
    return .error "current retry completion physical shape refused"
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let .ok invocation := NativeHost.prepareInvokeOn config ground (config.genesisHeight + ground.height) commandBytes
    | return .error "current retry completion invocation signing plan refused"
  if invocation.finalizedDraft != .invoke commandBytes then
    return .error "retry completion invocation plan differs from source"
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let wanted := ApplicationLifecycleRetryCompletionV4Admission.packageRequest
    config ground source prepared
  let .ok header := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, wanted⟩ : PackedEffectRequest)
    | return .error "current package observation signing key unavailable"
  let packageSlot : SigningSlot :=
    ⟨9, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩
  let plan : Plan := ⟨source.canonicalBytes, invocation, packageSlot⟩
  if header.keyId != pin.managementKeyId then
    return .error "retry completion signer differs from operator key pin"
  match fixedHeaders pin invocation with
  | .error detail => return .error detail
  | .ok _ => pure ()
  return .ok plan

private def planKeys (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) : Option DurableView.Keys := do
  let begin ← ApplicationLifecycleRetryBeginV4Ingress.codec.decode request.beginBytes
  let claim ← ApplicationLifecycleRetryClaimV4Ingress.codec.decode request.claimIngressBytes
  let physical ← ApplicationLifecycleRetryCompletionV4Report.signedCodec.decode request.signedReportBytes
  let appCell ← cellAtOn ground pin.app
  let packageCell ← cellAtOn ground pin.packageManifest
  let atomBefore ← ApplicationLifecycleRetryCompletionV4Admission.packageAtom
      config.deployment.domain pin.packageManifest pin.app packageCell
  let source : ApplicationLifecycleRetryCompletionV4Source.Source :=
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
  return ApplicationLifecycleRetryCompletionV4Admission.keys config
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      source := source
      signed := ⟨[], [], [], []⟩
      packageObservationEnvelope := [] }

def prepareRequestLight (config : Config) (light : NativeHostLight.Light config) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical retry completion operator request"
  let cells ← match ← light.basis ⟨[], []⟩ with
    | .error detail => return .error detail
    | .ok basis => pure basis
  let keys := (planKeys config (.ofBasis cells) pin request).getD ⟨[], []⟩
  match ← light.basis keys with
  | .error detail => return .error detail
  | .ok basis =>
      prepareOn config (.ofBasis basis) (light.opening.reader config.transport ResourceBirthCodec.rootBytes)
        pin request

inductive LightResult where
  | confirmed (kind : DurableReceiverIO.Confirmation) (transactionId : Digest)
      (eventId : Digest)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLight (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) : IO LightResult := do
  let some ingress := ApplicationLifecycleRetryCompletionV4Ingress.codec.decode bytes
    | return .rejected "noncanonical retry completion ingress"
  let grounded ← match ← light.groundedVia transport
      (ApplicationLifecycleRetryCompletionV4Admission.keys config ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let conditional ← match ← ApplicationLifecycleRetryCompletionV4Admission.prepareConditional config reader
      grounded ingress with
    | .error detail => return .rejected detail
    | .ok conditional => pure conditional
  let intent := ApplicationLifecycleRetryCompletionV4Core.intent conditional
  match grounded.ground.recorded intent.transactionId with
  | none => return .rejected "retry completion transaction identity undeclared"
  | some (some _) => return .rejected "retry completion transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening intent with
      | .appended kind next _ _ _ _ =>
          adopt next none
          return .confirmed kind intent.transactionId intent.event.eventId
      | .replayed _ => return .rejected "retry completion transaction identity already used"
      | .rejected _ => return .rejected "durable retry completion refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- Op71 (v4 frame) only inserts detached Ed25519 signatures into the exact
op70 plan. Op38 rechecks the current tip, historical retry claim, physical
report, and all authorization. No client-modified plan becomes an authority. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  unless signatures.length == invocationCount + 1 do
    throw "retry completion signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "retry completion plan is not a management invocation"
  let some source := ApplicationLifecycleRetryCompletionV4Source.codec.decode plan.sourceBytes
    | throw "noncanonical retry completion plan source"
  unless source.valid &&
      plan.invocation.domain == source.originalBegin.begin.base.domain &&
      plan.invocation.semantics == source.originalBegin.begin.base.semantics &&
      plan.invocation.finalizedDraft == .invoke
        (DeclaredResourceController.commandCodec.encode
          (source.command plan.invocation.domain plan.invocation.semantics)) do
    throw "retry completion plan differs from source-derived command"
  let some packageHeader := CredentialSignedEnvelopeController.headerCodec.decode
      plan.packageObservationSlot.header
    | throw "noncanonical package observation header"
  let some packageSignature := signatures[invocationCount]?
    | throw "missing package observation signature"
  unless packageSignature.length == 64 do
    throw "package observation signature must be 64 bytes"
  let packageEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨packageHeader, packageSignature⟩
  return ApplicationLifecycleRetryCompletionV4Ingress.codec.encode
    { domain := plan.invocation.domain
      semantics := plan.invocation.semantics
      source := source
      signed := signedCommand
      packageObservationEnvelope := packageEnvelope }

end Minidregg.Host.ApplicationLifecycleRetryCompletionV4Authoring
