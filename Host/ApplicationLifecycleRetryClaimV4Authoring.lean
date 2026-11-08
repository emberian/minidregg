/-
Operator-private current-image signing plan for a versioned retry CLAIM.
The requested index names a retry BEGIN-v4 in the same verified replay history.
The request never supplies an app state, resource root, grant, header, or the
recovery selector: the selector is the one retained in the admitted BEGIN-v4.
-/
module

public import Host.ApplicationLifecycleClaimOperator
public import Kernel.ApplicationLifecycleRetryClaimV4Core
public import Kernel.ApplicationLifecycleRetryClaimV4Projection
public import Kernel.NativeHostReplay

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

private def cellAtOn {deployment : CanonicalCellRegistry.Deployment} (ground : ServedBasis.Ground deployment)
    (resource : Nat) : Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
  | .present cell => some cell
  | .absent => none

private def fixedHeader (pin : Pin) (slot : SigningSlot) : Except String Unit := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
    | throw "noncanonical retry claim signing header"
  unless header.keyId == pin.managementKeyId do
    throw "retry claim signer differs from operator key pin"

private def sourceOn (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) (index : Nat) :
    Except String (ApplicationLifecycleClaim.Source ×
      PackedCell CanonicalCellRegistry.registry × PackedCell CanonicalCellRegistry.registry) := do
  let beginSource := begin.begin.base.source
  unless beginSource.app == pin.app &&
      beginSource.packageManifest == pin.packageManifest &&
      beginSource.subject.value == pin.managementSubject &&
      beginSource.managementSubject.value == pin.managementSubject &&
      beginSource.capability == pin.appCapability do
    throw "historical retry BEGIN differs from fixed claim operator pin"
  unless begin.shape && ApplicationLifecycleResidentProfile.beginMatchesV3 config.storeIdentity begin.begin do
    throw "historical retry BEGIN is outside resident host profile"
  let some appCell := cellAtOn ground pin.app
    | throw "current retry claim app cell unavailable"
  let some packageCell := cellAtOn ground pin.packageManifest
    | throw "current retry claim package cell unavailable"
  unless packageCell.kind == .content do
    throw "current retry claim package is not a content resource"
  let some before := ApplicationLifecycleClaimCurrent.appState pin.app appCell
    | throw "current retry claim app state unavailable"
  let source : ApplicationLifecycleClaim.Source :=
    { begin := begin.begin.base
      originalIndex := index
      before := before
      currentAppRoot := appCell.payload.root
      currentPackageRoot := packageCell.payload.root
      currentWorldRoot := ground.worldRoot
      appObserveCapability := pin.appObserveCapability
      packageObserveCapability := pin.packageObserveCapability
      queryNonce := request.queryNonce }
  unless source.valid do throw "current app is not at original pending retry BEGIN state"
  return (source, appCell, packageCell)

private def planKeys (config : Config) (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress)
    (source : ApplicationLifecycleClaim.Source) : DurableView.Keys :=
  let current := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics
    (ApplicationLifecycleClaim.command config.deployment.domain config.profile.semantics source)
  let retry := ApplicationFailedCreateRetryEvidence.keys begin.retry
  ⟨current.transactions ++ retry.transactions, current.nullifiers ++ retry.nullifiers⟩

private def prepareOn (config : Config) (ground : ServedBasis.Ground config.deployment) (pin : Pin)
    (request : Request) (begin : ApplicationLifecycleRetryBeginV4Ingress.Ingress) (index : Nat)
    (originalReceipt : NativeHostCodec.Receipt) : Except String Plan := do
  let (source, appCell, packageCell) ← sourceOn config ground pin request begin index
  unless ApplicationFailedCreateRetryEvidence.markersCurrent config ground begin.retry do
    throw "retry CLAIM first/created/recovery/one-use token markers refuse"
  let command := ApplicationLifecycleClaim.command config.deployment.domain
    config.profile.semantics source
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, config.genesisHeight + ground.height⟩
  let .ok prepared := DeclaredResourceController.prepare config.deployment
      config.profile ambient ground command
    | throw "current retry claim command preparation refused"
  unless ApplicationLifecycleClaimCurrent.linkedCurrentPolicy config.deployment
      config.profile ambient ground source prepared do
    throw "current retry claim app/package law differs"
  unless decide (DeclaredResourceController.PhysicalShape prepared) do
    throw "current retry claim physical shape refused"
  let context := DeclaredResourceController.readContext prepared
  let marker := DeclaredResourceController.operationMarker config.deployment.domain
    config.profile.semantics command
  let appWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient ground source prepared pin.app
    pin.appObserveCapability source.currentAppRoot
  let .ok appSelected := ResourceObservationAdmission.prepare context config.profile
      appWanted marker pin.appObserveCapability source.canonicalBytes
    | throw "current retry claim app observation preparation refused"
  unless CanonicalCellRegistry.cellCodec.encode appSelected.observed.before ==
      CanonicalCellRegistry.cellCodec.encode appCell do
    throw "retry claim app observation differs from current image"
  let packageWanted := ApplicationLifecycleClaimCurrent.observationRequest config.deployment
    config.profile ambient ground source prepared pin.packageManifest
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
  let .ok invocation := NativeHost.prepareInvokeOn config ground (config.genesisHeight + ground.height) commandBytes
    | throw "current retry claim invocation plan refused"
  unless invocation.finalizedDraft == .invoke commandBytes do
    throw "retry claim invocation plan differs from source"
  let .ok appHeader := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, appWanted⟩ : PackedEffectRequest)
    | throw "current retry claim app observation signing key unavailable"
  let .ok packageHeader := CredentialSignatureAdmission.signingHeader
      ground.authority marker (⟨.object, packageWanted⟩ : PackedEffectRequest)
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

def prepareRequestLight (config : Config) (light : NativeHostLight.Light config) (pin : Pin)
    (bytes : List UInt8) : IO (Except String Plan) := do
  let some request := requestCodec.decode bytes
    | return .error "noncanonical retry claim operator request"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let read ← match ← reader.atHeight (request.originalIndex + 1) with
    | .error refusal => return .error refusal.message
    | .ok read => pure read
  let some begin := ApplicationLifecycleRetryBeginV4Ingress.codec.decode (NativeHostReplay.sourceBytes read.record)
    | return .error "original retry BEGIN-v4 absent from verified history"
  let original ← match ← NativeHistorySelection.select config reader light.opening.head.height
      request.originalIndex (ApplicationLifecycleRetryBeginV4Admission.keys begin) with
    | .error detail => return .error detail
    | .ok original => pure original
  let originalAccepted ← match ← ApplicationLifecycleRetryBeginV4Admission.admitNative
      config reader original.grounded begin with
    | .error detail => return .error detail
    | .ok accepted => pure accepted
  match NativeHistorySelection.matchIntent original originalAccepted.intent with
  | .error detail => return .error detail
  | .ok _ =>
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

structure LightReservation (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  conditional : ApplicationLifecycleRetryClaimV4Core.Conditional config opening.head grounded.ground ingress
  fresh : grounded.ground.recorded conditional.intent.transactionId = some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record =
    DurableCheckpointCodec.recordFrame.encode (DurableReceiver.IntentRecord.ofIntent conditional.intent)
  freshCasWinner : Bool

def LightReservation.receipt {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (reservation : LightReservation config opening) : NativeHostCodec.Receipt :=
  ⟨reservation.conditional.intent.transactionId, reservation.conditional.intent.event.eventId,
    reservation.next.head.height, reservation.next.served.worldRoot⟩

def LightReservation.projection {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (reservation : LightReservation config opening) : ApplicationLifecycleRetryClaimV4Projection.Committed :=
  let source := reservation.ingress.base.source
  let served := reservation.next.served
  { core :=
      { source := source
        originalTransaction := reservation.conditional.original.record.transactionId
        originalEvent := reservation.conditional.original.record.event.eventId
        originalNullifier :=
          (ApplicationLifecycleBegin.stableNullifier config.deployment.domain
            config.profile.semantics source.begin.source).nullifierId
        claimReceipt := reservation.receipt
        claimNullifier :=
          (ApplicationLifecycleClaim.stableNullifier config.deployment.domain
            config.profile.semantics source).nullifierId
        appPhysicalRoot := served.roots ⟨source.begin.source.app⟩
        packagePhysicalRoot := served.roots ⟨source.begin.source.packageManifest⟩
        authorityPhysicalRoot := served.roots ⟨config.deployment.authorityCellId⟩
        postWorldRoot := reservation.receipt.worldRoot }
    originalClaim := reservation.ingress }

def LightReservation.withFreshTip {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    {α : Type} (reservation : LightReservation config opening) (transport : DurableReceiverIO.Transport)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  unless reservation.kind == .installed && reservation.freshCasWinner do
    return .error "retry claim was not freshly installed"
  let .ok current ← DurableReceiverIO.tipIs transport reservation.next.head.height reservation.entry
    | return .error "retry claim physical tip unavailable before handoff"
  if current then
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "retry claim physical tip changed before handoff"

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | reserved (reservation : LightReservation config opening)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLight (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt light.opening := fun _ _ _ _ => pure ()) :
    IO (LightResult config light.opening) := do
  let some ingress := ApplicationLifecycleRetryClaimV4Ingress.codec.decode bytes
    | return .rejected "noncanonical retry claim ingress"
  let grounded ← match ← light.groundedVia transport (ApplicationLifecycleRetryClaimV4Core.keys ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let conditional ← match ← ApplicationLifecycleRetryClaimV4Core.prepare config reader grounded ingress with
    | .error detail => return .rejected s!"retry BEGIN absent or current retry claim authority refused: {detail}"
    | .ok conditional => pure conditional
  match fresh : grounded.ground.recorded conditional.intent.transactionId with
  | none => return .rejected "retry claim transaction identity undeclared"
  | some (some _) => return .rejected "retry claim transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
          conditional.intent with
      | .appended kind next height entry entryExact freshCasWinner moved =>
          adopt next _ moved none
          return .reserved ⟨ingress, grounded, conditional, fresh, kind, next, height, entry, entryExact,
            freshCasWinner⟩
      | .replayed _ => return .rejected "retry claim transaction identity already used"
      | .rejected _ => return .rejected "durable retry claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

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
