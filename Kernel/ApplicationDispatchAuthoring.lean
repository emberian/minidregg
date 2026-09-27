/-
Detached, source-owned authoring for one special application dispatch. A fixed
participant custodian selects its admitted ticket and submits exact HTTP bytes;
this module derives current image roots, identity, permissions, command and
all signing headers. Assembly only inserts detached signatures. The native
op34 receiver still checks the whole result against a fresh verified tip.
-/
import Kernel.NativeHost
import Kernel.ApplicationDispatchAdmission
import Kernel.ApplicationDispatchHistoricalCore

namespace Minidregg.Kernel.ApplicationDispatchAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchCommand
open Minidregg.Kernel.ApplicationDispatchAdmissionIngress

set_option autoImplicit false

/-- These are custodian-fixed resource and capability selectors. There is no
caller-supplied subject, principal, permission bitset, root or issue bytes. -/
structure Request where
  issueIndex : Nat
  ticketResource : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  sessionObserveCapability : CapabilityId
  manifestObserveCapability : CapabilityId
  enrollmentObserveCapability : CapabilityId
  http : ApplicationDispatchCodec.Request
  deriving DecidableEq

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
                  ApplicationDispatchCodec.requestStream)))))))
    (fun request => (request.issueIndex, request.ticketResource,
      request.packageManifest, request.snapshotManifest,
      request.sessionObserveCapability, request.manifestObserveCapability,
      request.enrollmentObserveCapability, request.http))
    (fun (issueIndex, ticketResource, packageManifest, snapshotManifest,
          sessionObserveCapability, manifestObserveCapability,
          enrollmentObserveCapability, http) =>
      ⟨issueIndex, ticketResource, packageManifest, snapshotManifest,
        sessionObserveCapability, manifestObserveCapability,
        enrollmentObserveCapability, http⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed "DREGG/APPLICATION/DISPATCH-AUTHOR-REQUEST/v1".toUTF8.toList
    requestStream

theorem request_decode_encode (request : Request) :
    requestCodec.decode (requestCodec.encode request) = some request :=
  requestCodec.decode_encode request

structure Plan where
  request : Request
  unsignedIngress : List UInt8
  invocation : SigningPlan
  observationSlots : List SigningSlot

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product bytesStream
        (StreamCodec.product signingPlanStream
          (StreamCodec.list signingSlotStream))))
    (fun plan => (plan.request, plan.unsignedIngress,
      plan.invocation, plan.observationSlots))
    (fun (request, unsignedIngress, invocation, observationSlots) =>
      ⟨request, unsignedIngress, invocation, observationSlots⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  NativeHostCodec.framed "DREGG/APPLICATION/DISPATCH-AUTHOR-PLAN/v1".toUTF8.toList
    planStream

theorem plan_decode_encode (plan : Plan) :
    planCodec.decode (planCodec.encode plan) = some plan :=
  planCodec.decode_encode plan

private def cellAt (config : Config) (opened : Opened config) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match opened.directory.directory.slots resource with
  | .present cell => some cell
  | _ => none

private def sessionState (session : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrainSession.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page ← DeclaredEffectPageMaterializer.pageAt payload.logical
      ApplicationGrainSession.readState session page
  | _ => none

private def observationSlot (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩ opened.durable
      (command ingress.dispatch selection ingress.parent))
    (index resource : Nat) (capability : CapabilityId) (root : Digest) :
    Except String SigningSlot := do
  let wanted := ApplicationDispatchAdmission.observationRequest config.deployment
    config.profile ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    opened.durable ingress selection prepared resource capability root
  let header ← (CredentialSignatureAdmission.signingHeader
    prepared.authority.snapshot
    (ApplicationDispatchAdmission.observationMarker ingress selection)
    (⟨.object, wanted⟩ : PackedEffectRequest)).mapError
      (fun _ => "dispatch observation signing key unavailable")
  pure ⟨9, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

/-- Shared construction for a source-selected human or agent parent. A caller
can only obtain unsigned signing headers here; the special receiver will
check the parent against the actual current cell, capability and policy. -/
def prepareWithParent (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request)
    (parent : Option ApplicationDispatchCommand.Parent) :
    Except String Plan := do
  let opened := verified.opened
  let some prior := verified.issues.find? (fun issue => issue.index == request.issueIndex)
    | throw "admitted share issue index unavailable"
  let spec := prior.evidence.ingress.spec
  if spec.ticket.resource != request.ticketResource then
    throw "custodian ticket differs from admitted issue"
  let ticket := spec.ticket
  if !ApplicationDispatchCommand.parentMatches ticket.participant.origin parent then
    throw "dispatch parent differs from admitted ticket origin"
  if !ApplicationDispatchAdmission.requestSafe request.http then
    throw "unsupported or unsafe HTTP request shape"
  let appResource := ticket.scope.app
  let sessionResource := ticket.participant.session
  let appCell ← NativeHost.need "current app cell unavailable" (cellAt config opened appResource)
  let actualApp ← NativeHost.need "current app state unavailable"
    (ApplicationDispatchAdmission.appState appResource appCell)
  let manifestCell ← NativeHost.need "current package manifest unavailable"
    (cellAt config opened request.packageManifest)
  let manifest ← NativeHost.need "installed package manifest unavailable"
    (ApplicationDispatchAdmission.installedManifest config.deployment.domain
      request.packageManifest appResource actualApp.packageVersion manifestCell)
  let interface ← NativeHost.need "ticket interface missing from manifest"
    (manifest.select ticket.scope.interfaceId)
  let sessionCell ← NativeHost.need "current session cell unavailable"
    (cellAt config opened sessionResource)
  let actualSession ← NativeHost.need "current session state unavailable"
    (sessionState sessionResource sessionCell)
  let enrollmentResource := ticket.participant.descriptorResource
  let enrollmentCell ← NativeHost.need "current enrollment cell unavailable"
    (cellAt config opened enrollmentResource)
  let enrollment ← NativeHost.need "installed enrollment unavailable"
    (ApplicationDispatchAdmission.installedEnrollment config.deployment.domain
      enrollmentResource sessionResource actualSession.generation enrollmentCell)
  let ticketCell ← NativeHost.need "current ticket cell unavailable"
    (cellAt config opened ticket.resource)
  let currentTicket ← NativeHost.need "installed share ticket unavailable"
    (ApplicationDispatchAdmission.installedTicket config.deployment.domain
      ticket.resource ticketCell)
  if currentTicket != ticket then throw "installed share ticket differs from admitted issue"
  let requested ← NativeHost.need "enrollment role unresolved"
    (interface.schema.resolve enrollment.role)
  let ceiling ← NativeHost.need "share ceiling unresolved"
    (interface.schema.resolve ticket.ceiling)
  if !ApplicationDispatchAuthority.withinCeilingCheck requested ceiling then
    throw "enrollment permissions exceed issued ceiling"
  let dispatch : Dispatch :=
    { app :=
        { resource := appResource, packageManifest := request.packageManifest
          generation := actualApp.generation, packageVersion := actualApp.packageVersion
          snapshotVersion := actualApp.snapshotVersion, packageRoot := manifest.packageRoot
          manifestRoot := manifestCell.payload.root, interfaceId := interface.id
          interfaceVersion := interface.version, interfaceRoot := interface.root
          capability := ticket.participant.appObserveCapability }
      session :=
        { kind := ticket.participant.kind, resource := sessionResource
          appResource := appResource, appGeneration := actualSession.appGeneration
          generation := actualSession.generation, subject := ticket.participant.subject
          capability := ticket.participant.sessionCapability
          origin := ticket.participant.origin }
      identity :=
        { principal := ApplicationDispatchAdmission.principalFor config.deployment.domain
            appResource ticket.participant.subject
          permissionSchemaRoot := interface.schema.root
          permissionBits := ApplicationPermissionSchema.bitsToNat requested }
      request := request.http }
  let base : ApplicationDispatchIngress.Ingress :=
    { domain := config.deployment.domain, semantics := config.profile.semantics
      dispatch := dispatch, signed := ⟨[], [], [], []⟩
      appRoot := appCell.payload.root
      appObserveCapability := ticket.participant.appObserveCapability
      appObservationEnvelope := []
      manifestObserveCapability := request.manifestObserveCapability
      manifestObservationEnvelope := []
      enrollmentResource := enrollmentResource
      enrollmentRoot := enrollmentCell.payload.root
      enrollmentObserveCapability := request.enrollmentObserveCapability
      enrollmentObservationEnvelope := [] }
  let unsigned : ApplicationDispatchAdmissionIngress.Ingress :=
    { dispatch := base, appSnapshotManifest := request.snapshotManifest
      appManagementSubject := spec.issuer, parent := parent
      ticketRoot := ticketCell.payload.root
      ticketObserveCapability := ticket.participant.ticketObserveCapability
      ticketObservationEnvelope := []
      issueIngressBytes := ApplicationShareIssueSource.ingressCodec.encode
        prior.evidence.ingress }
  let selection : Selection :=
    ⟨opened.authority.snapshot.cell.root, sessionCell.payload.root,
      request.sessionObserveCapability⟩
  let command := ApplicationDispatchCommand.command base selection parent
  let .ok prepared := DeclaredResourceController.prepare config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    opened.durable command
    | throw "current dispatch invocation preparation refused"
  if ApplicationDispatchAdmission.selectedMeaning unsigned spec actualApp manifest
      enrollment currentTicket != some requested then
    throw "current app, ticket, enrollment or permission meaning differs"
  if !ApplicationDispatchAdmission.linkedCurrentPolicies config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.durable unsigned spec selection prepared then
    throw "current app/session/ticket policy linkage refused"
  if !ApplicationDispatchAdmission.issuerLineageCurrent config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.durable unsigned spec selection prior.evidence.descriptor prepared then
    throw "current issuer delegation lineage refused"
  let invocation ← NativeHost.prepareLoaded config opened
    (.invoke (DeclaredResourceController.commandCodec.encode command))
  if invocation.finalizedDraft !=
      .invoke (DeclaredResourceController.commandCodec.encode command) then
    throw "dispatch invocation plan differs from current source"
  let appSlot ← observationSlot config opened unsigned selection prepared 0
    appResource ticket.participant.appObserveCapability base.appRoot
  let manifestSlot ← observationSlot config opened unsigned selection prepared 1
    request.packageManifest request.manifestObserveCapability dispatch.app.manifestRoot
  let enrollmentSlot ← observationSlot config opened unsigned selection prepared 2
    enrollmentResource request.enrollmentObserveCapability base.enrollmentRoot
  let ticketSlot ← observationSlot config opened unsigned selection prepared 3
    ticket.resource ticket.participant.ticketObserveCapability unsigned.ticketRoot
  pure ⟨request, unsigned.canonicalBytes, invocation,
    [appSlot, manifestSlot, enrollmentSlot, ticketSlot]⟩

/-- The public human authoring route remains human-only with the same exact
request/plan wire. Agent tickets require a separately source-derived parent
from `ApplicationDispatchAgentAuthoring`, never a human principal fallback. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request) :
    Except String Plan := do
  let some prior := verified.issues.find? (fun issue => issue.index == request.issueIndex)
    | throw "admitted share issue index unavailable"
  if prior.evidence.ingress.spec.ticket.participant.origin != .human then
    throw "agent dispatch authoring requires an explicit parent plan"
  prepareWithParent config verified request none

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical dispatch authoring request"
  prepareVerified config verified request

/-- Invocation slots precede the four independent observation slots. A
decoded or client-modified plan has no authority; op34 re-admits the final
wrapper against its current verified tip. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let invocationCount := plan.invocation.slots.length
  if plan.observationSlots.length != 4 ||
      signatures.length != invocationCount + 4 then
    throw "dispatch signature count mismatch"
  let signed ← NativeHost.assemble plan.invocation
    (signatures.take invocationCount)
  let signedCommand ← match signed with
    | .invoke value => pure value
    | _ => throw "dispatch plan is not an invocation"
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode
      plan.unsignedIngress
    | throw "noncanonical unsigned dispatch ingress"
  if signedCommand.commandBytes !=
      (match plan.invocation.finalizedDraft with
        | .invoke bytes => bytes
        | _ => []) then
    throw "dispatch invocation differs from source plan"
  let observations ← ((plan.observationSlots.zip
    (signatures.drop invocationCount))).mapM fun (slot, signature) => do
      if signature.length != 64 then throw "dispatch observation signature must be 64 bytes"
      let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
        | throw "noncanonical dispatch observation signing header"
      pure (CredentialSignedEnvelopeController.envelopeCodec.encode ⟨header, signature⟩)
  let some appEnvelope := observations[0]? | throw "missing app observation"
  let some manifestEnvelope := observations[1]? | throw "missing manifest observation"
  let some enrollmentEnvelope := observations[2]? | throw "missing enrollment observation"
  let some ticketEnvelope := observations[3]? | throw "missing ticket observation"
  let base : ApplicationDispatchIngress.Ingress :=
    { domain := unsigned.dispatch.domain
      semantics := unsigned.dispatch.semantics
      dispatch := unsigned.dispatch.dispatch
      signed := signedCommand
      appRoot := unsigned.dispatch.appRoot
      appObserveCapability := unsigned.dispatch.appObserveCapability
      appObservationEnvelope := appEnvelope
      manifestObserveCapability := unsigned.dispatch.manifestObserveCapability
      manifestObservationEnvelope := manifestEnvelope
      enrollmentResource := unsigned.dispatch.enrollmentResource
      enrollmentRoot := unsigned.dispatch.enrollmentRoot
      enrollmentObserveCapability := unsigned.dispatch.enrollmentObserveCapability
      enrollmentObservationEnvelope := enrollmentEnvelope }
  pure (ApplicationDispatchAdmissionIngress.codec.encode
    { unsigned with dispatch := base, ticketObservationEnvelope := ticketEnvelope })

end Minidregg.Kernel.ApplicationDispatchAuthoring
