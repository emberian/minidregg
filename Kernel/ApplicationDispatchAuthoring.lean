module

public import Compiler.CarriedDispatchProvenance
public import Kernel.NativeHost
public import Kernel.ApplicationDispatchAdmission
public import Kernel.ApplicationAgentLifetimeGrantReceiver

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

private def cellAt {config : Config} (ground : ServedBasis.Ground config.deployment) (resource : Nat) :
    Option (PackedCell CanonicalCellRegistry.registry) :=
  match ground.directory.slots resource with
  | .present cell => some cell
  | _ => none

private def sessionState (session : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrainSession.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page := payload.logical
      ApplicationGrainSession.readState session page
  | _ => none

/-- Source-derived unsigned observation header at one prepared dispatch tip.
It grants no authority by itself; the special receiver checks its detached
signature, current law, exact old root and immutable request context. -/
def observationSlotOn (config : Config) (ground : ServedBasis.Ground config.deployment)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, config.genesisHeight + ground.height⟩ ground
      (command ingress.dispatch selection ingress.parent))
    (index resource : Nat) (capability : CapabilityId) (root : Digest) :
    Except String SigningSlot := do
  let wanted := ApplicationDispatchAdmission.observationRequest config.deployment
    config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
    ground ingress selection prepared resource capability root
  let header ← (CredentialSignatureAdmission.signingHeader
    ground.authority
    (ApplicationDispatchAdmission.observationMarker ingress selection)
    (⟨.object, wanted⟩ : PackedEffectRequest)).mapError
      (fun _ => "dispatch observation signing key unavailable")
  pure ⟨9, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

def prepareObservationSlot (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩ opened.ground
      (command ingress.dispatch selection ingress.parent))
    (index resource : Nat) (capability : CapabilityId) (root : Digest) :
    Except String SigningSlot :=
  observationSlotOn config opened.ground ingress selection prepared index resource capability root

/- Shared signing-header construction after a source-specific route has
selected a verified historical issue and parent. This is private because a
raw Parent alone is not lifetime authorization. Both public wrappers below
apply their distinct historical/current parent checks first. -/
private def constructPlan (config : Config) (cells : ServedBasis.Ground config.deployment)
    (request : Request) (spec : ApplicationShareIssueSource.Spec)
    (issueIngressBytes originalSourceBytes : List UInt8)
    (parent : Option ApplicationDispatchCommand.Parent) :
    Except String (DeclaredResourceController.Command ×
      (ServedBasis.Ground config.deployment → Except String Plan)) := do
  if spec.ticket.resource != request.ticketResource then
    throw "custodian ticket differs from admitted issue"
  let ticket := spec.ticket
  if !ApplicationDispatchAdmission.requestSafeFor (ticket.participant.origin == .human)
      request.http then
    throw "unsupported or unsafe HTTP request shape"
  let appResource := ticket.scope.app
  let sessionResource := ticket.participant.session
  let appCell ← NativeHost.need "current app cell unavailable" (cellAt (config := config) cells appResource)
  let actualApp ← NativeHost.need "current app state unavailable"
    (ApplicationDispatchAdmission.appState appResource appCell)
  let manifestCell ← NativeHost.need "current package manifest unavailable"
    (cellAt (config := config) cells request.packageManifest)
  let manifest ← NativeHost.need "installed package manifest unavailable"
    (ApplicationDispatchAdmission.installedManifest config.deployment.domain
      request.packageManifest appResource actualApp.packageVersion manifestCell)
  let interface ← NativeHost.need "ticket interface missing from manifest"
    (manifest.select ticket.scope.interfaceId)
  let sessionCell ← NativeHost.need "current session cell unavailable"
    (cellAt (config := config) cells sessionResource)
  let actualSession ← NativeHost.need "current session state unavailable"
    (sessionState sessionResource sessionCell)
  let enrollmentResource := ticket.participant.descriptorResource
  let enrollmentCell ← NativeHost.need "current enrollment cell unavailable"
    (cellAt (config := config) cells enrollmentResource)
  let enrollment ← NativeHost.need "installed enrollment unavailable"
    (ApplicationDispatchAdmission.installedEnrollment config.deployment.domain
      enrollmentResource sessionResource actualSession.generation enrollmentCell)
  let ticketCell ← NativeHost.need "current ticket cell unavailable"
    (cellAt (config := config) cells ticket.resource)
  let currentTicket ← NativeHost.need "installed share ticket unavailable"
    (ApplicationDispatchAdmission.installedTicket config.deployment.domain
      ticket.resource ticketCell)
  if currentTicket != ticket then throw "installed share ticket differs from admitted issue"
  -- A restart moves the app to a new serving generation and the participant renews its own
  -- (participant-signed) enrollment; name the stale case instead of the generic meaning refusal.
  if enrollment.appGeneration != actualApp.generation then
    throw s!"session enrollment names app generation {enrollment.appGeneration} but the app now serves generation {actualApp.generation}: renew it with `mini apps renew --grain <grain>` (a restart starts a new generation)"
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
      issueIngressBytes := issueIngressBytes }
  let selection : Selection :=
    ⟨sessionCell.payload.root, request.sessionObserveCapability⟩
  let command := ApplicationDispatchCommand.command base selection parent
  return (command, fun ground => do
    let .ok prepared := DeclaredResourceController.prepare config.deployment config.profile
      ⟨config.federation, config.genesisHeight + ground.height⟩
      ground command
      | throw "current dispatch invocation preparation refused"
    if ApplicationDispatchAdmission.selectedMeaning unsigned spec actualApp manifest
        enrollment currentTicket != some requested then
      throw "current app, ticket, enrollment or permission meaning differs"
    if let some clause := ApplicationDispatchAdmission.firstFailedLinkageClause config.deployment
        config.profile ⟨config.federation, config.genesisHeight + ground.height⟩
        ground unsigned spec selection prepared then
      throw s!"current app/session/ticket policy linkage refused: {clause}"
    if !ApplicationDispatchAdmission.issuerLineageCurrentFromSourceBytes config.deployment config.profile
        ⟨config.federation, config.genesisHeight + ground.height⟩
        ground unsigned spec selection originalSourceBytes prepared then
      throw "current issuer delegation lineage refused"
    let invocation ← NativeHost.prepareInvokeOn config ground (config.genesisHeight + ground.height)
      (DeclaredResourceController.commandCodec.encode command)
    if invocation.finalizedDraft !=
        .invoke (DeclaredResourceController.commandCodec.encode command) then
      throw "dispatch invocation plan differs from current source"
    let appSlot ← observationSlotOn config ground unsigned selection prepared 0
      appResource ticket.participant.appObserveCapability base.appRoot
    let manifestSlot ← observationSlotOn config ground unsigned selection prepared 1
      request.packageManifest request.manifestObserveCapability dispatch.app.manifestRoot
    let enrollmentSlot ← observationSlotOn config ground unsigned selection prepared 2
      enrollmentResource request.enrollmentObserveCapability base.enrollmentRoot
    let ticketSlot ← observationSlotOn config ground unsigned selection prepared 3
      ticket.resource ticket.participant.ticketObserveCapability unsigned.ticketRoot
    pure ⟨request, unsigned.canonicalBytes, invocation,
      [appSlot, manifestSlot, enrollmentSlot, ticketSlot]⟩)

private def prepareForIssue (config : Config) (opened : Opened config)
    (request : Request) (spec : ApplicationShareIssueSource.Spec)
    (issueIngressBytes originalSourceBytes : List UInt8)
    (parent : Option ApplicationDispatchCommand.Parent) : Except String Plan := do
  let (_, finish) ← constructPlan config opened.ground request spec issueIngressBytes originalSourceBytes parent
  finish opened.ground

private def prepareForSelectedIssue (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request)
    (prior : NativeHostReplay.PriorIssue config)
    (parent : Option ApplicationDispatchCommand.Parent) :
    Except String Plan :=
  prepareForIssue config verified.opened request prior.evidence.spec prior.evidence.ingressBytes
    (ApplicationShareIssueSource.sourceBytes prior.evidence.spec prior.evidence.descriptor) parent

/-- The v1/v2 authoring surface retains its exact original-generation rule
and bytes. An agent session cannot use this wrapper after a hard reconnect. -/
def prepareWithParent (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request)
    (parent : Option ApplicationDispatchCommand.Parent) :
    Except String Plan := do
  let some prior := verified.issues.find? (fun issue => issue.index == request.issueIndex)
    | throw "admitted share issue index unavailable"
  if prior.evidence.spec.ticket.resource != request.ticketResource then
    throw "custodian ticket differs from admitted issue"
  if !ApplicationDispatchCommand.parentMatches
      prior.evidence.spec.ticket.participant.origin parent then
    throw "dispatch parent differs from admitted ticket origin"
  prepareForSelectedIssue config verified request prior parent

private def lifetimeParent (config : Config) (ground : ServedBasis.Ground config.deployment)
    (request : Request) (grant : ApplicationAgentLifetimeGrant.Grant) (issueIndex : Nat)
    (spec : ApplicationShareIssueSource.Spec) (receipt : NativeHostCodec.Receipt)
    (parentTask : Nat) (parentCapability parentObserve : CapabilityId) :
    Except String ApplicationDispatchCommand.Parent := do
  if issueIndex != request.issueIndex ||
      spec.ticket.resource != request.ticketResource ||
      !grant.matchesIssued spec issueIndex receipt ||
      parentTask != grant.participant.parentTask then
    throw "lifetime grant does not certify selected ticket and parent"
  let cell ← NativeHost.need "lifetime parent cell unavailable"
    (cellAt (config := config) ground parentTask)
  let ⟨.declaredObject, payload⟩ := cell
    | throw "lifetime parent is not a grain"
  let page := payload.logical
  let state ← NativeHost.need "lifetime parent state unavailable"
    (AgentGrain.readState parentTask page)
  if !(state.status == 3 || state.status == 4) ||
      state.remaining < 0 || state.reserved < 0 then
    throw "lifetime parent is not currently reserved"
  return ⟨parentTask, state, parentCapability, payload.root, parentObserve⟩

/-- Event26 source authoring selects the grant from the same verified walk,
checks its original ticket lineage, and reads a fresh reserved parent from
the current image. This emits only unsigned signing headers; event26 later
rechecks grant, parent, capabilities, policy and physical image at admission. -/
def prepareWithLifetimeGrant (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request)
    (grantIssueIndex parentTask : Nat)
    (parentCapability parentObserve : CapabilityId) : Except String Plan := do
  let some grant := verified.grants.find? (fun prior => prior.index == grantIssueIndex)
    | throw "lifetime grant absent from admitted prefix"
  let prior := grant.ticket
  let parent ← lifetimeParent config verified.opened.ground request grant.ingress.spec.grant
    prior.index prior.evidence.spec prior.receipt parentTask parentCapability parentObserve
  prepareForSelectedIssue config verified request prior (some parent)

/-- The public human authoring route remains human-only with the same exact
request/plan wire. Agent tickets require a separately source-derived parent
from `ApplicationDispatchAgentAuthoring`, never a human principal fallback. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request) :
    Except String Plan := do
  let some prior := verified.issues.find? (fun issue => issue.index == request.issueIndex)
    | throw "admitted share issue index unavailable"
  if prior.evidence.spec.ticket.participant.origin != .human then
    throw "agent dispatch authoring requires an explicit parent plan"
  prepareWithParent config verified request none

/-- Human dispatch on a carried service retains exact old source commitments.
Agent tickets still need their separate authenticated reserve/lifetime path. -/
def prepareSuffix (config : Config) {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (request : Request) :
    ExceptT String IO Plan := do
  let (spec, issueBytes, originalSourceBytes) ←
    if request.issueIndex < anchor.durable.height then do
      let some origin := verified.origin
        | throw "old dispatch issue lacks authenticated carried origin"
      let custody ← origin.rebindChecked verified.opened.durable
      let issue ← ExceptT.mk (CarriedApplicationProvenance.selectIssue custody request.issueIndex)
      let selected ← CarriedDispatchProvenance.fromIssue issue
      pure (issue.spec, issue.ingress.canonicalBytes, selected.originalSourceBytes)
    else do
      let some prior := verified.issues.find? (fun issue => issue.index == request.issueIndex)
        | throw "target-suffix share issue index unavailable"
      pure (prior.evidence.spec, prior.evidence.ingressBytes,
        ApplicationShareIssueSource.sourceBytes prior.evidence.spec prior.evidence.descriptor)
  if spec.ticket.participant.origin != .human then
    throw "agent dispatch authoring requires an authenticated parent plan"
  if !ApplicationDispatchCommand.parentMatches spec.ticket.participant.origin none then
    throw "dispatch parent differs from admitted ticket origin"
  prepareForIssue config verified.opened request spec issueBytes originalSourceBytes none

def prepareRequestSuffix (config : Config) {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    ExceptT String IO Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical dispatch authoring request"
  prepareSuffix config verified request

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical dispatch authoring request"
  prepareVerified config verified request

private def finishIssueLight (config : Config) (light : NativeHostLight.Light config)
    (cells : ServedBasis.Ground config.deployment) (request : Request)
    (prior : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (parent : Option ApplicationDispatchCommand.Parent) : ExceptT String IO Plan := do
  let (command, finish) ← constructPlan config cells request prior.spec prior.ingressBytes
    (ApplicationShareIssueSource.sourceBytes prior.spec prior.descriptor) parent
  let keys := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics command
  let basis ← ExceptT.mk (light.basis keys)
  finish (.ofBasis basis)

def prepareForIssueLight (config : Config) (light : NativeHostLight.Light config)
    (cells : ServedBasis.Ground config.deployment) (request : Request)
    (prior : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (parent : Option ApplicationDispatchCommand.Parent) : ExceptT String IO Plan := do
  if !ApplicationDispatchCommand.parentMatches prior.spec.ticket.participant.origin parent then
    throw "dispatch parent differs from admitted ticket origin"
  finishIssueLight config light cells request prior parent

def prepareWithLifetimeGrantLight (config : Config) (light : NativeHostLight.Light config)
    {index : Nat} (grant : ApplicationAgentLifetimeGrantReceiver.Selected config light index)
    (cells : ServedBasis.Ground config.deployment) (request : Request) (parentTask : Nat)
    (parentCapability parentObserve : CapabilityId) : ExceptT String IO Plan := do
  let parent ← lifetimeParent config cells request grant.ingress.spec.grant
    grant.ingress.spec.grant.source.issueIndex grant.ticket.evidence.spec (receiptOfRecord grant.ticket.candidate.read)
    parentTask parentCapability parentObserve
  finishIssueLight config light cells request grant.ticket.evidence (some parent)

/-- All cells and history answers used for the plan belong to the refreshed light head. -/
def prepareRequestLight (config : Config) (light : NativeHostLight.Light config) (bytes : List UInt8) :
    ExceptT String IO Plan := do
  let some request := requestCodec.decode bytes | throw "noncanonical dispatch authoring request"
  let prior := (← ApplicationDispatchLight.selectIssue config light request.issueIndex).evidence
  if prior.spec.ticket.participant.origin != .human then
    throw "agent dispatch authoring requires an explicit parent plan"
  let cells ← ExceptT.mk (light.basis ⟨[], []⟩)
  prepareForIssueLight config light (.ofBasis cells) request prior none

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
