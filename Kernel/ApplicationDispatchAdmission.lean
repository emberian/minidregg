/-
Current-image selectors for special application dispatch. These helpers do not
admit a request by themselves: the receiver must check signed observations,
the DRC invocation, accepted historical share issuance, and one durable CAS.
-/
import Kernel.ApplicationDispatchAdmissionIngress
import Kernel.ApplicationDispatchManifest
import Kernel.ApplicationDispatchWitness
import Kernel.ApplicationDispatchAuthority
import Kernel.ApplicationShareIssueSource
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.ApplicationDispatchAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.IntStream (intStream)
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchCodec
open Minidregg.Kernel.ApplicationDispatchCommand
open Minidregg.Kernel.ApplicationDispatchAdmissionIngress
open Minidregg.Kernel.ApplicationShareIssueSource

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DeclaredResourceController.Durable
abbrev Ambient := DeclaredResourceController.Ambient

/-- Stable 32-byte Sandstorm-facing identity for one Mini subject within one
app. Session reconnect, ticket replacement and app wake do not change it.
Display names are never inputs to this authority identity. -/
def principalFor (domain : Digest) (app : Nat) (subject : SubjectId) : List UInt8 :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SANDSTORM-PRINCIPAL/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        TypedAuthorizationRequestCodec.subjectIdStream)).encode
      (domain, app, subject))).bytes

theorem principalFor_length (domain : Digest) (app : Nat) (subject : SubjectId) :
    (principalFor domain app subject).length = 32 := by
  simp [principalFor, Sp800185Cshake256.hash]

/-- No caller may choose app-visible identity bytes or attach a session to a
different app/generation than the selected serving app. -/
def identityMatches (ingress : ApplicationDispatchAdmissionIngress.Ingress) : Bool :=
  ingress.dispatch.dispatch.identity.principal ==
      principalFor ingress.dispatch.domain ingress.dispatch.dispatch.app.resource
        ingress.dispatch.dispatch.session.subject &&
    decide (ingress.dispatch.dispatch.session.appResource =
      ingress.dispatch.dispatch.app.resource) &&
    decide (ingress.dispatch.dispatch.session.appGeneration =
      ingress.dispatch.dispatch.app.generation)

/-- Recover only selector coordinates from the canonical signed command.
`matchesCommand` and ordinary DRC admission must then check every byte and
current old page. An absent session observation capability refuses. -/
def selectCommand (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option Selection := do
  let signed ← DeclaredResourceController.commandCodec.decode
    ingress.dispatch.signed.commandBytes
  let first ← signed.targets.head?
  let observe ← first.observeCapability
  some ⟨first.expectedTargetRoot, observe⟩

def appState (app : Nat) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrain.State := do
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page := payload.logical
      ApplicationGrain.readState app page
  | _ => none

def installedManifest (domain : Digest) (manifestResource app : Nat)
    (version : Int) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationDispatchManifest.Manifest := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationDispatchManifest.decodeInstalled domain manifestResource app version page
  | _ => none

def installedEnrollment (domain : Digest) (descriptorResource session : Nat)
    (generation : Int) (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationGrainSessionEnrollment.Enrollment := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationGrainSessionEnrollment.decodeInstalled domain descriptorResource session
        generation page
  | _ => none

def installedTicket (domain : Digest) (ticketResource : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationDispatchAuthority.Ticket := do
  match cell with
  | ⟨.content, payload⟩ =>
      let page := payload.logical
      ApplicationDispatchAuthority.decodeInstalled domain ticketResource page
  | _ => none

/-- Ordinary client headers that the physical Sandstorm adapter may map to
WebRequest context. App identity and permission headers are absent here and
must be generated from the checked projection after durable admission. -/
def ordinaryHeaderName (name : List UInt8) : Bool :=
  (["cookie", "accept", "accept-encoding", "content-type", "user-agent",
    "if-match", "if-none-match", "x-requested-with", "x-csrftoken",
    "x-csrf-token", "oc-total-length", "oc-chunk-size", "x-oc-mtime",
    "oc-fileid", "oc-chunked", "oc-checksum", "oc-chunk-offset",
    "oc-lazyops"] : List String).any (fun allowed => name == allowed.toUTF8.toList)

def cleanTransportText (bytes : List UInt8) : Bool :=
  (String.fromUTF8? bytes.toByteArray).isSome &&
    bytes.all (fun byte => byte != 0 && byte != 10 && byte != 13)

/-- The exact signed request is a bounded WebSession candidate. The received
`generated` tag is never trusted: every incoming header must be ordinary,
and the host synthesizes Sandstorm security context from checked fields.
This excludes unsafe or unsupported HTTP shapes before a pending event. -/
def requestSafe (request : ApplicationDispatchCodec.Request) : Bool :=
  let methodAllowed :=
    (["GET", "HEAD", "POST", "PUT", "PATCH", "DELETE"] : List String).any
      (fun method => request.method == method.toUTF8.toList)
  let bodyAllowed :=
    if request.method == "GET".toUTF8.toList ||
        request.method == "HEAD".toUTF8.toList ||
        request.method == "DELETE".toUTF8.toList then
      request.body.isEmpty
    else true
  methodAllowed && bodyAllowed &&
    decide (request.path.length + request.query.length ≤ 8192) &&
    decide (request.body.length ≤ 8 * 1024 * 1024) &&
    decide (request.headers.length ≤ 128) &&
    request.path.head? != some 47 &&
    !(request.path ++ request.query).contains 35 &&
    !request.path.contains 63 &&
    cleanTransportText request.path && cleanTransportText request.query &&
    request.headers.all (fun header =>
      !header.generated && ordinaryHeaderName header.name &&
      decide (header.name.length ≤ 128) &&
      decide (header.value.length ≤ 8192) &&
      cleanTransportText header.value)

/-- A separate current native observation request for each read-only resource.
The source command is the DRC session/agent witness, while the native observe
signature is bound to the current root, policy epoch and immutable context. -/
def observationRequest {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest) : Request .object :=
  let target : DeclaredResourceController.Target :=
    ⟨.object, resource, capability, 1, root, .content ⟨[]⟩, none, none, none⟩
  { DeclaredResourceController.requestFor prepared.authority.snapshot profile.semantics
      ambient (command ingress.dispatch selection ingress.parent) target root with
    verb := .observeObject }

def observationGuard (resource : Nat) (root : Digest) : ReadGuard :=
  ⟨⟨resource⟩, root⟩

/-- A signed observation names the inner payload root. A durable CAS guard
protects the complete encoded physical cell, whose root is generally distinct. -/
theorem observedPhysicalRoot_current {deployment : Deployment} {durable : Durable}
    (context : ResourceObservationAdmission.Context deployment durable)
    (resource : Nat) (packed : PackedCell CanonicalCellRegistry.registry)
    (present : context.directory.directory.slots resource = .present packed) :
    ResourceBirthCodec.physicalRoot (.live packed) =
      durable.snapshot.model.roots ⟨resource⟩ :=
  PhysicalResourceReadGuard.current context.directory resource packed present

/-- Native observation signatures bind the base signed request and the
selected issue/ticket coordinates, without including their own envelopes. -/
def observationContext (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-OBSERVATION/v1".toUTF8.toList ++
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product digestStream
            (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
              bytesStream))))).encode
      (ApplicationDispatchIngress.requestDigest ingress.dispatch,
        ingress.appSnapshotManifest, ingress.appManagementSubject,
        ingress.ticketRoot, ingress.ticketObserveCapability,
        ingress.issueIngressBytes))

def observationMarker
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection) : Nat :=
  DeclaredResourceController.operationMarker ingress.dispatch.domain
    ingress.dispatch.semantics (command ingress.dispatch selection ingress.parent)

structure CheckedRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) profile
    (observationRequest deployment profile ambient durable ingress selection prepared
      resource capability root)
    (observationMarker ingress selection) capability (observationContext ingress)
  checked : ResourceObservationAdmission.Checked selected envelope
  current : ResourceBirthCodec.physicalRoot (.live selected.observed.before) =
    durable.snapshot.model.roots ⟨resource⟩
  readonly : (observationGuard resource
    (ResourceBirthCodec.physicalRoot (.live selected.observed.before))).cellId ∉
    (DeclaredResourceController.writes prepared).map DataWrite.cellId

/-- The same checked read retains the signed inner commitment. It is not
substituted for the physical root used by the later CAS read guard. -/
theorem CheckedRead.signedInnerRoot {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {selection : Selection}
    {prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent)}
    {resource : Nat} {capability : CapabilityId} {root : Digest}
    {envelope : List UInt8}
    (read : CheckedRead deployment profile ambient durable ingress selection prepared
      resource capability root envelope) :
    root = read.selected.observed.before.payload.root :=
  ResourceObservationAdmission.preparation_actual_root read.selected

def checkRead {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent))
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) :
    IO (Except String (CheckedRead deployment profile ambient durable ingress selection
      prepared resource capability root envelope)) := do
  let wanted := observationRequest deployment profile ambient durable ingress selection
    prepared resource capability root
  let context := DeclaredResourceController.readContext prepared
  match ResourceObservationAdmission.prepare context profile wanted
      (observationMarker ingress selection) capability (observationContext ingress) with
  | .error _ => return .error "current application observation refused"
  | .ok selected =>
      match ← ResourceObservationAdmission.check native selected envelope with
      | .error _ => return .error "signed application observation refused"
      | .ok checked =>
          let current := observedPhysicalRoot_current context resource
            selected.observed.before selected.observed.present
          if readonly : (observationGuard resource
              (ResourceBirthCodec.physicalRoot (.live selected.observed.before))).cellId ∉
              (DeclaredResourceController.writes prepared).map DataWrite.cellId then
            return .ok ⟨selected, checked, current, readonly⟩
          else return .error "application observation overlaps dispatch writes"

/-- Exact meaning extracted from four current, independently observed cells.
The share ceiling is app-issued, while the participant's enrollment requests
the role. Neither the HTTP method nor a display label grants a bit. -/
def selectedMeaning (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (actualApp : ApplicationGrain.State)
    (manifest : ApplicationDispatchManifest.Manifest)
    (enrollment : ApplicationGrainSessionEnrollment.Enrollment)
    (ticket : ApplicationDispatchAuthority.Ticket) : Option (List Bool) := do
  let dispatch := ingress.dispatch.dispatch
  if !identityMatches ingress ||
      !ApplicationDispatchWitness.matchesServing dispatch actualApp ||
      !ApplicationDispatchManifest.matchesDispatch manifest dispatch ||
      ticket != spec.ticket ||
      ticket.resource == dispatch.app.resource ||
      ticket.resource == ingress.dispatch.enrollmentResource ||
      ticket.participant.ticketObserveCapability != ingress.ticketObserveCapability ||
      dispatch.app.capability != ingress.dispatch.appObserveCapability then
    none
  else
    let interface ← manifest.select dispatch.app.interfaceId
    ApplicationDispatchAuthority.eligibleBits ticket dispatch enrollment interface.schema

/-- Live dispatch requires the current v2 app law. The exact v1 law remains
available for replay re-admission at a verifier-authenticated original prefix,
but must not turn a present v1 installation into a new live permit. -/
theorem current_app_policy_excludes_v1 (package snapshot : Nat)
    (management : Minidregg.Pred.Pred) :
    ApplicationGrain.policyV1 package snapshot management ≠
      ApplicationGrain.policy package snapshot management := by
  intro equal
  have lengthEqual := congrArg
    (fun policy : Minidregg.Pred.Pred =>
      match policy with
      | .anyL alternatives => alternatives.toList.length
      | _ => 0) equal
  simp [ApplicationGrain.policyV1, ApplicationGrain.policy,
    Minidregg.Pred.Pred.any] at lengthEqual

/-- The wrapper's extra selectors are checked against source-owned current
policy records. The standard v2 app law admits `.delegateObject` only for its
current management subject, so an old issuer loses that leg when management
changes. This deliberately supports the standard application/session/ticket
policy family, not arbitrary app-revised laws. -/
def linkedCurrentPolicies {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent)) : Bool :=
  let auth := prepared.authority.snapshot.logical
  let directory := prepared.directory.directory
  let policyAt := fun target => do
    let head ← CredentialAuthorityDomain.headAt auth ⟨target⟩
    let policy ← CanonicalCellRegistry.loadPolicySource deployment.domain directory head.address
    if policy.record.policyId == ⟨target⟩ &&
        policy.record.version == head.version &&
        policy.record.semantics == profile.semantics then
      pure policy.record.predicate
    else none
  let app := ingress.dispatch.dispatch.app.resource
  let manifest := ingress.dispatch.dispatch.app.packageManifest
  let session := ingress.dispatch.dispatch.session.resource
  let descriptor := ingress.dispatch.enrollmentResource
  let kind := if ingress.dispatch.dispatch.session.kind = InterfaceKind.web then
    ApplicationGrainSession.Kind.web else ApplicationGrainSession.Kind.api
  let management := Minidregg.Pred.Pred.eq "request/subject" ingress.appManagementSubject.value
  let participant := ingress.dispatch.dispatch.session.subject
  -- The session and descriptor laws are exactly those the current session
  -- birth installs (`ApplicationGrainSessionBirth.Ready.policyRecords`):
  -- the participant manages its own session. Expecting the older no-manager
  -- law refused every dispatch for a currently born session.
  let sessionManagement := Minidregg.Pred.Pred.eq "request/subject" participant.value
  decide (spec.issuer = ingress.appManagementSubject) &&
  policyAt app == some (ApplicationGrain.policy manifest ingress.appSnapshotManifest management) &&
  policyAt manifest == some (ApplicationGrain.packageManifestPolicy app management) &&
  policyAt session == some (ApplicationGrainSession.policy descriptor kind
    participant sessionManagement) &&
  policyAt descriptor == some (ApplicationGrainSession.descriptorPolicy session kind
    participant sessionManagement) &&
  policyAt spec.ticket.resource == some (ticketPolicy spec.issuer)

/-- Issuance authenticated the issuer once. At each dispatch, the same
selected app-delegation capability must still be present with valid stored
lineage, current epochs, time window and no ancestor/channel revocation.
This is a data/current-law check; it does not pretend an old signature is a
fresh signature at the new height. The app law is separately exact-matched
by `linkedCurrentPolicies`. -/
def issuerLineageCurrent {F : Type} [Field F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (selection : Selection)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
      (command ingress.dispatch selection ingress.parent)) : Bool :=
  let snapshot := prepared.authority.snapshot
  let request := ApplicationShareIssueSource.appRequest deployment.domain profile.semantics
    ambient.federation snapshot.authState ambient.height ingress.dispatch.appRoot spec descriptor
  match CredentialAuthorityState.readCapability snapshot.cell .object spec.appDelegateCapability with
  | none => false
  | some stored =>
      CredentialAuthorityPolicyRegistry.capabilityCheck snapshot stored.head
        (CredentialAuthorityPolicyRegistry.storedCapabilityDigest snapshot stored) &&
      AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request


/-- Current-image native checks, still short of accepted historical issue
provenance and a durable special pending event. The `spec` and `descriptor`
arguments must come from a verified historical issue selector, never directly
from HTTP or the caller's ticket bytes. -/
structure CheckedCurrent {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) where
  private mk ::
  profileExact : ingress.dispatch.domain = deployment.domain ∧
    ingress.dispatch.semantics = profile.semantics
  identityExact : identityMatches ingress = true
  selection : Selection
  selectedCommand : selectCommand ingress = some selection
  signedCommand : DeclaredResourceController.Command
  decodedCommand : DeclaredResourceController.commandCodec.decode
    ingress.dispatch.signed.commandBytes = some signedCommand
  commandExact : matchesCommand ingress.dispatch selection ingress.parent signedCommand = true
  prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
    (command ingress.dispatch selection ingress.parent)
  shape : DeclaredResourceController.PhysicalShape prepared
  linked : linkedCurrentPolicies deployment profile ambient durable ingress spec selection prepared = true
  appRead : CheckedRead deployment profile ambient durable ingress selection prepared
    ingress.dispatch.dispatch.app.resource ingress.dispatch.appObserveCapability
    ingress.dispatch.appRoot ingress.dispatch.appObservationEnvelope
  manifestRead : CheckedRead deployment profile ambient durable ingress selection prepared
    ingress.dispatch.dispatch.app.packageManifest ingress.dispatch.manifestObserveCapability
    ingress.dispatch.dispatch.app.manifestRoot ingress.dispatch.manifestObservationEnvelope
  enrollmentRead : CheckedRead deployment profile ambient durable ingress selection prepared
    ingress.dispatch.enrollmentResource ingress.dispatch.enrollmentObserveCapability
    ingress.dispatch.enrollmentRoot ingress.dispatch.enrollmentObservationEnvelope
  ticketRead : CheckedRead deployment profile ambient durable ingress selection prepared
    spec.ticket.resource ingress.ticketObserveCapability ingress.ticketRoot
    ingress.ticketObservationEnvelope
  actualApp : ApplicationGrain.State
  appExact : appState ingress.dispatch.dispatch.app.resource appRead.selected.observed.before =
    some actualApp
  manifest : ApplicationDispatchManifest.Manifest
  manifestExact : installedManifest deployment.domain
    ingress.dispatch.dispatch.app.packageManifest ingress.dispatch.dispatch.app.resource
    ingress.dispatch.dispatch.app.packageVersion manifestRead.selected.observed.before =
      some manifest
  enrollment : ApplicationGrainSessionEnrollment.Enrollment
  enrollmentExact : installedEnrollment deployment.domain ingress.dispatch.enrollmentResource
    ingress.dispatch.dispatch.session.resource ingress.dispatch.dispatch.session.generation
    enrollmentRead.selected.observed.before = some enrollment
  ticket : ApplicationDispatchAuthority.Ticket
  ticketExact : installedTicket deployment.domain spec.ticket.resource
    ticketRead.selected.observed.before = some ticket
  bits : List Bool
  meaningExact : selectedMeaning ingress spec actualApp manifest enrollment ticket = some bits
  requestShape : requestSafe ingress.dispatch.dispatch.request = true
  issuerCurrent : issuerLineageCurrent deployment profile ambient durable ingress spec
    selection descriptor prepared = true
  invocation : DeclaredResourceController.AcceptedInvocation prepared ingress.dispatch.signed

/-- Only app-side identity and authorization continuity belongs in the
WebSession cache key. A DRC active witness reads the live session root on
every request; that workflow root, the HTTP request and app checkpoint
snapshot version must not recreate the app-side WebSession. -/
structure SessionFingerprintKey where
  authorityRoot : Digest
  app : ApplicationDispatchCodec.App
  session : ApplicationDispatchCodec.Session
  identity : ApplicationDispatchCodec.Identity
  bits : List Bool
  ticketResource : Nat
  ticketRoot : Digest
  enrollmentResource : Nat
  enrollmentRoot : Digest
  issueIngressBytes : List UInt8
  deriving DecidableEq

/-- `authorityRoot` is the authority root at admission (the prepared
invocation's snapshot); the signed command no longer names one. -/
def sessionFingerprintKey (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) : SessionFingerprintKey :=
  ⟨authorityRoot, { dispatch.app with snapshotVersion := 0 },
    dispatch.session, dispatch.identity, bits, ticketResource, ticketRoot,
    enrollmentResource, enrollmentRoot, issueIngressBytes⟩

private def workflowChangedDispatch (dispatch : ApplicationDispatchCodec.Dispatch)
    (nextSnapshot : Int) (nextRequest : ApplicationDispatchCodec.Request) :
    ApplicationDispatchCodec.Dispatch :=
  let nextApp := { dispatch.app with snapshotVersion := nextSnapshot }
  { dispatch with app := nextApp, request := nextRequest }

/-- General regression: changing a request, current session-page root or app
checkpoint version leaves the cache key equal when the stable authority and
rights projection is equal. Each request still independently checks those
current roots in `checkCurrent`. -/
theorem sessionFingerprintKey_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8)
    (nextRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintKey authorityRoot { selection with sessionRoot := nextRoot }
      (workflowChangedDispatch dispatch nextSnapshot nextRequest)
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes =
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  rfl

/-- These are exact source-preimage distinctions. Digest inequality additionally
relies on the deployed cSHAKE collision boundary, not a Lean axiom. -/
theorem sessionFingerprintKey_ticket_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot nextTicketRoot enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : ticketRoot ≠ nextTicketRoot) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource nextTicketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.ticketRoot equal)

theorem sessionFingerprintKey_enrollment_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextEnrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : enrollmentRoot ≠ nextEnrollmentRoot) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource nextEnrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.enrollmentRoot equal)

theorem sessionFingerprintKey_permissions_change (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits nextBits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8) (changed : bits ≠ nextBits) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection dispatch nextBits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.bits equal)

theorem sessionFingerprintKey_authority_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextAuthority : Digest)
    (issueIngressBytes : List UInt8) (changed : authorityRoot ≠ nextAuthority) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey nextAuthority selection dispatch bits
      ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg SessionFingerprintKey.authorityRoot equal)

theorem sessionFingerprintKey_package_changes (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource enrollmentResource : Nat) (ticketRoot enrollmentRoot nextPackage : Digest)
    (issueIngressBytes : List UInt8) (changed : dispatch.app.packageRoot ≠ nextPackage) :
    sessionFingerprintKey authorityRoot selection dispatch bits ticketResource ticketRoot
      enrollmentResource enrollmentRoot issueIngressBytes ≠
    sessionFingerprintKey authorityRoot selection
      { dispatch with app := { dispatch.app with packageRoot := nextPackage } }
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes := by
  intro equal
  exact changed (congrArg (fun key : SessionFingerprintKey => key.app.packageRoot) equal)

/-- Versioned, unambiguous source preimage for the physical app-side session.
It intentionally does not encode the current session/app page root, request,
or snapshot checkpoint. -/
def sessionFingerprintStream : StreamCodec SessionFingerprintKey :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product appStream
        (StreamCodec.product sessionStream
          (StreamCodec.product identityStream
            (StreamCodec.product (StreamCodec.list StreamCodec.bool)
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product digestStream
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product digestStream bytesStream)))))))))
    (fun key => (key.authorityRoot, key.app, key.session, key.identity, key.bits,
      key.ticketResource, key.ticketRoot, key.enrollmentResource,
      key.enrollmentRoot, key.issueIngressBytes))
    (fun (authorityRoot, app, session, identity, bits, ticketResource,
          ticketRoot, enrollmentResource, enrollmentRoot, issueIngressBytes) =>
      ⟨authorityRoot, app, session, identity, bits, ticketResource,
        ticketRoot, enrollmentResource, enrollmentRoot, issueIngressBytes⟩)
    (by intro key; cases key; rfl)

def sessionFingerprintMaterial (key : SessionFingerprintKey) : List UInt8 :=
  sessionFingerprintStream.encode key

/-- Ticket, enrollment, permission, authority and package changes above are
distinct *serialized preimages*. The final digest distinction is conditional
on the deployed hash collision boundary. -/
theorem sessionFingerprintMaterial_injective :
    Function.Injective sessionFingerprintMaterial :=
  lawful_encode_injective sessionFingerprintStream.toLawful

def sessionFingerprintOfKey (key : SessionFingerprintKey) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/DISPATCH-SESSION-FINGERPRINT/v2".toUTF8.toList
    (sessionFingerprintMaterial key)).digest

theorem sessionFingerprint_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (dispatch : ApplicationDispatchCodec.Dispatch) (bits : List Bool)
    (ticketResource : Nat) (ticketRoot : Digest)
    (enrollmentResource : Nat) (enrollmentRoot : Digest)
    (issueIngressBytes : List UInt8)
    (nextRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintOfKey (sessionFingerprintKey authorityRoot
      { selection with sessionRoot := nextRoot }
      (workflowChangedDispatch dispatch nextSnapshot nextRequest)
      bits ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes) =
    sessionFingerprintOfKey (sessionFingerprintKey authorityRoot selection dispatch bits
      ticketResource ticketRoot enrollmentResource enrollmentRoot issueIngressBytes) := by
  rw [sessionFingerprintKey_workflow_invariant]

def sessionFingerprintKeyFor (authorityRoot : Digest) (selection : Selection)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (bits : List Bool) (ticketResource : Nat) : SessionFingerprintKey :=
  sessionFingerprintKey authorityRoot selection ingress.dispatch.dispatch bits ticketResource
    ingress.ticketRoot ingress.dispatch.enrollmentResource
    ingress.dispatch.enrollmentRoot ingress.issueIngressBytes

private def workflowChangedIngress (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (nextAppRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    ApplicationDispatchAdmissionIngress.Ingress :=
  let nextDispatch := workflowChangedDispatch ingress.dispatch.dispatch
    nextSnapshot nextRequest
  let rootChanged := { ingress.dispatch with appRoot := nextAppRoot }
  let nextBase := { rootChanged with dispatch := nextDispatch }
  { ingress with dispatch := nextBase }

/-- The source-level carrier may have a different app page root, session page
root, checkpoint and HTTP request on the next admitted turn while retaining
the exact same WebSession authority projection. -/
theorem sessionFingerprint_ingress_workflow_invariant (authorityRoot : Digest) (selection : Selection)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (bits : List Bool) (ticketResource : Nat)
    (nextAppRoot nextSessionRoot : Digest) (nextSnapshot : Int)
    (nextRequest : ApplicationDispatchCodec.Request) :
    sessionFingerprintOfKey (sessionFingerprintKeyFor authorityRoot
      { selection with sessionRoot := nextSessionRoot }
      (workflowChangedIngress ingress nextAppRoot nextSnapshot nextRequest)
      bits ticketResource) =
    sessionFingerprintOfKey (sessionFingerprintKeyFor authorityRoot selection ingress bits ticketResource) := by
  rfl

/-- This is a cache invalidation key, never an external delivery permit. -/
def CheckedCurrent.sessionFingerprint {F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {spec : Spec} {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) : Digest :=
  sessionFingerprintOfKey (sessionFingerprintKeyFor
    checked.prepared.authority.snapshot.cell.root checked.selection ingress
    checked.bits spec.ticket.resource)

/-- Check one loaded image from actual native signature/capability/policy and
old-page admission. This is intentionally not the final dispatch receiver:
the `spec`/`descriptor` must be obtained from a separately verified, admitted
historical issue at a prefix of this exact image before a pending event can be
committed. -/
def checkCurrent {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (spec : Spec) (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :
    IO (Except String (CheckedCurrent deployment profile ambient durable ingress
      spec descriptor)) := do
  if profileExact : ingress.dispatch.domain = deployment.domain ∧
      ingress.dispatch.semantics = profile.semantics then
    if identityExact : identityMatches ingress = true then
      match selectedCommand : selectCommand ingress with
      | none => return .error "dispatch session observation selector missing"
      | some selection =>
          match decodedCommand : DeclaredResourceController.commandCodec.decode
              ingress.dispatch.signed.commandBytes with
          | none => return .error "noncanonical signed dispatch command"
          | some signedCommand =>
              if commandExact : matchesCommand ingress.dispatch selection ingress.parent
                  signedCommand = true then
                let expected := command ingress.dispatch selection ingress.parent
                match DeclaredResourceController.prepare deployment profile ambient durable
                    expected with
                | .error _ => return .error "current dispatch session or agent preparation refused"
                | .ok prepared =>
                    if shape : DeclaredResourceController.PhysicalShape prepared then
                      if linked : linkedCurrentPolicies deployment profile ambient durable
                          ingress spec selection prepared = true then
                        let .ok appRead ← checkRead deployment profile ambient native durable
                          ingress selection prepared ingress.dispatch.dispatch.app.resource
                          ingress.dispatch.appObserveCapability ingress.dispatch.appRoot
                          ingress.dispatch.appObservationEnvelope
                          | return .error "current serving app observation refused"
                        let .ok manifestRead ← checkRead deployment profile ambient native durable
                          ingress selection prepared ingress.dispatch.dispatch.app.packageManifest
                          ingress.dispatch.manifestObserveCapability
                          ingress.dispatch.dispatch.app.manifestRoot
                          ingress.dispatch.manifestObservationEnvelope
                          | return .error "current manifest observation refused"
                        let .ok enrollmentRead ← checkRead deployment profile ambient native durable
                          ingress selection prepared ingress.dispatch.enrollmentResource
                          ingress.dispatch.enrollmentObserveCapability ingress.dispatch.enrollmentRoot
                          ingress.dispatch.enrollmentObservationEnvelope
                          | return .error "current enrollment observation refused"
                        let .ok ticketRead ← checkRead deployment profile ambient native durable
                          ingress selection prepared spec.ticket.resource
                          ingress.ticketObserveCapability ingress.ticketRoot
                          ingress.ticketObservationEnvelope
                          | return .error "current share ticket observation refused"
                        match appExact : appState ingress.dispatch.dispatch.app.resource
                            appRead.selected.observed.before with
                        | none => return .error "serving app state missing"
                        | some actualApp =>
                          match manifestExact : installedManifest deployment.domain
                              ingress.dispatch.dispatch.app.packageManifest
                              ingress.dispatch.dispatch.app.resource
                              ingress.dispatch.dispatch.app.packageVersion
                              manifestRead.selected.observed.before with
                          | none => return .error "installed manifest missing"
                          | some manifest =>
                            match enrollmentExact : installedEnrollment deployment.domain
                                ingress.dispatch.enrollmentResource
                                ingress.dispatch.dispatch.session.resource
                                ingress.dispatch.dispatch.session.generation
                                enrollmentRead.selected.observed.before with
                            | none => return .error "current session enrollment missing"
                            | some enrollment =>
                              match ticketExact : installedTicket deployment.domain
                                  spec.ticket.resource ticketRead.selected.observed.before with
                              | none => return .error "current share ticket missing"
                              | some ticket =>
                                match meaningExact : selectedMeaning ingress spec actualApp
                                    manifest enrollment ticket with
                                | none => return .error "dispatch identity or permission ceiling refused"
                                | some bits =>
                                  if requestShape : requestSafe
                                      ingress.dispatch.dispatch.request = true then
                                    if issuerCurrent : issuerLineageCurrent deployment profile
                                        ambient durable ingress spec selection descriptor prepared = true then
                                      match ← DeclaredResourceController.admit native prepared
                                          ingress.dispatch.signed with
                                      | .error _ => return .error "current dispatch mutation authority refused"
                                      | .ok invocation =>
                                        return .ok ⟨profileExact, identityExact, selection,
                                          selectedCommand, signedCommand, decodedCommand,
                                          commandExact, prepared, shape, linked, appRead,
                                          manifestRead, enrollmentRead, ticketRead, actualApp,
                                          appExact, manifest, manifestExact, enrollment,
                                          enrollmentExact, ticket, ticketExact, bits,
                                          meaningExact, requestShape, issuerCurrent, invocation⟩
                                    else return .error "current issuer delegation lineage refused"
                                  else return .error "unsupported or unsafe HTTP request shape"
                      else return .error "current app/session/ticket policy linkage refused"
                    else return .error "dispatch physical mutation shape refused"
              else return .error "signed dispatch command differs from selected session/agent"
    else return .error "app-visible principal or app generation mismatch"
  else return .error "dispatch domain or semantics differs from deployment"


end Minidregg.Kernel.ApplicationDispatchAdmission
