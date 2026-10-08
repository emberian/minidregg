/-
Current-image authoring for participant enrollment. The verified event22 issue
selects the participant and ticket ceiling. The session and descriptor are one
ordinary signed joint mutation. Event28 admission separately checks a signed
app observation and adds the app's physical read guard to that same turn.
-/
import Compiler.CarriedApplicationProvenance
import Kernel.ApplicationGrainSessionEnrollmentSource
import Kernel.ApplicationGrainSessionEnrollmentConstruction
import Kernel.ApplicationDispatchAdmission
import Kernel.NativeHost

namespace Minidregg.Host.ApplicationGrainSessionEnrollmentAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

structure Plan where
  request : Request
  enrollment : Enrollment
  issueReceipt : NativeHostCodec.Receipt
  appRoot : Digest
  manifestRoot : Digest
  ticketRoot : Digest
  previous : Option AtomRecord
  invocation : SigningPlan
  observationSlots : List SigningSlot

private def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product enrollmentStream
        (StreamCodec.product NativeHostCodec.receiptStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product
                  (StreamCodec.option HyperdocumentCodec.atomRecordStream)
                  (StreamCodec.product signingPlanStream
                    (StreamCodec.list signingSlotStream)))))))))
    (fun plan => (plan.request, plan.enrollment, plan.issueReceipt,
      plan.appRoot, plan.manifestRoot, plan.ticketRoot, plan.previous,
      plan.invocation, plan.observationSlots))
    (fun (request, enrollment, issueReceipt, appRoot, manifestRoot,
          ticketRoot, previous, invocation, observationSlots) =>
      ⟨request, enrollment, issueReceipt, appRoot, manifestRoot,
        ticketRoot, previous, invocation, observationSlots⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SESSION-ENROLLMENT-PLAN/v1".toUTF8.toList
    planStream

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
      let page := payload.logical
      ApplicationGrainSession.readState session page
  | _ => none

private def descriptorPage (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ContentResource.ContentStore := do
  match cell with
  | ⟨.content, payload⟩ => some payload.logical
  | _ => none

private def observationSlot (config : Config) (opened : Opened config)
    (command : DeclaredResourceController.Command)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.ground command)
    (index resource : Nat) (capability : CapabilityId) (root : Digest) :
    Except String SigningSlot := do
  let probe : DeclaredResourceController.Target :=
    { kind := .object, target := resource, capability := capability,
      observeCapability := none, schemaVersion := ContentResource.commandVersion, expectedTargetRoot := root,
      payload := .content ⟨[]⟩ }
  let wanted : Request .object :=
    { DeclaredResourceController.requestFor opened.ground.authority
        config.profile.semantics
        ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
        command probe root with verb := .observeObject }
  let marker := DeclaredResourceController.operationMarker
    config.deployment.domain config.profile.semantics command
  let header ← (CredentialSignatureAdmission.signingHeader
      opened.ground.authority marker (⟨.object, wanted⟩ : PackedEffectRequest)).mapError
      (fun _ => "enrollment observation signing key unavailable")
  pure ⟨9, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

/-- This returns a proposal only. Event28 receiving must independently admit
the participant's joint mutation and all signed reads at the same image. -/
def prepareForIssue (config : Config) (opened : Opened config)
    (request : Request) (spec : ApplicationShareIssueSource.Spec)
    (issueReceipt : NativeHostCodec.Receipt) : Except String Plan := do
  let ticket := spec.ticket
  let app := ticket.scope.app
  let session := ticket.participant.session
  let descriptor := ticket.participant.descriptorResource
  if app == session || app == descriptor || session == descriptor then
    throw "app, session and descriptor must be distinct"
  let appCell ← NativeHost.need "current app cell absent" (cellAt config opened app)
  let appState ← NativeHost.need "current app state absent"
    (ApplicationDispatchAdmission.appState app appCell)
  if appState.phase != 4 then throw "app is not serving"
  let manifestCell ← NativeHost.need "current package manifest absent"
    (cellAt config opened request.packageManifest)
  let manifest ← NativeHost.need "installed package manifest absent"
    (ApplicationDispatchAdmission.installedManifest config.deployment.domain
      request.packageManifest app appState.packageVersion manifestCell)
  let interface ← NativeHost.need "issued interface absent from package"
    (manifest.select ticket.scope.interfaceId)
  if ticket.scope.packageVersion != appState.packageVersion ||
      ticket.scope.packageRoot != manifest.packageRoot ||
      ticket.scope.interfaceVersion != interface.version ||
      ticket.scope.interfaceRoot != interface.root ||
      ticket.scope.schemaRoot != interface.schema.root ||
      ticket.scope.schemaVersion != interface.schema.version ||
      ticket.participant.kind != interface.kind then
    throw "current installed interface differs from issued ticket"
  let requested ← NativeHost.need "enrollment role refused by current schema"
    (interface.schema.resolve request.role)
  let ceiling ← NativeHost.need "issued ceiling refused by current schema"
    (interface.schema.resolve ticket.ceiling)
  if !ApplicationDispatchAuthority.withinCeilingCheck requested ceiling then
    throw "enrollment role exceeds issued ceiling"
  let ticketCell ← NativeHost.need "current ticket cell absent"
    (cellAt config opened ticket.resource)
  let currentTicket ← NativeHost.need "installed ticket absent"
    (ApplicationDispatchAdmission.installedTicket config.deployment.domain
      ticket.resource ticketCell)
  if currentTicket != ticket then throw "installed ticket differs from admitted issue"
  let sessionCell ← NativeHost.need "current session cell absent"
    (cellAt config opened session)
  let before ← NativeHost.need "current session state absent"
    (sessionState session sessionCell)
  let kind := if ticket.participant.kind == .web then
    ApplicationGrainSession.Kind.web else ApplicationGrainSession.Kind.api
  if before.app != app || before.kind != kind ||
      !(before.status == .inactive || before.status == .closed) then
    throw "session is not available for enrollment"
  let descriptorCell ← NativeHost.need "current descriptor cell absent"
    (cellAt config opened descriptor)
  let page ← NativeHost.need "current descriptor page absent"
    (descriptorPage descriptorCell)
  let previous := Hyperdocument.lookup page .atoms
    (enrollmentAtom config.deployment.domain session)
  if previous.any (fun record => record.document != ⟨⟨descriptor⟩⟩) then
    throw "session descriptor identity differs"
  if before.status == .inactive then
    if before.generation != 0 || previous.isSome then
      throw "initial enrollment has a prior atom or generation"
  else
    let old ← NativeHost.need "renewal enrollment atom absent" previous
    let priorEnrollment ← NativeHost.need "renewal enrollment atom noncanonical"
      (enrollmentCodec.decode old.payload)
    if old.tombstonedAt.isSome || old.kind != .inlineObject ⟨14⟩ ||
        priorEnrollment.session != session ||
        priorEnrollment.descriptorResource != descriptor ||
        priorEnrollment.app != app ||
        priorEnrollment.subject != ticket.participant.subject ||
        priorEnrollment.origin != ticket.participant.origin ||
        priorEnrollment.sessionGeneration != before.generation - 1 then
      throw "renewal atom does not match closed session"
  let after := ApplicationGrainSession.Operation.after
    (.enroll appState.generation) before
  let enrollment : Enrollment :=
    { session := session, descriptorResource := descriptor,
      app := app, appGeneration := appState.generation,
      sessionGeneration := after.generation,
      kind := ticket.participant.kind,
      subject := ticket.participant.subject,
      capability := ticket.participant.sessionCapability,
      role := request.role, origin := ticket.participant.origin }
  if !enrollment.valid then throw "invalid session enrollment"
  let action := match previous with
    | none => initialAction config.deployment.domain enrollment
    | some old => renewalAction config.deployment.domain old enrollment
  let sessionTarget := ApplicationGrainSession.Operation.target
    (.enroll appState.generation) session ticket.participant.sessionCapability
    sessionCell.payload.root before (some request.sessionObserveCapability)
  let descriptorTarget : DeclaredResourceController.Target :=
    { kind := .object, target := descriptor,
      capability := request.descriptorCapability,
      observeCapability := some request.descriptorObserveCapability,
      schemaVersion := ContentResource.commandVersion, expectedTargetRoot := descriptorCell.payload.root,
      payload := .content ⟨[action]⟩ }
  let command := ApplicationGrainSession.Operation.command
    (.enroll appState.generation) ticket.participant.subject
    request.nonce session
    ticket.participant.sessionCapability sessionCell.payload.root before
    [descriptorTarget] (some request.sessionObserveCapability)
  if command.targets != [sessionTarget, descriptorTarget] then
    throw "enrollment command target mismatch"
  let constructed ← ApplicationGrainSessionEnrollmentConstruction.prepare
    config opened request spec
  if constructed.command != command || constructed.enrollment != enrollment ||
      constructed.previous != previous ||
      constructed.appRoot != appCell.payload.root ||
      constructed.manifestRoot != manifestCell.payload.root ||
      constructed.ticketRoot != ticketCell.payload.root then
    throw "enrollment authoring differs from shared native construction"
  let prepared ← match DeclaredResourceController.prepare
      config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.ground command with
    | .ok prepared => pure prepared
    | .error reason => throw s!"enrollment joint preparation refused: {repr reason}"
  let invocation ← NativeHost.prepareLoaded config opened
    (.invoke (DeclaredResourceController.commandCodec.encode command))
  if invocation.finalizedDraft !=
      .invoke (DeclaredResourceController.commandCodec.encode command) then
    throw "enrollment finalized command differs"
  let appSlot ← observationSlot config opened command prepared 0
    app ticket.participant.appObserveCapability appCell.payload.root
  let manifestSlot ← observationSlot config opened command prepared 1
    request.packageManifest request.manifestObserveCapability manifestCell.payload.root
  let ticketSlot ← observationSlot config opened command prepared 2
    ticket.resource ticket.participant.ticketObserveCapability ticketCell.payload.root
  pure ⟨request, enrollment, issueReceipt, appCell.payload.root,
    manifestCell.payload.root, ticketCell.payload.root, previous,
    invocation, [appSlot, manifestSlot, ticketSlot]⟩

/-- The ordinary path still selects a same-profile, fully admitted event22. -/
def prepareVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request) :
    Except String Plan := do
  let some prior := verified.issues.find? (fun issue =>
      issue.index == request.issueIndex &&
      issue.evidence.spec.ticket.resource == request.ticketResource)
    | throw "exact event22 ticket issue absent"
  if prior.evidence.record.event.codecVersion != 22 then
    throw "enrollment requires event22 ticket issue"
  prepareForIssue config verified.opened request prior.evidence.spec prior.receipt

/-- The carried path changes only historical selection. Current construction,
headers, role/ticket/interface checks and original receipt remain exact. -/
def prepareCarried (config : Config) (opened : Opened config)
    (custody : CarriedSegmentIO.PreservedPrefix config opened.durable) (request : Request) :
    ExceptT String IO Plan := do
  let issue ← ExceptT.mk (CarriedApplicationProvenance.selectIssue custody request.issueIndex)
  if issue.spec.ticket.resource != request.ticketResource then
    throw "carried enrollment ticket resource differs"
  prepareForIssue config opened request issue.spec issue.receipt

def prepareRequestCarried (config : Config) (opened : Opened config)
    (custody : CarriedSegmentIO.PreservedPrefix config opened.durable) (bytes : List UInt8) :
    ExceptT String IO Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical session enrollment request"
  if requestCodec.encode request != bytes then
    throw "noncanonical session enrollment request"
  prepareCarried config opened custody request

/-- Both sides of a carried service use their actual provenance: old issues
come from the retained profile, new issues from the admitted target suffix. -/
def prepareSuffix (config : Config) {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (request : Request) :
    ExceptT String IO Plan := do
  if request.issueIndex < anchor.durable.height then
    let some origin := verified.origin
      | throw "old session issue lacks authenticated carried origin"
    let custody ← origin.rebindChecked verified.opened.durable
    prepareCarried config verified.opened custody request
  else
    let some prior := verified.issues.find? (fun issue =>
        issue.index == request.issueIndex &&
        issue.evidence.spec.ticket.resource == request.ticketResource)
      | throw "exact target-suffix event22 ticket issue absent"
    if prior.evidence.record.event.codecVersion != 22 then
      throw "enrollment requires target-suffix event22 ticket issue"
    prepareForIssue config verified.opened request prior.evidence.spec prior.receipt

def prepareRequestSuffix (config : Config) {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    ExceptT String IO Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical session enrollment request"
  if requestCodec.encode request != bytes then
    throw "noncanonical session enrollment request"
  prepareSuffix config verified request

def prepareRequestVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical session enrollment request"
  if requestCodec.encode request != bytes then
    throw "noncanonical session enrollment request"
  prepareVerified config verified request

/-- Detached signatures are placed only in source-selected canonical headers.
Submission through event28 still performs fresh native admission and one CAS. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  if plan.observationSlots.length != 3 ||
      signatures.length != plan.invocation.slots.length + 3 then
    throw "session enrollment signing slot count mismatch"
  let signed ← NativeHost.assemble plan.invocation
    (signatures.take plan.invocation.slots.length)
  let signedBytes ← match signed with
    | .invoke command =>
        pure (DeclaredResourceController.signedBytes
          plan.invocation.domain plan.invocation.semantics command)
    | _ => throw "session enrollment plan is not an invocation"
  let observations ← (plan.observationSlots.zip
      (signatures.drop plan.invocation.slots.length)).mapM fun (slot, signature) => do
    if signature.length != 64 then
      throw "session enrollment observation signature must be 64 bytes"
    let some header := CredentialSignedEnvelopeController.headerCodec.decode slot.header
      | throw "noncanonical session enrollment observation header"
    pure <| CredentialSignedEnvelopeController.envelopeCodec.encode
      ⟨header, signature⟩
  match observations with
  | [app, manifest, ticket] =>
      pure <| ingressCodec.encode
        ⟨plan.request, plan.enrollment, plan.issueReceipt,
          plan.appRoot, plan.manifestRoot, plan.ticketRoot,
          signedBytes, app, manifest, ticket⟩
  | _ => throw "session enrollment observation list mismatch"

/-- A detached plan is reselected against a freshly verified tip before
signatures are packaged. Equality covers old atom, all current roots,
original issue receipt and every signing header. -/
def assembleCurrent (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let fresh ← prepareVerified config verified plan.request
  if planCodec.encode fresh != planCodec.encode plan then
    throw "session enrollment plan no longer current"
  assemble fresh signatures


/-- A carried detached plan is reselected before assembly using the same
current roots/headers and retained original receipt, never a fresh baseline. -/
def assembleCurrentCarried (config : Config) (opened : Opened config)
    (custody : CarriedSegmentIO.PreservedPrefix config opened.durable)
    (plan : Plan) (signatures : List (List UInt8)) :
    ExceptT String IO (List UInt8) := do
  let fresh ← prepareCarried config opened custody plan.request
  if planCodec.encode fresh != planCodec.encode plan then
    throw "carried session enrollment plan no longer current"
  assemble fresh signatures


def assembleCurrentSuffix (config : Config) {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target)
    (plan : Plan) (signatures : List (List UInt8)) :
    ExceptT String IO (List UInt8) := do
  let fresh ← prepareSuffix config verified plan.request
  if planCodec.encode fresh != planCodec.encode plan then
    throw "session enrollment plan no longer current in carried service"
  assemble fresh signatures

end Minidregg.Host.ApplicationGrainSessionEnrollmentAuthoring
