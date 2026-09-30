/-
Cycle-safe source construction for a current session enrollment. The input
ticket is a verifier-selected original issue, not a caller's asserted ticket.
This function does no signature checking and mints no admission evidence.
-/
import Kernel.ApplicationGrainSessionEnrollmentSource
import Kernel.ApplicationDispatchAdmission

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentConstruction

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollment
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

structure Current where
  ticket : ApplicationDispatchAuthority.Ticket
  enrollment : Enrollment
  previous : Option AtomRecord
  appRoot : Digest
  manifestRoot : Digest
  ticketRoot : Digest
  command : DeclaredResourceController.Command

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

def prepare (config : Config) (opened : Opened config)
    (request : Request) (spec : ApplicationShareIssueSource.Spec) :
    Except String Current := do
  let ticket := spec.ticket
  if ticket.resource != request.ticketResource then
    throw "selected issue ticket resource differs"
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
  let descriptorTarget : DeclaredResourceController.Target :=
    { kind := .object, target := descriptor,
      capability := request.descriptorCapability,
      observeCapability := some request.descriptorObserveCapability,
      schemaVersion := 1, expectedTargetRoot := descriptorCell.payload.root,
      payload := .content ⟨[action]⟩ }
  let command := ApplicationGrainSession.Operation.command
    (.enroll appState.generation) ticket.participant.subject
    opened.authority.snapshot.cell.root request.nonce session
    ticket.participant.sessionCapability sessionCell.payload.root before
    [descriptorTarget] (some request.sessionObserveCapability)
  pure ⟨ticket, enrollment, previous, appCell.payload.root,
    manifestCell.payload.root, ticketCell.payload.root, command⟩

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentConstruction
