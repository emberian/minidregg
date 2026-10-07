/-
Native admission for a proposed enrollment at one loaded prefix. The joint
session/descriptor mutation remains an ordinary DRC admission. The app,
manifest and issued ticket are separately observed with current signed reads;
their physical roots become guards of one distinct event28 intent.
-/
import Kernel.ApplicationGrainSessionEnrollmentConstruction
import Kernel.PhysicalResourceReadGuard
import Kernel.NativeHostServed

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentAdmission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentConstruction
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

private def observationRequest (config : Config) (opened : Opened config)
    (command : DeclaredResourceController.Command)
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.ground command)
    (resource : Nat) (capability : CapabilityId) (root : Digest) : Request .object :=
  let target : DeclaredResourceController.Target :=
    { kind := .object, target := resource, capability := capability,
      observeCapability := none, schemaVersion := ContentResource.commandVersion, expectedTargetRoot := root,
      payload := .content ⟨[]⟩ }
  { DeclaredResourceController.requestFor opened.ground.authority
      config.profile.semantics
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      command target root with verb := .observeObject }

private def observationMarker (config : Config)
    (command : DeclaredResourceController.Command) : Nat :=
  DeclaredResourceController.operationMarker
    config.deployment.domain config.profile.semantics command

structure CheckedRead {config : Config} {opened : Opened config}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.ground command)
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared
    (DeclaredResourceController.readContext prepared) config.profile
    (observationRequest config opened command prepared resource capability root)
    (observationMarker config command) capability
    (DeclaredResourceController.commandCodec.encode command)
  checked : ResourceObservationAdmission.Checked selected envelope
  current : ResourceBirthCodec.physicalRoot (.live selected.observed.before) =
    opened.durable.snapshot.model.roots ⟨resource⟩
  readonly : (⟨⟨resource⟩,
    ResourceBirthCodec.physicalRoot (.live selected.observed.before)⟩ : ReadGuard).cellId ∉
    (DeclaredResourceController.writes prepared).map DataWrite.cellId

def checkRead {config : Config} {opened : Opened config}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
      opened.ground command)
    (resource : Nat) (capability : CapabilityId) (root : Digest)
    (envelope : List UInt8) :
    IO (Except String (CheckedRead prepared resource capability root envelope)) := do
  let wanted := observationRequest config opened command prepared resource capability root
  let context := DeclaredResourceController.readContext prepared
  match ResourceObservationAdmission.prepare context config.profile wanted
      (observationMarker config command) capability
      (DeclaredResourceController.commandCodec.encode command) with
  | .error _ => return .error "current enrollment observation refused"
  | .ok selected =>
      match ← ResourceObservationAdmission.check config.signature selected envelope with
      | .error _ => return .error "signed enrollment observation refused"
      | .ok checked =>
          let current := ServedBasis.Ground.physicalCurrent context resource
            selected.observed.before selected.observed.present
          if readonly : (⟨⟨resource⟩,
              ResourceBirthCodec.physicalRoot (.live selected.observed.before)⟩ : ReadGuard).cellId ∉
              (DeclaredResourceController.writes prepared).map DataWrite.cellId then
            return .ok ⟨selected, checked, current, readonly⟩
          else return .error "enrollment observation overlaps joint writes"

structure Checked (config : Config) (opened : Opened config)
    (ingress : Ingress) (spec : ApplicationShareIssueSource.Spec)
    (issueReceipt : NativeHostCodec.Receipt) where
  private mk ::
  current : Current
  signed : DeclaredResourceController.SignedCommand
  command : DeclaredResourceController.Command
  prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    opened.ground command
  shape : DeclaredResourceController.PhysicalShape prepared
  accepted : DeclaredResourceController.AcceptedInvocation prepared signed
  appRead : CheckedRead prepared spec.ticket.scope.app
    spec.ticket.participant.appObserveCapability ingress.appRoot
    ingress.appObservationEnvelope
  manifestRead : CheckedRead prepared ingress.request.packageManifest
    ingress.request.manifestObserveCapability ingress.manifestRoot
    ingress.manifestObservationEnvelope
  ticketRead : CheckedRead prepared spec.ticket.resource
    spec.ticket.participant.ticketObserveCapability ingress.ticketRoot
    ingress.ticketObservationEnvelope

def admitAt (config : Config) (opened : Opened config)
    (ingress : Ingress) (spec : ApplicationShareIssueSource.Spec)
    (issueReceipt : NativeHostCodec.Receipt) :
    IO (Except String (Checked config opened ingress spec issueReceipt)) := do
  if ingress.issueReceipt != issueReceipt then
    return .error "enrollment original issue receipt differs"
  let .ok current := prepare config opened ingress.request spec
    | return .error "current enrollment construction refused"
  if ingress.enrollment != current.enrollment ||
      ingress.appRoot != current.appRoot ||
      ingress.manifestRoot != current.manifestRoot ||
      ingress.ticketRoot != current.ticketRoot then
    return .error "enrollment source differs from current image"
  let some (domain, semantics, signed) :=
      DeclaredResourceController.decodeSignedBytes ingress.signedBytes
    | return .error "noncanonical signed enrollment command"
  if domain != config.deployment.domain || semantics != config.profile.semantics ||
      DeclaredResourceController.signedBytes domain semantics signed != ingress.signedBytes then
    return .error "enrollment domain or signed command differs"
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | return .error "noncanonical enrollment command"
  if command != current.command ||
      DeclaredResourceController.commandCodec.encode command != signed.commandBytes then
    return .error "signed enrollment command differs from source"
  match ← DeclaredResourceController.prepareAuthenticated config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩ config.signature
      opened.ground command signed.authorityEnvelope with
  | .error _ => return .error "joint enrollment preparation refused"
  | .ok prepared =>
      if shape : DeclaredResourceController.PhysicalShape prepared then
        match ← DeclaredResourceController.admit config.signature prepared signed with
        | .error _ => return .error "joint enrollment native admission refused"
        | .ok accepted =>
            let .ok appRead ← checkRead prepared spec.ticket.scope.app
                spec.ticket.participant.appObserveCapability ingress.appRoot
                ingress.appObservationEnvelope
              | return .error "current signed app read refused"
            let .ok manifestRead ← checkRead prepared ingress.request.packageManifest
                ingress.request.manifestObserveCapability ingress.manifestRoot
                ingress.manifestObservationEnvelope
              | return .error "current signed manifest read refused"
            let .ok ticketRead ← checkRead prepared spec.ticket.resource
                spec.ticket.participant.ticketObserveCapability ingress.ticketRoot
                ingress.ticketObservationEnvelope
              | return .error "current signed ticket read refused"
            return .ok ⟨current, signed, command, prepared, shape, accepted,
              appRead, manifestRead, ticketRead⟩
      else return .error "joint enrollment physical shape refused"

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentAdmission
