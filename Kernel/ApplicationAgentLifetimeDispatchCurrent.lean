/-
Current-image component for event26. It keeps the original event22 ticket and
session origin intact, while checking the currently reserved parent as a
separate execution witness. The grant and ticket certificates supplied to
this component still require chronological admission in NativeHostReplay.
-/
import Kernel.ApplicationAgentLifetimeDispatchIngress
import Kernel.ApplicationDispatchAdmission

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchCurrent

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationDispatchAdmission
open Minidregg.Kernel.ApplicationDispatchCommand
open Minidregg.Kernel.ApplicationAgentLifetimeDispatchIngress

set_option autoImplicit false

def grantAt (domain : Digest) (resource : Nat)
    (cell : PackedCell CanonicalCellRegistry.registry) :
    Option ApplicationAgentLifetimeGrant.Grant := do
  let ⟨.content, payload⟩ := cell
    | none
  let page ← HyperdocumentContentPageMaterializer.pageAt payload.logical
  ApplicationAgentLifetimeGrant.decodeInstalled domain resource page

/-- Unlike event21's `parentMatches`, this tests the physical current parent
against the separately issued grant. The original ticket origin stays bound
to its issuance generation. -/
def currentParentMatches (ingress : Ingress)
    (grant : ApplicationAgentLifetimeGrant.Grant) : Bool :=
  let context := ingress.reserveContext.base
  match ingress.dispatch.parent with
  | none => false
  | some current =>
      decide (current.task = context.parentTask ∧
        context.parentTask = grant.participant.parentTask ∧
        current.state.generation = context.parentGeneration ∧
        (current.state.status = 3 ∨ current.state.status = 4) ∧
        current.state.remaining ≥ 0 ∧ current.state.reserved ≥ 0)

structure Checked {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : Ingress)
    (spec : ApplicationShareIssueSource.Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (ticketIssueIndex : Nat) (ticketIssueReceipt : NativeHostCodec.Receipt)
    (issuedIngressBytes : List UInt8) (certifiedGrantIssueIndex : Nat)
    (certifiedGrantRoot : Digest) where
  private mk ::
  issued : grant.matchesIssued spec ticketIssueIndex ticketIssueReceipt = true
  issueBytesExact : ingress.dispatch.issueIngressBytes = issuedIngressBytes
  route : matchesRoute ingress grant spec.ticket.resource certifiedGrantIssueIndex = true
  profileExact : ingress.dispatch.dispatch.domain = deployment.domain ∧
    ingress.dispatch.dispatch.semantics = profile.semantics
  identityExact : identityMatches ingress.dispatch = true
  selection : Selection
  selectedCommand : selectCommand ingress.dispatch = some selection
  signedCommand : DeclaredResourceController.Command
  decodedCommand : DeclaredResourceController.commandCodec.decode
    ingress.dispatch.dispatch.signed.commandBytes = some signedCommand
  parentCurrent : currentParentMatches ingress grant = true
  commandExact : signedCommand = command ingress.dispatch.dispatch
    selection ingress.dispatch.parent
  prepared : DeclaredResourceController.PreparedInvocation deployment profile ambient durable
    (command ingress.dispatch.dispatch selection ingress.dispatch.parent)
  shape : DeclaredResourceController.PhysicalShape prepared
  linked : linkedCurrentPolicies deployment profile ambient durable
    ingress.dispatch spec selection prepared = true
  appRead : CheckedRead deployment profile ambient durable ingress.dispatch
    selection prepared ingress.dispatch.dispatch.dispatch.app.resource
    ingress.dispatch.dispatch.appObserveCapability
    ingress.dispatch.dispatch.appRoot
    ingress.dispatch.dispatch.appObservationEnvelope
  manifestRead : CheckedRead deployment profile ambient durable ingress.dispatch
    selection prepared ingress.dispatch.dispatch.dispatch.app.packageManifest
    ingress.dispatch.dispatch.manifestObserveCapability
    ingress.dispatch.dispatch.dispatch.app.manifestRoot
    ingress.dispatch.dispatch.manifestObservationEnvelope
  enrollmentRead : CheckedRead deployment profile ambient durable ingress.dispatch
    selection prepared ingress.dispatch.dispatch.enrollmentResource
    ingress.dispatch.dispatch.enrollmentObserveCapability
    ingress.dispatch.dispatch.enrollmentRoot
    ingress.dispatch.dispatch.enrollmentObservationEnvelope
  ticketRead : CheckedRead deployment profile ambient durable ingress.dispatch
    selection prepared spec.ticket.resource
    ingress.dispatch.ticketObserveCapability
    ingress.dispatch.ticketRoot
    ingress.dispatch.ticketObservationEnvelope
  grantRead : CheckedRead deployment profile ambient durable ingress.dispatch
    selection prepared ingress.reserveContext.grantResource ingress.grantObserveCapability
    ingress.grantRoot ingress.grantObservationEnvelope
  grantPhysical : ResourceBirthCodec.physicalRoot (.live grantRead.selected.observed.before) =
    certifiedGrantRoot
  grantExact : grantAt deployment.domain ingress.reserveContext.grantResource
    grantRead.selected.observed.before = some grant
  actualApp : ApplicationGrain.State
  appExact : appState ingress.dispatch.dispatch.dispatch.app.resource
    appRead.selected.observed.before = some actualApp
  manifest : ApplicationDispatchManifest.Manifest
  manifestExact : installedManifest deployment.domain
    ingress.dispatch.dispatch.dispatch.app.packageManifest
    ingress.dispatch.dispatch.dispatch.app.resource
    ingress.dispatch.dispatch.dispatch.app.packageVersion
    manifestRead.selected.observed.before = some manifest
  enrollment : ApplicationGrainSessionEnrollment.Enrollment
  enrollmentExact : installedEnrollment deployment.domain
    ingress.dispatch.dispatch.enrollmentResource
    ingress.dispatch.dispatch.dispatch.session.resource
    ingress.dispatch.dispatch.dispatch.session.generation
    enrollmentRead.selected.observed.before = some enrollment
  ticket : ApplicationDispatchAuthority.Ticket
  ticketExact : installedTicket deployment.domain spec.ticket.resource
    ticketRead.selected.observed.before = some ticket
  bits : List Bool
  meaningExact : selectedMeaning ingress.dispatch spec actualApp manifest
    enrollment ticket = some bits
  requestShape : requestSafe ingress.dispatch.dispatch.dispatch.request = true
  issuerCurrent : issuerLineageCurrent deployment profile ambient durable
    ingress.dispatch spec selection descriptor prepared = true
  invocation : DeclaredResourceController.AcceptedInvocation prepared
    ingress.dispatch.dispatch.signed

/-- All five current observations share the exact prepared DRC image. The
grant read uses the participant's separately issued selector; its signed
inner root is not substituted for the complete physical cell root. -/
def checkCurrent {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (durable : Durable) (ingress : Ingress)
    (spec : ApplicationShareIssueSource.Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry)
    (grant : ApplicationAgentLifetimeGrant.Grant)
    (ticketIssueIndex : Nat) (ticketIssueReceipt : NativeHostCodec.Receipt)
    (issuedIngressBytes : List UInt8) (certifiedGrantIssueIndex : Nat)
    (certifiedGrantRoot : Digest) :
    IO (Except String (Checked deployment profile ambient durable ingress spec
      descriptor grant ticketIssueIndex ticketIssueReceipt issuedIngressBytes
      certifiedGrantIssueIndex certifiedGrantRoot)) := do
  let base := ingress.dispatch
  if issued : grant.matchesIssued spec ticketIssueIndex ticketIssueReceipt = true then
    if issueBytesExact : base.issueIngressBytes = issuedIngressBytes then
      if route : matchesRoute ingress grant spec.ticket.resource
          certifiedGrantIssueIndex = true then
        if profileExact : base.dispatch.domain = deployment.domain ∧
            base.dispatch.semantics = profile.semantics then
          if identityExact : identityMatches base = true then
            match selectedCommand : selectCommand base with
            | none => return .error "lifetime dispatch session selector missing"
            | some selection =>
              match decodedCommand : DeclaredResourceController.commandCodec.decode
                  base.dispatch.signed.commandBytes with
              | none => return .error "lifetime dispatch signed command malformed"
              | some signedCommand =>
                if parentCurrent : currentParentMatches ingress grant = true then
                  if commandExact : signedCommand = command base.dispatch selection base.parent then
                    match DeclaredResourceController.prepare deployment profile ambient durable
                        (command base.dispatch selection base.parent) with
                    | .error _ => return .error "lifetime dispatch current preparation refused"
                    | .ok prepared =>
                      if shape : DeclaredResourceController.PhysicalShape prepared then
                        if linked : linkedCurrentPolicies deployment profile ambient durable
                            base spec selection prepared = true then
                          let .ok appRead ← checkRead deployment profile ambient native durable
                            base selection prepared base.dispatch.dispatch.app.resource
                            base.dispatch.appObserveCapability base.dispatch.appRoot
                            base.dispatch.appObservationEnvelope
                            | return .error "lifetime dispatch app observation refused"
                          let .ok manifestRead ← checkRead deployment profile ambient native
                            durable base selection prepared
                            base.dispatch.dispatch.app.packageManifest
                            base.dispatch.manifestObserveCapability
                            base.dispatch.dispatch.app.manifestRoot
                            base.dispatch.manifestObservationEnvelope
                            | return .error "lifetime dispatch manifest observation refused"
                          let .ok enrollmentRead ← checkRead deployment profile ambient native
                            durable base selection prepared base.dispatch.enrollmentResource
                            base.dispatch.enrollmentObserveCapability
                            base.dispatch.enrollmentRoot
                            base.dispatch.enrollmentObservationEnvelope
                            | return .error "lifetime dispatch enrollment observation refused"
                          let .ok ticketRead ← checkRead deployment profile ambient native durable
                            base selection prepared spec.ticket.resource
                            base.ticketObserveCapability base.ticketRoot
                            base.ticketObservationEnvelope
                            | return .error "lifetime dispatch original ticket observation refused"
                          let .ok grantRead ← checkRead deployment profile ambient native durable
                            base selection prepared ingress.reserveContext.grantResource
                            ingress.grantObserveCapability ingress.grantRoot
                            ingress.grantObservationEnvelope
                            | return .error "lifetime dispatch grant observation refused"
                          if grantPhysical : ResourceBirthCodec.physicalRoot
                              (.live grantRead.selected.observed.before) = certifiedGrantRoot then
                            if grantExact : grantAt deployment.domain ingress.reserveContext.grantResource
                                grantRead.selected.observed.before = some grant then
                              match appExact : appState base.dispatch.dispatch.app.resource
                                  appRead.selected.observed.before with
                              | none => return .error "lifetime dispatch current app missing"
                              | some actualApp =>
                                match manifestExact : installedManifest deployment.domain
                                    base.dispatch.dispatch.app.packageManifest
                                    base.dispatch.dispatch.app.resource
                                    base.dispatch.dispatch.app.packageVersion
                                    manifestRead.selected.observed.before with
                                | none => return .error "lifetime dispatch manifest missing"
                                | some manifest =>
                                  match enrollmentExact : installedEnrollment deployment.domain
                                      base.dispatch.enrollmentResource
                                      base.dispatch.dispatch.session.resource
                                      base.dispatch.dispatch.session.generation
                                      enrollmentRead.selected.observed.before with
                                  | none => return .error "lifetime dispatch enrollment missing"
                                  | some enrollment =>
                                    match ticketExact : installedTicket deployment.domain
                                        spec.ticket.resource ticketRead.selected.observed.before with
                                    | none => return .error "lifetime dispatch original ticket missing"
                                    | some ticket =>
                                      match meaningExact : selectedMeaning base spec actualApp
                                          manifest enrollment ticket with
                                      | none => return .error "lifetime dispatch scope or role refused"
                                      | some bits =>
                                        if requestShape : requestSafe base.dispatch.dispatch.request = true then
                                          if issuerCurrent : issuerLineageCurrent deployment profile
                                              ambient durable base spec selection descriptor prepared = true then
                                            match ← DeclaredResourceController.admit native prepared
                                                base.dispatch.signed with
                                            | .error _ =>
                                              return .error "lifetime dispatch current mutation refused"
                                            | .ok invocation =>
                                              return .ok ⟨issued, issueBytesExact, route, profileExact,
                                                identityExact, selection, selectedCommand,
                                                signedCommand, decodedCommand, parentCurrent,
                                                commandExact, prepared, shape, linked, appRead,
                                                manifestRead, enrollmentRead, ticketRead,
                                                grantRead, grantPhysical, grantExact,
                                                actualApp, appExact, manifest, manifestExact,
                                                enrollment, enrollmentExact, ticket, ticketExact,
                                                bits, meaningExact, requestShape,
                                                issuerCurrent, invocation⟩
                                          else return .error "lifetime dispatch issuer lineage refused"
                                        else return .error "lifetime dispatch unsafe HTTP request"
                            else return .error "lifetime grant content differs from certified issue"
                          else return .error "lifetime grant complete cell changed since issue"
                        else return .error "lifetime dispatch current policy linkage refused"
                      else return .error "lifetime dispatch physical shape refused"
                  else return .error "lifetime dispatch signed command differs"
                else return .error "lifetime dispatch current parent refused"
          else return .error "lifetime dispatch app identity refused"
        else return .error "lifetime dispatch profile mismatch"
      else return .error "lifetime dispatch grant or reserve route mismatch"
    else return .error "lifetime dispatch original issue bytes differ"
  else return .error "lifetime dispatch grant exceeds original ticket"

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchCurrent
