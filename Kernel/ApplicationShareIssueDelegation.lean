/-
Current app delegation leg for a special share issue. The app resource is
read-only in the physical turn, but the signer must hold a current native
`.delegateObject` capability and satisfy the app's installed law for the
exact source-derived ticket birth. This checked result is not by itself an
issue receipt: the birth branch and this branch must be joined at one loaded
image and one durable CAS by ApplicationShareIssueAdmission.
-/
import Kernel.ApplicationShareIssueSource
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.ApplicationShareIssueDelegation
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationShareIssueSource
set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Context := ResourceObservationAdmission.Context

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {durable : Durable}

/-- A read-only app cell selected from the exact loaded directory. No public
constructor accepts an asserted policy result, owner, or capability value. -/
structure Prepared (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) where
  private mk ::
  root : Digest
  observed : ResourceTargetAdmission.Observed deployment context.directory.directory
    .object spec.ticket.scope.app root
  declared : observed.before.kind = .declaredObject
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨spec.ticket.scope.app⟩
  epochCurrent :
    (appRequest deployment.domain profile.semantics federation
      context.authority.snapshot.authState height root spec descriptor).policyEpoch =
        context.authority.snapshot.authState.policyEpoch ⟨spec.ticket.scope.app⟩
  revisionCurrent :
    (appRequest deployment.domain profile.semantics federation
      context.authority.snapshot.authState height root spec descriptor).policyRevision =
        context.authority.snapshot.authState.policyRevision ⟨spec.ticket.scope.app⟩

def Prepared.wanted {context : Context deployment durable}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {height : Nat} {spec : Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    (prepared : Prepared context profile federation height spec descriptor) : Request .object :=
  appRequest deployment.domain profile.semantics federation
    context.authority.snapshot.authState height prepared.root spec descriptor

private def refused : String := "app share delegation refused"

def prepare (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :
    Except String (Prepared context profile federation height spec descriptor) :=
  match context.directory.directory.slots spec.ticket.scope.app with
  | .absent => .error refused
  | .present packed =>
      match ResourceTargetAdmission.observe deployment context.directory.directory
          .object spec.ticket.scope.app packed.payload.root with
      | none => .error refused
      | some observed =>
          if declared : observed.before.kind = .declaredObject then
            .ok ⟨packed.payload.root, observed, declared,
              PhysicalResourceReadGuard.current context.directory
                spec.ticket.scope.app observed.before observed.present,
              rfl, rfl⟩
          else .error refused

variable {context : Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {spec : Spec}
  {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}

def project (prepared : Prepared context profile federation height spec descriptor)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots context.directory.directory spec.ticket.scope.app ++
    CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (sourceBytes spec descriptor) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots prepared.wanted.subject spec.ticket.scope.app
      prepared.observed.before.kind logical⟩

def step (prepared : Prepared context profile federation height spec descriptor) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate prepared.wanted
      prepared.observed.before.kind prepared.observed.before.payload
      prepared.observed.rootExact)

def kindDependencies (_prepared : Prepared context profile federation height spec descriptor) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment context.directory.directory spec.ticket.scope.app

def policyConfig (prepared : Prepared context profile federation height spec descriptor) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile context.authority.snapshot
    context.directory.directory
    (sourceCapabilityPortal context.authority.snapshot (issueMarker spec descriptor))
    (step prepared) spec.ticket.scope.app
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def lawReadGuards (prepared : Prepared context profile federation height spec descriptor) :
    Option (List DurableDataIntent.ReadGuard) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards context.authority.snapshot
    context.directory.directory profile.semantics spec.ticket.scope.app structural.additional
  pure ((sources ++ structural.readGuards).map fun (id, root) => ⟨⟨id⟩, root⟩)

def readGuards (prepared : Prepared context profile federation height spec descriptor) :
    List DurableDataIntent.ReadGuard := (lawReadGuards prepared).getD []


def portal (prepared : Prepared context profile federation height spec descriptor) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile federation height spec descriptor)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted) := do
  let config := policyConfig prepared
  let _ ← kindDependencies prepared
  let evidence ← (config.capabilityEvidenceChecked prepared.wanted
    spec.appDelegateCapability () signature () (fun _ => ())).toOption
  let law ← config.resolve?
  ComposedPolicyAdmission.admit config prepared.wanted
    evidence law.witness (.policy prepared.wanted.policyId prepared.wanted.policyRevision)
    prepared.epochCurrent prepared.revisionCurrent

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile federation height spec descriptor)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted
  authorized : authorize prepared signature = some authorization
  guardsPresent : (lawReadGuards prepared).isSome = true
  guardsCurrent : ∀ guard ∈ readGuards prepared,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height spec descriptor)
    (envelope : List UInt8) : IO (Except String (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot
      (issueMarker spec descriptor) prepared.wanted envelope with
  | .error _ => return .error refused
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return .error refused
        | some authorization =>
          if guardsPresent : (lawReadGuards prepared).isSome = true then
            if guardsCurrent : ∀ guard ∈ readGuards prepared,
                guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
              return .ok ⟨signature, exact, authorization, authorized, guardsPresent, guardsCurrent⟩
            else return .error refused
          else return .error refused
      else return .error refused

def readGuard (prepared : Prepared context profile federation height spec descriptor) :
    DurableDataIntent.ReadGuard :=
  ⟨⟨spec.ticket.scope.app⟩,
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before)⟩

theorem readGuard_current (prepared : Prepared context profile federation height spec descriptor) :
    (readGuard prepared).expectedRoot =
      durable.snapshot.model.roots (readGuard prepared).cellId :=
  prepared.physicalCurrent

end Minidregg.Kernel.ApplicationShareIssueDelegation
