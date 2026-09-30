/-
Current app delegation leg for special lifetime-grant issuance. The app resource is
read-only in the physical turn, but the signer must hold a current native
`.delegateObject` capability and satisfy the app's installed law for the
exact source-derived grant birth. This checked result is not by itself an
issuance receipt: the birth branch and this branch must be joined at one loaded
image and one durable CAS by the event27 receiver.
-/
import Kernel.ApplicationAgentLifetimeGrantSource
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantDelegation
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
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
    .object spec.grant.participant.app root
  declared : observed.before.kind = .declaredObject
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨spec.grant.participant.app⟩
  epochCurrent :
    (appRequest deployment.domain profile.semantics federation
      context.authority.snapshot.authState height root spec descriptor).policyEpoch =
        context.authority.snapshot.authState.policyEpoch ⟨spec.grant.participant.app⟩
  revisionCurrent :
    (appRequest deployment.domain profile.semantics federation
      context.authority.snapshot.authState height root spec descriptor).policyRevision =
        context.authority.snapshot.authState.policyRevision ⟨spec.grant.participant.app⟩

def Prepared.wanted {context : Context deployment durable}
    {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
    {height : Nat} {spec : Spec}
    {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    (prepared : Prepared context profile federation height spec descriptor) : Request .object :=
  appRequest deployment.domain profile.semantics federation
    context.authority.snapshot.authState height prepared.root spec descriptor

private def refused : String := "agent lifetime grant delegation refused"

def prepare (context : Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) :
    Except String (Prepared context profile federation height spec descriptor) :=
  match context.directory.directory.slots spec.grant.participant.app with
  | .absent => .error refused
  | .present packed =>
      match ResourceTargetAdmission.observe deployment context.directory.directory
          .object spec.grant.participant.app packed.payload.root with
      | none => .error refused
      | some observed =>
          if declared : observed.before.kind = .declaredObject then
            .ok ⟨packed.payload.root, observed, declared,
              PhysicalResourceReadGuard.current context.directory
                spec.grant.participant.app observed.before observed.present,
              rfl, rfl⟩
          else .error refused

variable {context : Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {spec : Spec}
  {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}

def project (prepared : Prepared context profile federation height spec descriptor)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (sourceBytes spec descriptor) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots spec.grant.participant.app
      prepared.observed.before.kind logical⟩

def step (prepared : Prepared context profile federation height spec descriptor) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate prepared.wanted
      prepared.observed.before.kind prepared.observed.before.payload
      prepared.observed.rootExact)

def policyConfig (prepared : Prepared context profile federation height spec descriptor) :
    CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile
    context.authority.snapshot (ResourceObservationAdmission.sourceStore context)
    (sourceCapabilityPortal context.authority.snapshot (issueMarker spec descriptor))
    (step prepared)

def portal (prepared : Prepared context profile federation height spec descriptor) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile federation height spec descriptor)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted) := do
  let config := policyConfig prepared
  let evidence ← sourceCapabilityOnlyEvidence profile.compilerProfile
    context.authority.snapshot (ResourceObservationAdmission.sourceStore context)
    (issueMarker spec descriptor) (step prepared) prepared.wanted
    spec.grant.approval.delegateCapability signature
  let committed ← config.registry.resolve prepared.wanted.policyId prepared.wanted.policyRevision
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared).oldState (step prepared).newState
  CanonicalPolicyAdmission.admit config context.authority.snapshot.authState prepared.wanted
    evidence witness (.policy prepared.wanted.policyId prepared.wanted.policyRevision)
    prepared.epochCurrent prepared.revisionCurrent

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile federation height spec descriptor)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted
  authorized : authorize prepared signature = some authorization

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
        | some authorization => return .ok ⟨signature, exact, authorization, authorized⟩
      else return .error refused

def readGuard (prepared : Prepared context profile federation height spec descriptor) :
    DurableDataIntent.ReadGuard :=
  ⟨⟨spec.grant.participant.app⟩,
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before)⟩

omit [DecidableEq F] in
theorem readGuard_current (prepared : Prepared context profile federation height spec descriptor) :
    (readGuard prepared).expectedRoot =
      durable.snapshot.model.roots (readGuard prepared).cellId :=
  prepared.physicalCurrent

end Minidregg.Kernel.ApplicationAgentLifetimeGrantDelegation
