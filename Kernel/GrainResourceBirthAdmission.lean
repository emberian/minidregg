/-
Tuple-indexed current-law admission for a grain-backed birth. No independent
bare-birth or marker-only grain acceptance is composed here: every request
and policy projection is derived from the one composite tuple.
-/
import Kernel.GrainResourceBirthTransaction

namespace Minidregg.Kernel.GrainResourceBirthAdmission

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Kernel
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

abbrev Source := GrainResourceBirthController.Source
abbrev Tariff := GrainResourceBirthController.Tariff
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DeclaredResourceController.Durable
abbrev Ambient := DeclaredResourceController.Ambient

/-- Every composite native envelope uses one operation-use nullifier. The
separate birth identity marker is still installed by the combined authority
patch and names replay/conflict at the durable birth journal. -/
def useMarker {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (tariff : Tariff) (source : Source) : Nat :=
  DeclaredResourceController.operationMarker deployment.domain profile.semantics
    (source.grainCommand tariff)

/-- A bare-birth signature header uses the birth identity marker. Every
composite native envelope is instead checked against the distinct derived
grain marker; even an equal request would have a different signed header.
This is an exact header inequality, independent of any hash injectivity. -/
theorem composite_header_differs_from_bare {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : Deployment} {pins : ResourceBirth.FactoryPins}
    {durable : Durable} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (key : Minidregg.Theory.CredentialSigningKey.KeyRecord)
    (request : SomeRequest) (validUntil validUntil' : Nat) :
    CredentialSignatureAdmission.header birth.prepared.pre.authority.snapshot key
      (useMarker profile deployment tariff source) request validUntil ≠
    CredentialSignatureAdmission.header birth.prepared.pre.authority.snapshot key
      source.birth.authorityNullifier request validUntil' := by
  intro same
  have markerEqual := congrArg CredentialSignedEnvelopeController.SignedHeader.nullifier same
  rcases birth.shape with ⟨_, _, _, _, _, _, _, _, _, distinct⟩
  exact distinct markerEqual.symm

/-- Both strict signed carriers describe this exact loaded, source-derived
operation. The two authority envelope fields must name the same one authority
incidence; neither a second authority leg nor an unchecked extra signature is
silently admitted. -/
def SignedShape {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (tariff : Tariff) (source : Source)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) : Prop :=
  GrainResourceBirthPolicyController.SourceBound deployment.domain profile.semantics
    tariff source ingress ∧
  ingress.birth.ingress.credentials.allocations.length = source.birth.createRequests.length ∧
  ingress.birth.ingress.credentials.sources.length = source.birth.resourceBatch.operations.length ∧
  ingress.grain.2.2.targetEnvelopes.length = (source.grainCommand tariff).targets.length ∧
  ingress.grain.2.2.observeEnvelopes.length = (source.grainCommand tariff).targets.length ∧
  ingress.birth.ingress.credentials.authority.envelope =
    ingress.grain.2.2.authorityEnvelope

instance signedShapeDecidable {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (tariff : Tariff) (source : Source)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) :
    Decidable (SignedShape profile deployment tariff source ingress) := by
  unfold SignedShape
  infer_instance

abbrev Branch (tariff : Tariff) (source : Source) :=
  ResourceBirthPolicyController.Concrete.Branch source.birth ⊕
    DeclaredResourceController.TargetIndex (source.grainCommand tariff)

def credentialFor {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {tariff : Tariff} {source : Source}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (shape : SignedShape profile deployment tariff source ingress) :
    Branch tariff source → ResourceBirthPolicyController.Concrete.BranchCredential
  | .inl .factory => ingress.birth.ingress.credentials.factory
  | .inl .authority => ingress.birth.ingress.credentials.authority
  | .inl (.allocation index) =>
      ingress.birth.ingress.credentials.allocations.get (Fin.cast shape.2.1.symm index)
  | .inl (.source index) =>
      ingress.birth.ingress.credentials.sources.get (Fin.cast shape.2.2.1.symm index)
  | .inr index =>
      ⟨some (source.grainCommand tariff).targets[index].capability,
        ingress.grain.2.2.targetEnvelopes.get (Fin.cast shape.2.2.2.1.symm index)⟩

def observationEnvelope {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {tariff : Tariff} {source : Source}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (shape : SignedShape profile deployment tariff source ingress)
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff)) : List UInt8 :=
  ingress.grain.2.2.observeEnvelopes.get (Fin.cast shape.2.2.2.2.1.symm index)

def branchPrimary {tariff : Tariff} {source : Source} :
    Branch tariff source → GrainResourceBirthTransaction.Incidence tariff source
  | .inl branch => .inl (ResourceBirthPolicyController.Concrete.branchPrimary branch)
  | .inr index => .inr index

def branchRequest {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (height : Height) : Branch tariff source → PackedEffectRequest
  | .inl (.source index) => ⟨.account, CanonicalResourceEffect.batchSourceRequest
      CanonicalCellRegistry.sourceEncoding birth.prepared.pre.book.payload
      (GrainResourceBirthTransaction.resourceContexts birth height) source.birth index⟩
  | .inl .factory =>
      (GrainResourceBirthTransaction.rawLeg birth grain height () (.inl .factory)).request
  | .inl .authority =>
      (GrainResourceBirthTransaction.rawLeg birth grain height () (.inl .authority)).request
  | .inl (.allocation index) =>
      (GrainResourceBirthTransaction.rawLeg birth grain height () (.inl (.allocation index))).request
  | .inr index =>
      (GrainResourceBirthTransaction.rawLeg birth grain height () (.inr index)).request

def branchIdentity {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (height : Height) (branch : Branch tariff source) :
    AuthorizationDeclaration.RequestWire :=
  AuthorizationDeclaration.encodeRequest (branchRequest birth grain height branch)

/-- Factory and Book laws receive only their own old/post cut plus the
canonical user-authored birth draft. Grain laws receive the two explicitly
observed grain target states and the source-derived command. No newborn
authority or unrelated Book balance is projected into another law. -/
def project {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (height : Height) (branch : Branch tariff source)
    (logical : (incidence : GrainResourceBirthTransaction.Incidence tariff source) →
      Store.Store ((GrainResourceBirthTransaction.layout birth grain).storeLayout incidence)) :
    Minidregg.Pred.State :=
  let wanted := branchRequest birth grain height branch
  let common := CanonicalRuntimeProfile.requestSlots wanted.2
  match branch with
  | .inl birthBranch =>
      let metadata :=
        [("request/creator", Int.ofNat source.birth.creator.value),
         ("birth/count", Int.ofNat source.birth.births.length),
         ("fee/amount", Int.ofNat source.birth.fee.amount),
         ("birth/mode/grain-backed", 1)]
      let draft := ResourceBirthPolicyController.Concrete.bytesSlots "command/bytes" 0
        (ResourceBirthPolicyController.Concrete.userCommandBytes source.birth)
      let resource := match birthBranch with
        | .factory => ResourceBirthPolicyController.Concrete.bytesSlots
            "cell/factory/bytes" 0
            (DeclaredEffectCell.materializer.codec.encode (logical (.inl .factory)))
        | .source _ => match wanted with
          | ⟨.account, request⟩ => CanonicalAccountView.slots
              (CanonicalResourceKernel.logicalBook (logical (.inl .book))) request.target.value
          | _ => []
        | _ => []
      ⟨common ++ metadata ++ draft ++ resource⟩
  | .inr index =>
      let command := source.grainCommand tariff
      let ownSlots := ResourceBirthPolicyController.Concrete.bytesSlots "resource/bytes" 0
        (command.targets[index].materializer.codec.encode (logical (.inr index))) ++
        DeclaredResourceController.targetProjection command.targets[index]
          (grain.targets index).pre.logical (logical (.inr index))
      let observed := DeclaredResourceController.jointSlots command.targets fun i =>
        ResourceBirthPolicyController.Concrete.bytesSlots "resource/bytes" 0
          (command.targets[i].materializer.codec.encode (logical (.inr i))) ++
         DeclaredResourceController.targetProjection command.targets[i]
           (grain.targets i).pre.logical (logical (.inr i))
      ⟨common ++ ResourceBirthPolicyController.Concrete.bytesSlots "command/bytes" 0
        (DeclaredResourceController.commandCodec.encode command) ++ ownSlots ++ observed⟩

inductive Reject where
  | tuple
  | physical
  | metadata (reason : ResourceBirthPolicyController.Reject)
  | ambiguousRequests
  | capability
  | credentialShape
  | nativeSignature (reason : CredentialSignatureAdmission.Reject)
  | policySourceUnavailable
  | policySourceConflict
  | policyUnavailable
  | policyInputRange
  | policyCastAlias
  | policyRejected
  deriving Repr

/-- This carries one fixed tuple and its union physical proof. Every later
policy step, native request and final intent must consume this exact value. -/
structure Pending {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (pins : ResourceBirth.FactoryPins) (durable : Durable)
    (ambient : Ambient) (tariff : Tariff) (source : Source)
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)) where
  private mk ::
  tuple : PreparedTuple (GrainResourceBirthTransaction.plan birth grain ambient.height)
  physical : GrainResourceBirthTransaction.PhysicalShape birth grain
  checked : ResourceBirthPolicyController.Checked pins CanonicalCellRegistry.sourceEncoding
    birth.prepared.pre.authority.snapshot.authState source.birth
  templateBound : ResourceBirthPolicyController.Concrete.TemplateBound profile.template
    birth.prepared.pre.authority.snapshot.authState ambient.height source.birth
  requestsDistinct : Function.Injective (branchIdentity birth grain ambient.height)

def preparePending {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (pins : ResourceBirth.FactoryPins) (durable : Durable)
    (ambient : Ambient) (tariff : Tariff) (source : Source)
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)) :
    Except Reject (Pending profile deployment pins durable ambient tariff source birth grain) := do
  let tuple ← match GrainResourceBirthTransaction.prepareTuple birth grain with
    | none => .error .tuple
    | some tuple => .ok tuple
  let physical ←
    (if shape : GrainResourceBirthTransaction.PhysicalShape birth grain then
      Except.ok (PLift.up shape) else Except.error .physical :
        Except Reject (PLift (GrainResourceBirthTransaction.PhysicalShape birth grain)))
  let checked ← (ResourceBirthPolicyController.check pins
    CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
    source.birth).mapError Reject.metadata
  let templateBound ← (ResourceBirthPolicyController.Concrete.checkTemplateAt profile.template
      birth.prepared.pre.authority.snapshot.authState ambient.height source.birth).mapError
    Reject.metadata
  if distinct : Function.Injective (branchIdentity birth grain ambient.height) then
    return ⟨tuple, physical.down, checked.down, templateBound.down, distinct⟩
  else .error .ambiguousRequests

/-- Changing the primary selector for one policy branch leaves every old cell,
validated patch, physical guard and joint source exactly the same. The native
composite tuple retained in `pending.tuple` remains factory-primary. -/
def Pending.branchTuple {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source) :
    PreparedTuple (GrainResourceBirthTransaction.plan birth grain ambient.height) :=
  { pending.tuple with primary := branchPrimary branch }

def Pending.branchStep {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source) : CanonicalPolicyAdmission.PolicyStepContext :=
  CanonicalPolicyAdmission.PolicyStepContext.ofPreparedTuple
    (fun _ logical => project birth grain ambient.height branch logical)
    profile.semantics (pending.branchTuple branch)

theorem Pending.branchStep_states {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source) :
    (pending.branchStep branch).oldState =
      project birth grain ambient.height branch pending.tuple.logicalPre ∧
    (pending.branchStep branch).newState =
      project birth grain ambient.height branch pending.tuple.logicalPost :=
  ⟨rfl, rfl⟩

def Pending.branchConfig {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source) : CanonicalPolicyAdmission.CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile
    birth.prepared.pre.authority.snapshot
    ⟨CanonicalCellRegistry.fetchPolicySource deployment.domain birth.prepared.pre.directory.directory⟩
    (CredentialAuthorityPolicyRegistry.sourcePortal birth.prepared.pre.authority.snapshot
      (useMarker profile deployment tariff source))
    (pending.branchStep branch)

/-- The branch tag must match the *complete* encoded request before its
compiled witness can be accepted. This includes the composite factory mode,
the two grain actions and their source-bound nonce. -/
def Pending.portal {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain) : Portal :=
  let base := CredentialAuthorityPolicyRegistry.domainPortal
    birth.prepared.pre.authority.snapshot
    (CredentialAuthorityPolicyRegistry.sourcePortal birth.prepared.pre.authority.snapshot
      (useMarker profile deployment tariff source))
  { base with
    PolicyWitness := Branch tariff source × CanonicalPolicyAdmission.CompiledPolicyWitness F
    policyAddress := fun witness => witness.2.address
    verifyCommittedPolicy := fun address kind request witness =>
      decide (AuthorizationDeclaration.encodeRequest ⟨kind, request⟩ =
        branchIdentity birth grain ambient.height witness.1) &&
      (pending.branchConfig witness.1).portal.verifyCommittedPolicy
        address request witness.2 }

theorem Pending.dispatched_request_exact {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    {kind : ResourceKind} (request : Request kind) (address : Digest)
    (witness : pending.portal.PolicyWitness)
    (accepted : pending.portal.verifyCommittedPolicy address request witness = true) :
    (⟨kind, request⟩ : PackedEffectRequest) =
      branchRequest birth grain ambient.height witness.1 ∧
    (pending.branchConfig witness.1).portal.verifyCommittedPolicy
      address request witness.2 = true := by
  have checks := Bool.and_eq_true_iff.mp accepted
  constructor
  · have wire := of_decide_eq_true checks.1
    have decoded := congrArg AuthorizationDeclaration.decodeRequest wire
    simpa [branchIdentity, AuthorizationDeclaration.decodeRequest_encodeRequest] using decoded
  · exact checks.2

def Pending.liftEvidence {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source)
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence (pending.branchConfig branch).portal
      birth.prepared.pre.authority.snapshot.authState request) :
    Evidence pending.portal birth.prepared.pre.authority.snapshot.authState request := by
  unfold Pending.portal Pending.branchConfig CredentialAuthorityPolicyRegistry.config
    CanonicalPolicyAdmission.CanonicalPolicyConfig.portal at *
  cases evidence with
  | signature witness epoch verified => exact .signature witness epoch verified
  | proof witness verified => exact .proof witness verified
  | capability cap commitment commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified commitmentVerified
      membershipVerified issuerVerified selfRevocationVerified ancestorVerified channelVerified =>
      exact .capability cap commitment commitmentWitness membershipWitness issuerWitness
        selfRevocationWitness useWitness semantic useVerified commitmentVerified
        membershipVerified issuerVerified selfRevocationVerified ancestorVerified channelVerified

def Pending.liftAuthorization {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source)
    (authorized : Authorized (pending.branchConfig branch).portal
      birth.prepared.pre.authority.snapshot.authState
      (branchRequest birth grain ambient.height branch).2) :
    Authorized pending.portal birth.prepared.pre.authority.snapshot.authState
      (branchRequest birth grain ambient.height branch).2 where
  evidence := pending.liftEvidence branch authorized.evidence
  policyWitness := (branch, authorized.policyWitness)
  policyMembershipWitness := authorized.policyMembershipWitness
  policyEpochExact := authorized.policyEpochExact
  policyRevisionExact := authorized.policyRevisionExact
  policyAddressExact := authorized.policyAddressExact
  policyMembershipVerified := authorized.policyMembershipVerified
  policyVerified := by
    change (decide (AuthorizationDeclaration.encodeRequest
      (branchRequest birth grain ambient.height branch) =
        branchIdentity birth grain ambient.height branch) &&
      (pending.branchConfig branch).portal.verifyCommittedPolicy _ _
        authorized.policyWitness) = true
    simp only [branchIdentity, decide_true, Bool.true_and]
    exact authorized.policyVerified

def requiresCapability {tariff : Tariff} {source : Source} :
    Branch tariff source → Bool
  | .inl branch => ResourceBirthPolicyController.Concrete.branchRequiresCapability branch
  | .inr _ => true

/-- The immutable policy-source guard is retained beside its exact native
receipt and typed authorization; the final union intent must include it. -/
structure CheckedBranch {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source)
    (credential : ResourceBirthPolicyController.Concrete.BranchCredential) where
  receipt : CredentialSignatureAdmission.CheckedSignature birth.prepared.pre.authority.snapshot
  envelopeExact : receipt.envelopeBytes = credential.envelope
  policySource : CanonicalCellRegistry.LoadedPolicySource deployment.domain
    birth.prepared.pre.directory.directory
    (birth.prepared.pre.authority.snapshot.authState.policyAddress
      (branchRequest birth grain ambient.height branch).2.policyId
      (branchRequest birth grain ambient.height branch).2.policyRevision)
  authorization : Authorized pending.portal birth.prepared.pre.authority.snapshot.authState
    (branchRequest birth grain ambient.height branch).2
  modeBound : requiresCapability branch = true →
    authorization.evidence.capabilityValue.isSome = true

def Pending.admitBranch {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source)
    (credential : ResourceBirthPolicyController.Concrete.BranchCredential)
    (receipt : CredentialSignatureAdmission.CheckedSignature birth.prepared.pre.authority.snapshot) :
    Except Reject (CheckedBranch pending branch credential) := do
  if exactEnvelope : receipt.envelopeBytes = credential.envelope then
    let wanted := branchRequest birth grain ambient.height branch
    let step := pending.branchStep branch
    let config := pending.branchConfig branch
    let old := birth.prepared.pre.authority.snapshot.authState
    let policySource ← match CanonicalCellRegistry.loadPolicySource deployment.domain
        birth.prepared.pre.directory.directory
        (old.policyAddress wanted.2.policyId wanted.2.policyRevision) with
      | none => .error .policySourceUnavailable
      | some loaded => .ok loaded
    let store : CanonicalPolicyRegistry.PayloadStore :=
      ⟨CanonicalCellRegistry.fetchPolicySource deployment.domain
        birth.prepared.pre.directory.directory⟩
    let evidence : Evidence config.portal old wanted.2 ←
      if requiresCapability branch then
        match credential.capability with
        | none => .error .capability
        | some identifier =>
            match CredentialAuthorityPolicyRegistry.sourceCapabilityEvidence
                profile.compilerProfile birth.prepared.pre.authority.snapshot
                store (useMarker profile deployment tariff source) step
                wanted.2 identifier receipt with
            | none => .error .capability
            | some evidence => .ok evidence
      else
        match credential.capability with
        | some identifier =>
            match CredentialAuthorityPolicyRegistry.sourceCapabilityEvidence
                profile.compilerProfile birth.prepared.pre.authority.snapshot
                store (useMarker profile deployment tariff source) step
                wanted.2 identifier receipt with
            | none => .error .capability
            | some evidence => .ok evidence
        | none =>
            if epoch : wanted.2.subjectKeyEpoch = old.subjectKeyEpoch wanted.2.subject then
              if verified : config.portal.verifySignature wanted.2 receipt = true then
                .ok (.signature receipt epoch verified)
              else .error (Reject.nativeSignature .sourceBinding)
            else .error (Reject.nativeSignature .sourceBinding)
    if epoch : wanted.2.policyEpoch = old.policyEpoch wanted.2.policyId then
      if revision : wanted.2.policyRevision = old.policyRevision wanted.2.policyId then
        match config.registry.resolve wanted.2.policyId wanted.2.policyRevision with
        | none => .error .policyUnavailable
        | some committed =>
            let witness := CanonicalPolicyAdmission.canonicalWitness
              profile.compilerProfile.compiler committed step.oldState step.newState
            if inputsInRange profile.compilerProfile.compiler
                committed.record.predicate witness.oldState witness.newState != true then
              .error .policyInputRange
            else if !decide (castInjOn F
                (intsOf committed.record.predicate
                  witness.oldState witness.newState)) then
              .error .policyCastAlias
            else
              match CanonicalPolicyAdmission.admit config old wanted.2 evidence witness
                  (.policy wanted.2.policyId wanted.2.policyRevision) epoch revision with
              | none => .error .policyRejected
              | some admitted =>
                  let authorization := pending.liftAuthorization branch admitted
                  if modeBound : requiresCapability branch = true →
                      authorization.evidence.capabilityValue.isSome = true then
                    .ok ⟨receipt, exactEnvelope, policySource, authorization, modeBound⟩
                  else .error .capability
      else .error .policyUnavailable
    else .error .policyUnavailable
  else .error .credentialShape

def Pending.admitBranchNative {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    (pending : Pending profile deployment pins durable ambient tariff source birth grain)
    (branch : Branch tariff source)
    (native : CredentialSignatureIO.NativeConfig)
    (credential : ResourceBirthPolicyController.Concrete.BranchCredential) :
    IO (Except Reject (CheckedBranch pending branch credential)) := do
  match ← CredentialSignatureAdmission.verifyNative native
      birth.prepared.pre.authority.snapshot
      (useMarker profile deployment tariff source)
      (branchRequest birth grain ambient.height branch).2 credential.envelope with
  | .error reason => return .error (.nativeSignature reason)
  | .ok receipt => return pending.admitBranch branch credential receipt

def readContext {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source) :
    ResourceObservationAdmission.Context deployment durable :=
  ⟨birth.prepared.pre.directory, birth.prepared.pre.authority⟩

def readRequest {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff)) :
    Request (source.grainCommand tariff).targets[index].kind :=
  let command := source.grainCommand tariff
  { DeclaredResourceController.requestFor birth.prepared.pre.authority.snapshot
      profile.semantics ambient command command.targets[index]
      (grain.targets index).before.payload.root with
    verb := DeclaredResourceController.observeVerb command.targets[index].kind
    effectsDigest := (Sp800185Cshake256.hash
      "DREGG.RESOURCE.TRANSACTION.OBSERVE/v3".toUTF8.toList
      ((Tower256ConcreteBackend.StreamCodec.product
        Tower256ConcreteBackend.bytesStream Tower256ConcreteBackend.StreamCodec.nat).encode
        (DeclaredResourceController.commandBytes birth.prepared.pre.authority.snapshot.domain
          profile.semantics command, command.targets[index].target))).digest }

def readPreparation {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff)) :=
  ResourceObservationAdmission.prepare (readContext birth) profile
    (readRequest birth grain index) (useMarker profile deployment tariff source)
    ((source.grainCommand tariff).targets[index].observeCapability.getD ⟨0⟩)
    (DeclaredResourceController.commandCodec.encode (source.grainCommand tariff))

structure ReadLeg {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff))
    (envelope : List UInt8) where
  capabilityPresent : (source.grainCommand tariff).targets[index].observeCapability.isSome = true
  selected : ResourceObservationAdmission.Prepared (readContext birth) profile
    (readRequest birth grain index) (useMarker profile deployment tariff source)
    ((source.grainCommand tariff).targets[index].observeCapability.getD ⟨0⟩)
    (DeclaredResourceController.commandCodec.encode (source.grainCommand tariff))
  checked : ResourceObservationAdmission.Checked selected envelope

def verifyRead {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff))
    (native : CredentialSignatureIO.NativeConfig) (envelope : List UInt8) :
    IO (Except Reject (ReadLeg birth grain index envelope)) := do
  if present : (source.grainCommand tariff).targets[index].observeCapability.isSome = true then
    match readPreparation birth grain index with
    | .error _ => return .error .policyRejected
    | .ok ready =>
        match ← ResourceObservationAdmission.check native ready envelope with
        | .error _ => return .error .policyRejected
        | .ok checked => return .ok ⟨present, ready, checked⟩
  else return .error .capability

def branches (tariff : Tariff) (source : Source) : List (Branch tariff source) :=
  (ResourceBirthPolicyController.Concrete.policyBranches source.birth.createRequests.length
    source.birth.resourceBatch.operations.length).map Sum.inl ++
  (List.finRange (source.grainCommand tariff).targets.length).map Sum.inr

theorem mem_branches {tariff : Tariff} {source : Source}
    (branch : Branch tariff source) : branch ∈ branches tariff source := by
  cases branch with
  | inl birthBranch =>
      simp [branches, ResourceBirthPolicyController.Concrete.mem_policyBranches birthBranch]
  | inr index => simp [branches]

def policySourceGuards {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {pending : Pending profile deployment pins durable ambient tariff source birth grain}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (signed : SignedShape profile deployment tariff source ingress)
    (checked : (branch : Branch tariff source) →
      CheckedBranch pending branch (credentialFor signed branch)) : List ReadGuard :=
  (branches tariff source).map fun branch =>
    ⟨⟨(checked branch).policySource.readGuard.1⟩,
      (checked branch).policySource.readGuard.2⟩

def PolicyGuardShape {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {pending : Pending profile deployment pins durable ambient tariff source birth grain}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (signed : SignedShape profile deployment tariff source ingress)
    (checked : (branch : Branch tariff source) →
      CheckedBranch pending branch (credentialFor signed branch)) : Prop :=
  (∀ guard ∈ policySourceGuards signed checked,
    guard.cellId ∉ (GrainResourceBirthTransaction.writes birth grain).map DataWrite.cellId) ∧
  (∀ guard ∈ policySourceGuards signed checked,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance policyGuardShapeDecidable {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {pending : Pending profile deployment pins durable ambient tariff source birth grain}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (signed : SignedShape profile deployment tariff source ingress)
    (checked : (branch : Branch tariff source) →
      CheckedBranch pending branch (credentialFor signed branch)) :
    Decidable (PolicyGuardShape signed checked) := by
  unfold PolicyGuardShape
  infer_instance

/-- All signed incidences, including both current observe grants, must pass
before a caller can obtain this private-constructor value. -/
structure Accepted {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (pins : ResourceBirth.FactoryPins) (durable : Durable)
    (ambient : Ambient) (tariff : Tariff) (source : Source)
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) where
  private mk ::
  signed : SignedShape profile deployment tariff source ingress
  pending : Pending profile deployment pins durable ambient tariff source birth grain
  observations : (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff)) →
    ReadLeg birth grain index (observationEnvelope signed index)
  checked : (branch : Branch tariff source) →
    CheckedBranch pending branch (credentialFor signed branch)
  guardShape : PolicyGuardShape signed checked

def admitDecodedNative {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (pins : ResourceBirth.FactoryPins) (durable : Durable)
    (ambient : Ambient) (tariff : Tariff) (source : Source)
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff))
    (native : CredentialSignatureIO.NativeConfig)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) :
    IO (Except Reject (Accepted profile deployment pins durable ambient tariff source birth grain ingress)) := do
  if signed : SignedShape profile deployment tariff source ingress then
    match preparePending profile deployment pins durable ambient tariff source birth grain with
    | .error reason => return .error reason
    | .ok pending =>
        let observationResults ← DeclaredResourceController.collectIO
          (fun index => verifyRead birth grain index native (observationEnvelope signed index))
        match observationResults with
        | .error reason => return .error reason
        | .ok observations =>
            let factory ← pending.admitBranchNative (.inl .factory) native
              (credentialFor signed (.inl .factory))
            match factory with
            | .error reason => return .error reason
            | .ok factory =>
                match ← pending.admitBranchNative (.inl .authority) native
                    (credentialFor signed (.inl .authority)) with
                | .error reason => return .error reason
                | .ok authority =>
                    match ← DeclaredResourceController.collectIO (fun index =>
                        pending.admitBranchNative (.inl (.allocation index)) native
                          (credentialFor signed (.inl (.allocation index)))) with
                    | .error reason => return .error reason
                    | .ok allocations =>
                        match ← DeclaredResourceController.collectIO (fun index =>
                            pending.admitBranchNative (.inl (.source index)) native
                              (credentialFor signed (.inl (.source index)))) with
                        | .error reason => return .error reason
                        | .ok sources =>
                            match ← DeclaredResourceController.collectIO (fun index =>
                                pending.admitBranchNative (.inr index) native
                                  (credentialFor signed (.inr index))) with
                            | .error reason => return .error reason
                            | .ok targets =>
                                let checked : (branch : Branch tariff source) →
                                    CheckedBranch pending branch (credentialFor signed branch) :=
                                  fun branch => match branch with
                                    | .inl .factory => factory
                                    | .inl .authority => authority
                                    | .inl (.allocation index) => allocations index
                                    | .inl (.source index) => sources index
                                    | .inr index => targets index
                                if guards : PolicyGuardShape signed checked then
                                  return .ok ⟨signed, pending, observations, checked, guards⟩
                                else return .error .policySourceConflict
  else return .error .credentialShape

def Accepted.portals {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :
    GrainResourceBirthTransaction.Incidence tariff source → Portal :=
  fun _ => accepted.pending.portal

def Accepted.admissionEvidence {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :
    accepted.pending.tuple.AdmissionEvidence accepted.portals where
  modes incidence := by
    cases incidence with
    | inl leg =>
        cases leg with
        | factory => exact ()
        | book =>
            exact
              { factory :=
                  { checked := accepted.pending.checked
                    authorized := (accepted.checked (.inl .factory)).authorization }
                admission := birth.prepared.post.resources.admission
                sources := fun position =>
                  (accepted.checked (.inl (.source position))).authorization }
        | authority => exact ()
        | allocation index =>
            exact (ResourceBirthController.allocationCandidate pins
              CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
              birth.prepared.post.allocated
              (ResourceBirthPolicyController.Concrete.creation source.birth index)
              (List.get_mem _ _) ambient.height).modeEvidence
    | inr index => exact (grain.targets index).candidate.modeEvidence
  authorizations incidence := by
    cases incidence with
    | inl leg =>
        cases leg with
        | factory => exact (accepted.checked (.inl .factory)).authorization
        | book =>
            exact (accepted.checked (.inl (.source
              (CanonicalResourceEffect.feePosition source.birth)))).authorization
        | authority => exact (accepted.checked (.inl .authority)).authorization
        | allocation index =>
            exact (accepted.checked (.inl (.allocation index))).authorization
    | inr index => exact (accepted.checked (.inr index)).authorization
  disclosure := fun _ => .sealed
  disclosureAllowed incidence := by
    cases incidence with
    | inl leg => cases leg <;> trivial
    | inr _ => trivial

def Accepted.apex {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (_accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :
    Digest :=
  CanonicalCellRegistry.sourceEncoding.hashBytes
    ("DREGG/GRAIN-RESOURCE-BIRTH/APEX/v1".toUTF8.toList ++
      ingress.bytes)

def Accepted.declaration {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :=
  accepted.pending.tuple.toDeclaration accepted.portals accepted.apex

def Accepted.legs {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :
    accepted.declaration.AcceptedLegs :=
  accepted.pending.tuple.accept accepted.portals accepted.apex accepted.admissionEvidence

theorem Accepted.post_exact {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress)
    (incidence : GrainResourceBirthTransaction.Incidence tariff source) :
    accepted.declaration.post accepted.legs incidence =
      (GrainResourceBirthTransaction.validated birth grain ambient.height incidence).apply :=
  (accepted.pending.tuple.accepted_posts_exact accepted.portals accepted.apex
    accepted.admissionEvidence incidence).trans (by rfl)

/-- The CAS observes every physical source and every admitted policy source.
Read-only source cells may overlap each other, but none may overlap a write. -/
def Accepted.readGuards {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress) :
    List ReadGuard :=
  GrainResourceBirthTransaction.readGuards birth grain ++
    policySourceGuards accepted.signed accepted.checked

theorem Accepted.readGuards_readonly {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress)
    (guard : ReadGuard) (member : guard ∈ accepted.readGuards) :
    guard.cellId ∉ (GrainResourceBirthTransaction.writes birth grain).map DataWrite.cellId := by
  rcases List.mem_append.mp member with physical | policy
  · exact accepted.pending.physical.2.2.2.1 guard physical
  · exact accepted.guardShape.1 guard policy

theorem Accepted.readGuards_exact {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : Accepted profile deployment pins durable ambient tariff source birth grain ingress)
    (guard : ReadGuard) (member : guard ∈ accepted.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  rcases List.mem_append.mp member with physical | policy
  · exact accepted.pending.physical.2.2.2.2 guard physical
  · exact accepted.guardShape.2 guard policy

end Minidregg.Kernel.GrainResourceBirthAdmission
