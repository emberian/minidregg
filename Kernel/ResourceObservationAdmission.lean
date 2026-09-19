/- Resource-local observation admission shared by native reads and joint
transactions. Every policy sees only its own unchanged canonical payload and
its own sparse account cut. Selection, credentials and committed policy source
all come from one loaded image; no foreign state enters this admission step. -/
import Compiler.CanonicalRuntimeProfile
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.ResourceTargetAdmission
import Compiler.CanonicalAccountView
import Compiler.ResourceAuthorityProjection
import Kernel.ContentResource
import Kernel.DeclaredResourceProjection

namespace Minidregg.Kernel.ResourceObservationAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Registry := CanonicalCellRegistry.registry

structure Context (deployment : Deployment) (durable : Durable) where
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot

variable {deployment : Deployment} {durable : Durable}

def observeVerb : (kind : ResourceKind) → Verb kind
  | .object => .observeObject
  | .account => .observeAccount
  | .program => .observeProgram

def book (context : Context deployment durable) : Option CanonicalResourceKernel.Book :=
  match context.directory.directory.slots deployment.resourceBookId with
  | .present packed =>
      if CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId packed then
        match packed with
        | ⟨.resourceBook, payload⟩ => CanonicalResourcePageMaterializer.bookAt payload.logical
        | _ => none
      else none
  | _ => none

def balances (context : Context deployment durable) (kind : ResourceKind) (target : Nat) :
    Option (List (Nat × Int)) :=
  if kind = .account then (book context).map (fun value => CanonicalAccountView.accountCut value target)
  else some []

def readPatch (kind : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer kind)) :
    Patch (CanonicalCellRegistry.schema kind) Digest where
  expectedPreRoot := pre.root
  fieldFootprint := ∅
  resourceFootprint := ∅
  fieldWrites := []
  resourceWrites := []

def readFamily {kind : ResourceKind} (wanted : Request kind)
    (physical : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer physical)) :
    SemanticEffectFamily (CanonicalCellRegistry.schema physical)
      (CanonicalCellRegistry.materializer physical) Unit where
  Declaration := Unit
  declarationCodec := CredentialAuthorityEffects.unitCodec
  pre := pre
  request := fun _ => ⟨kind, wanted⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CredentialAuthorityEffects.unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ logical => logical = pre.logical
  effectDigest := fun _ => wanted.effectsDigest
  patch := fun _ _ => readPatch physical pre
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

def readCandidate {kind : ResourceKind} (wanted : Request kind)
    (physical : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer physical))
    (_rootExact : wanted.preStateRoot = pre.root) :
    PolicyInstall.Candidate (readFamily wanted physical pre) pre () () :=
  match checked : validate (CanonicalCellRegistry.materializer physical) pre (readPatch physical pre) with
  | .accepted validated =>
      { preStateBound := rfl, modeEvidence := (), validated := validated
        postcondition := by
          change ({ fields := pre.logical.fields, resources := pre.logical.resources } :
            LogicalState (CanonicalCellRegistry.schema physical)) = pre.logical
          rfl }
  | .rejected _ => False.elim (by
      simp [validate, readPatch, Patch.namedFields, Patch.namedResources] at checked)

def resourceSlots (target : Nat) : (kind : CanonicalCellRegistry.Kind) →
    LogicalState (CanonicalCellRegistry.schema kind) → List (String × Int)
  | .content, logical =>
      match HyperdocumentContentPageMaterializer.pageAt logical with
      | some page => ContentResource.project page page ⟨[]⟩
      | none => []
  | .declaredObject, logical | .accountMetadata, logical | .declaredProgram, logical =>
      match DeclaredEffectPageMaterializer.pageAt logical with
      | some page => DeclaredResourceProjection.project target page page
      | none => []
  | _, _ => []

def sourceStore (context : Context deployment durable) : CanonicalPolicyRegistry.PayloadStore where
  fetch := CanonicalCellRegistry.fetchPolicySource deployment.domain context.directory.directory

variable {F : Type} [Field F] [DecidableEq F] {kind : ResourceKind}

/-- Preparation retains the actual physical role/root and current source
coordinates; a request supplied to this shared primitive cannot turn an
ordinary mutation into an observation or select an internal authority cell. -/
structure Prepared (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (wanted : Request kind) (marker : Nat) (capability : CapabilityId) (contextBytes : List UInt8) where
  private mk ::
  observed : ResourceTargetAdmission.Observed deployment context.directory.directory kind
    wanted.target.value wanted.preStateRoot
  observeExact : wanted.verb = observeVerb kind
  domainExact : wanted.domain = deployment.domain
  semanticsExact : wanted.semantics = profile.semantics
  policyExact : wanted.policyId.value = wanted.target.value
  epochExact : wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId
  revisionExact : wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId
  accountBalances : List (Nat × Int)
  balancesExact : balances context kind wanted.target.value = some accountBalances

private def refused : String := "observation refused"

def prepare (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (wanted : Request kind) (marker : Nat) (capability : CapabilityId) (contextBytes : List UInt8) :
    Except String (Prepared context profile wanted marker capability contextBytes) :=
  match ResourceTargetAdmission.observe deployment context.directory.directory kind
      wanted.target.value wanted.preStateRoot with
  | none => .error refused
  | some observed =>
      if observeExact : wanted.verb = observeVerb kind then
        if domainExact : wanted.domain = deployment.domain then
          if semanticsExact : wanted.semantics = profile.semantics then
            if policyExact : wanted.policyId.value = wanted.target.value then
              if epochExact : wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId then
                if revisionExact : wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId then
                  match balancesExact : balances context kind wanted.target.value with
                  | none => .error refused
                  | some values => .ok ⟨observed, observeExact, domainExact, semanticsExact,
                      policyExact, epochExact, revisionExact, values, balancesExact⟩
                else .error refused
              else .error refused
            else .error refused
          else .error refused
        else .error refused
      else .error refused

variable {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
  {wanted : Request kind} {marker : Nat} {capability : CapabilityId} {contextBytes : List UInt8}

def project (prepared : Prepared context profile wanted marker capability contextBytes)
    (logical : LogicalState (CanonicalCellRegistry.schema prepared.observed.before.kind)) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 contextBytes ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceAuthorityProjection.bytesSlots "account/bytes" 0
      (CanonicalAccountView.balanceStream.encode prepared.accountBalances) ++
    prepared.accountBalances.map (fun pair => (s!"account/balance/{pair.1}", pair.2)) ++
    resourceSlots wanted.target.value prepared.observed.before.kind logical⟩

def step (prepared : Prepared context profile wanted marker capability contextBytes) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (readCandidate wanted prepared.observed.before.kind prepared.observed.before.payload prepared.observed.rootExact)

def policyConfig (prepared : Prepared context profile wanted marker capability contextBytes) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile context.authority.snapshot (sourceStore context)
    (sourceCapabilityPortal context.authority.snapshot marker) (step prepared)

def portal (prepared : Prepared context profile wanted marker capability contextBytes) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState wanted) := do
  let config := policyConfig prepared
  let evidence ← sourceCapabilityOnlyEvidence profile.compilerProfile context.authority.snapshot
    (sourceStore context) marker (step prepared) wanted capability signature
  let committed ← config.registry.resolve wanted.policyId wanted.policyRevision
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared).oldState (step prepared).newState
  CanonicalPolicyAdmission.admit config context.authority.snapshot.authState wanted
    evidence witness (.policy wanted.policyId wanted.policyRevision) prepared.epochExact prepared.revisionExact

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile wanted marker capability contextBytes)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState wanted
  authorized : authorize prepared signature = some authorization

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile wanted marker capability contextBytes) (envelope : List UInt8) :
    IO (Except String (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot marker wanted envelope with
  | .error _ => return .error refused
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return .error refused
        | some authorization => return .ok ⟨signature, exact, authorization, authorized⟩
      else return .error refused

omit [DecidableEq F] in
theorem read_preserves_resource (prepared : Prepared context profile wanted marker capability contextBytes) :
    (readCandidate wanted prepared.observed.before.kind prepared.observed.before.payload
      prepared.observed.rootExact).post.logical = prepared.observed.before.payload.logical :=
  (readCandidate wanted prepared.observed.before.kind prepared.observed.before.payload
    prepared.observed.rootExact).postcondition

omit [DecidableEq F] in
theorem policy_views_equal (prepared : Prepared context profile wanted marker capability contextBytes) :
    (step prepared).oldState = (step prepared).newState := by
  change project prepared prepared.observed.before.payload.logical =
    project prepared (readCandidate wanted prepared.observed.before.kind prepared.observed.before.payload
      prepared.observed.rootExact).post.logical
  rw [read_preserves_resource]

omit [DecidableEq F] in
theorem preparation_actual_root (prepared : Prepared context profile wanted marker capability contextBytes) :
    wanted.preStateRoot = prepared.observed.before.payload.root := prepared.observed.rootExact

omit [DecidableEq F] in
theorem preparation_observation_only (prepared : Prepared context profile wanted marker capability contextBytes) :
    wanted.verb = observeVerb kind := prepared.observeExact

theorem checked_exact_envelope (prepared : Prepared context profile wanted marker capability contextBytes)
    (envelope : List UInt8) (checked : Checked prepared envelope) :
    checked.signature.envelopeBytes = envelope := checked.envelopeExact

theorem checked_current_source (prepared : Prepared context profile wanted marker capability contextBytes)
    (envelope : List UInt8) (checked : Checked prepared envelope) :
    wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId ∧
      wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId :=
  ⟨checked.authorization.policyEpochExact, checked.authorization.policyRevisionExact⟩

end Minidregg.Kernel.ResourceObservationAdmission
