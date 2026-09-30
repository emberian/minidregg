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
import Theory.RoomAuthorization

namespace Minidregg.Kernel.ResourceObservationAdmission

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Registry := CanonicalCellRegistry.registry

structure Context (deployment : Deployment) (durable : Durable) where
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot

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

/-- An observation writes nothing: the empty patch. -/
def readPatch (kind : CanonicalCellRegistry.Kind) : Patch (CanonicalCellRegistry.layout kind) := []

def readFamily {kind : ResourceKind} (wanted : Request kind)
    (physical : CanonicalCellRegistry.Kind)
    (pre : Materialized (CanonicalCellRegistry.materializer physical)) :
    SemanticEffectFamily (CanonicalCellRegistry.layout physical)
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
  patch := fun _ _ => readPatch physical
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
  { preStateBound := rfl, modeEvidence := ()
    validated := (validate_accepts (CanonicalCellRegistry.materializer physical) pre pre.root
      (readPatch physical) rfl trivial).choose
    postcondition := rfl }

def resourceSlots (target : Nat) : (kind : CanonicalCellRegistry.Kind) →
    Store (CanonicalCellRegistry.layout kind) → List (String × Int)
  | .content, logical => ContentResource.project logical logical ⟨[]⟩
  | .declaredObject, logical | .accountMetadata, logical | .declaredProgram, logical =>
      DeclaredResourceProjection.project target logical logical
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
    (logical : Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) : Minidregg.Pred.State :=
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

/-! ## Room confidentiality at the controller (PRIVACY row 8)

The observation portal is the source-capability portal: it has no signature
and no proof witness, so no signature-mode or proof-mode evidence exists for an
observation, whoever signs. An admitted observation therefore invokes a
capability that is admissible for the exact request, and its scope reaches the
observed cell: `under X` for an `X` on the cell's parent chain, or an explicit
set naming it. For a cell in a room this is `RoomAuthorization.room_confidentiality`
at the controller, not a policy default. -/

/-- The signature-mode and proof-mode poles are refuted at this controller:
its portal has no witness for either. -/
theorem signature_mode_refuted
    (prepared : Prepared context profile wanted marker capability contextBytes) :
    IsEmpty (portal prepared).SignatureWitness ∧ IsEmpty (portal prepared).ProofWitness := by
  unfold portal policyConfig
  exact ⟨⟨fun witness => nomatch witness⟩, ⟨fun witness => nomatch witness⟩⟩

/-- **Controller room confidentiality.** Every authorization this controller
can hold for an observation is capability-mode, the invoked capability is
admissible for the exact request, and its scope reaches the observed cell only
through the cell's own parent chain or by naming it. -/
theorem controller_room_confidentiality
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (authorization : Authorized (portal prepared) context.authority.snapshot.authState wanted) :
    ∃ cap : Capability kind, ∃ commitment : Digest,
      authorization.evidence.capabilityValue = some (cap, commitment) ∧
      cap.Admissible context.authority.snapshot.authState wanted ∧
      ((∃ room, cap.scope.targets = .under room ∧
          context.authority.snapshot.authState.parent.Descends wanted.target.value room) ∨
        ∃ ts, cap.scope.targets = .explicit ts ∧ wanted.target ∈ ts) := by
  obtain ⟨noSignature, noProof⟩ := signature_mode_refuted prepared
  match authorization.evidence with
  | .signature witness _ _ => exact (noSignature.false witness).elim
  | .proof witness _ => exact (noProof.false witness).elim
  | .capability cap commitment _ _ _ _ _ semantic _ _ _ _ _ _ _ =>
      exact ⟨cap, commitment, rfl, semantic,
        RoomAuthorization.covers_cases semantic.scope.target⟩

/-- The capability an authorization invokes is exactly the stored record at
the requested capability identifier of the loaded authority cell. -/
theorem authorize_names_stored
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    {authorization : Authorized (portal prepared) context.authority.snapshot.authState wanted}
    (accepted : authorize prepared signature = some authorization) :
    ∃ stored, CredentialAuthorityState.readCapability context.authority.snapshot.cell kind capability = some stored ∧
      authorization.evidence.capabilityValue =
        some (stored.head, storedCapabilityDigest context.authority.snapshot stored) := by
  revert authorization
  unfold portal
  intro authorization accepted
  unfold authorize at accepted
  cases supplied : sourceCapabilityOnlyEvidence profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature with
  | none =>
    simp only [supplied, bind, Option.bind] at accepted
    exact absurd accepted (by simp)
  | some evidence =>
  cases resolved : (policyConfig prepared).registry.resolve wanted.policyId wanted.policyRevision with
  | none =>
    simp only [supplied, resolved, bind, Option.bind] at accepted
    exact absurd accepted (by simp)
  | some committed =>
  simp only [supplied, resolved, bind, Option.bind] at accepted
  have admitted := accepted
  obtain ⟨stored, read, named⟩ := sourceCapabilityOnlyEvidence_names_parent
    profile.compilerProfile context.authority.snapshot (sourceStore context) marker (step prepared)
    wanted capability signature supplied
  refine ⟨stored, read, ?_⟩
  rw [CanonicalPolicyAdmission.admit_preserves_evidence _ _ _ _ _ _ _ _ admitted]
  exact named

/-- Refusal: an observer — however valid their signature — whose named stored
capability is not admissible for the request is refused. -/
theorem controller_refuses_inadmissible
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (noGrant : ∀ stored, CredentialAuthorityState.readCapability context.authority.snapshot.cell kind capability = some stored →
      ¬ stored.head.Admissible context.authority.snapshot.authState wanted) :
    authorize prepared signature = none := by
  cases accepted : authorize prepared signature with
  | none => rfl
  | some authorization =>
      obtain ⟨stored, read, named⟩ := authorize_names_stored prepared signature accepted
      obtain ⟨cap, commitment, value, admissible, _⟩ :=
        controller_room_confidentiality prepared authorization
      rw [named] at value
      cases value
      exact (noGrant stored read admissible).elim

/-- **The outsider pole.** An observation of a cell by someone whose named
stored capability reaches neither the cell's parent chain nor the cell itself
is refused, with a valid signature and no matter which capability identifier
they name. -/
theorem controller_outsider_refused
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (offRoom : ∀ stored, CredentialAuthorityState.readCapability context.authority.snapshot.cell kind capability = some stored →
      (∀ room, stored.head.scope.targets = .under room →
        ¬ context.authority.snapshot.authState.parent.Descends wanted.target.value room) ∧
      ∀ ts, stored.head.scope.targets = .explicit ts → wanted.target ∉ ts) :
    authorize prepared signature = none :=
  controller_refuses_inadmissible prepared signature fun stored read =>
    RoomAuthorization.room_confidentiality stored.head (offRoom stored read).1 (offRoom stored read).2

/-- A signature with no stored capability behind it authorizes nothing. -/
theorem controller_signature_alone_refused
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (none_stored : CredentialAuthorityState.readCapability context.authority.snapshot.cell kind capability = none) :
    authorize prepared signature = none :=
  controller_refuses_inadmissible prepared signature fun stored read => by
    rw [none_stored] at read
    cases read

end Minidregg.Kernel.ResourceObservationAdmission

/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.signature_mode_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.signature_mode_refuted
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.controller_room_confidentiality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.controller_room_confidentiality
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.authorize_names_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.authorize_names_stored
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.controller_refuses_inadmissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.controller_refuses_inadmissible
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.controller_outsider_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.controller_outsider_refused
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.controller_signature_alone_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.controller_signature_alone_refused
