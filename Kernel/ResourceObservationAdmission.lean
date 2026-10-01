/- Resource-local observation admission shared by native reads and joint
transactions. Every policy sees only its own unchanged canonical payload, its
own sparse account cut, and the deployment's one clock (`clock/now`,
`clock/day`, `clock/slot`, first, exactly as a resource invocation sees them;
`read_law_sees_clock`). Selection, credentials, the clock and committed policy
source all come from one loaded image; no other foreign state enters this
admission step.

A read commits nothing, so the clock it was judged at is not pinned by a CAS:
it is the clock cell of the very snapshot the read is answered from, and the
read's challenge names it beside the world root and height
(`NativeObservationController.challenge_names_clock`). -/
import Compiler.CanonicalRuntimeProfile
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.ResourceTargetAdmission
import Compiler.CanonicalAccountView
import Compiler.ResourceAuthorityProjection
import Kernel.ContentResource
import Kernel.DeclaredResourceProjection
import Kernel.ClockCellDomain
import Theory.AssertAxioms

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
  /-- The deployment clock of the snapshot the read is answered from. -/
  clock : Kernel.ClockCellDomain.Loaded deployment durable.snapshot
  clockLoaded : Kernel.ClockCellDomain.load deployment durable.snapshot = some clock

/-- Each refusing branch names its reason. The request is host-built from the
same image, so a component mismatch means the caller asked for something other
than an observation of this image (`malformed`) or named generations that have
moved (`staleRoot`); an unobservable target is `noGrant`. -/
def prepare (context : Context deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (wanted : Request kind) (marker : Nat) (capability : CapabilityId) (contextBytes : List UInt8) :
    Except Refusal (Prepared context profile wanted marker capability contextBytes) :=
  match ResourceTargetAdmission.observe deployment context.directory.directory kind
      wanted.target.value wanted.preStateRoot with
  | none => .error (.of .noGrant)
  | some observed =>
      if observeExact : wanted.verb = observeVerb kind then
        if domainExact : wanted.domain = deployment.domain then
          if semanticsExact : wanted.semantics = profile.semantics then
            if policyExact : wanted.policyId.value = wanted.target.value then
              if epochExact : wanted.policyEpoch = context.authority.snapshot.authState.policyEpoch wanted.policyId then
                if revisionExact : wanted.policyRevision = context.authority.snapshot.authState.policyRevision wanted.policyId then
                  match balancesExact : balances context kind wanted.target.value with
                  | none => .error (.of .noGrant)
                  | some values =>
                    match clockLoaded : Kernel.ClockCellDomain.load deployment durable.snapshot with
                    | none => .error (.of .operationRejected)
                    | some clock => .ok ⟨observed, observeExact, domainExact, semanticsExact,
                        policyExact, epochExact, revisionExact, values, balancesExact, clock,
                        clockLoaded⟩
                else .error (.of .staleRoot)
              else .error (.of .staleRoot)
            else .error (.of .malformed)
          else .error (.of .malformed)
        else .error (.of .malformed)
      else .error (.of .malformed)

variable {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
  {wanted : Request kind} {marker : Nat} {capability : CapabilityId} {contextBytes : List UInt8}

def project (prepared : Prepared context profile wanted marker capability contextBytes)
    (logical : Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) : Minidregg.Pred.State :=
  ⟨Kernel.ClockCell.slots prepared.clock.clock ++
    CanonicalRuntimeProfile.requestSlots wanted ++
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

/-- Read admission after the requester's signature has verified. Capability
failures carry the reason of the component that decided them
(`sourceCapabilityOnlyEvidenceChecked`); a missing or failing committed law is
`lawDenied`, and a failing law names its failing clause (`LawLeaf.of`) on the
very witness states the law was admitted against. -/
def authorizeChecked (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Except Refusal (Authorized (portal prepared) context.authority.snapshot.authState wanted) :=
  let config := policyConfig prepared
  match sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature with
  | .error reason => .error (.of reason)
  | .ok evidence =>
      match config.registry.resolve wanted.policyId wanted.policyRevision with
      | none => .error (Refusal.lawDenied none)
      | some committed =>
          let witness := canonicalWitness profile.compilerProfile.compiler committed
            (step prepared).oldState (step prepared).newState
          match CanonicalPolicyAdmission.admit config context.authority.snapshot.authState wanted
              evidence witness (.policy wanted.policyId wanted.policyRevision)
              prepared.epochExact prepared.revisionExact with
          | none => .error (Refusal.lawDenied
              (LawLeaf.of committed.record.predicate witness.oldState witness.newState))
          | some authorized => .ok authorized

def authorize (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState wanted) :=
  (authorizeChecked prepared signature).toOption

/-- The signed requester is told the reason of the capability branch that
decided its refusal, unchanged. -/
theorem authorizeChecked_capability_reason
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (reason : RefusalReason)
    (refused : sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature = .error reason) :
    authorizeChecked prepared signature = .error (.of reason) := by
  simp only [authorizeChecked, refused]

/-- With admissible capability evidence and a resolved committed law, a law
that does not accept is reported as `lawDenied`, naming the failing clause of
that law on the same witness states the admission was decided on. -/
theorem authorizeChecked_lawDenied
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (evidence : Evidence (portal prepared) context.authority.snapshot.authState wanted)
    (committed : CommittedPolicy)
    (supplied : sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature = .ok evidence)
    (resolved : (policyConfig prepared).registry.resolve wanted.policyId wanted.policyRevision =
      some committed)
    (denied : CanonicalPolicyAdmission.admit (policyConfig prepared) context.authority.snapshot.authState
      wanted evidence
      (canonicalWitness profile.compilerProfile.compiler committed
        (step prepared).oldState (step prepared).newState)
      (.policy wanted.policyId wanted.policyRevision)
      prepared.epochExact prepared.revisionExact = none) :
    authorizeChecked prepared signature = .error (Refusal.lawDenied
      (LawLeaf.of committed.record.predicate (step prepared).oldState (step prepared).newState)) := by
  simp only [authorizeChecked, supplied, resolved, denied]
  rfl

/-- The clause a read refusal names is false on the step the law was
evaluated on. -/
theorem authorizeChecked_leaf_fails
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (evidence : Evidence (portal prepared) context.authority.snapshot.authState wanted)
    (committed : CommittedPolicy) (leaf : LawLeaf)
    (supplied : sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature = .ok evidence)
    (resolved : (policyConfig prepared).registry.resolve wanted.policyId wanted.policyRevision =
      some committed)
    (refused : authorizeChecked prepared signature = .error (Refusal.lawDenied (some leaf))) :
    committed.record.predicate.subterm leaf.path = some leaf.clause ∧
      Minidregg.Pred.eval leaf.clause (step prepared).oldState (step prepared).newState = false := by
  simp only [authorizeChecked, supplied, resolved] at refused
  split at refused
  · simp only [Except.error.injEq, Refusal.lawDenied, Refusal.mk.injEq, true_and] at refused
    obtain ⟨at_, _, fails⟩ := LawLeaf.of_fails _ _ _ leaf refused
    exact ⟨at_, fails⟩
  · cases refused

/-- The admitted pole: the law's acceptance is returned unchanged. -/
theorem authorizeChecked_admitted
    (prepared : Prepared context profile wanted marker capability contextBytes)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot)
    (evidence : Evidence (portal prepared) context.authority.snapshot.authState wanted)
    (committed : CommittedPolicy)
    (authorized : Authorized (portal prepared) context.authority.snapshot.authState wanted)
    (supplied : sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature = .ok evidence)
    (resolved : (policyConfig prepared).registry.resolve wanted.policyId wanted.policyRevision =
      some committed)
    (accepted : CanonicalPolicyAdmission.admit (policyConfig prepared) context.authority.snapshot.authState
      wanted evidence
      (canonicalWitness profile.compilerProfile.compiler committed
        (step prepared).oldState (step prepared).newState)
      (.policy wanted.policyId wanted.policyRevision)
      prepared.epochExact prepared.revisionExact = some authorized) :
    authorizeChecked prepared signature = .ok authorized := by
  simp only [authorizeChecked, supplied, resolved, accepted]

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile wanted marker capability contextBytes)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState wanted
  authorized : authorize prepared signature = some authorization

/-- Signature first: until it verifies, the requester is not authenticated
and only `badSignature` (a fact about its own envelope) is named. -/
def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile wanted marker capability contextBytes) (envelope : List UInt8) :
    IO (Except Refusal (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot marker wanted envelope with
  | .error reason => return .error (.of (RefusalReason.ofSignature reason))
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match decided : authorizeChecked prepared signature with
        | .error refusal => return .error refusal
        | .ok authorization =>
            return .ok ⟨signature, exact, authorization, by simp [authorize, decided, Except.toOption]⟩
      else return .error (.of .badSignature)

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

/-! ## The clock a read's law sees -/

/-- **`read_law_sees_clock`**: the clock slots a read's law is evaluated on —
old and new alike — are exactly the clock cell's of the snapshot the read is
answered from (`clock/now`, `clock/day`, `clock/slot`), and that cell decodes
to that clock.  The read-path twin of `DeclaredResourceController.now_slot_exact`. -/
theorem read_law_sees_clock (prepared : Prepared context profile wanted marker capability contextBytes)
    (logical : Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    (project prepared logical).get "clock/now" = some (Int.ofNat prepared.clock.clock.now) ∧
      (project prepared logical).get "clock/day" =
        some (Int.ofNat (prepared.clock.clock.now / Kernel.ClockCell.secondsPerDay)) ∧
      (project prepared logical).get "clock/slot" = some (Int.ofNat prepared.clock.clock.slot) ∧
      Kernel.ClockCell.clockOf prepared.clock.cell.logical = some prepared.clock.clock ∧
      Kernel.ClockCellDomain.load deployment durable.snapshot = some prepared.clock := by
  refine ⟨?_, ?_, ?_, prepared.clock.clockExact, ?_⟩
  · simp [project, Kernel.ClockCell.slots, Minidregg.Pred.State.get]
  · simp [project, Kernel.ClockCell.slots, Minidregg.Pred.State.get]
  · simp [project, Kernel.ClockCell.slots, Minidregg.Pred.State.get]
  · exact prepared.clockLoaded

/-- **`read_now_slot_exact`** (K-CLOCK's `now_slot_exact` on the read path):
the law's old and new states both carry `clock/now` = the loaded clock's. -/
theorem read_now_slot_exact (prepared : Prepared context profile wanted marker capability contextBytes) :
    (step prepared).oldState.get "clock/now" = some (Int.ofNat prepared.clock.clock.now) ∧
      (step prepared).newState.get "clock/now" = some (Int.ofNat prepared.clock.clock.now) ∧
      Kernel.ClockCell.clockOf prepared.clock.cell.logical = some prepared.clock.clock := by
  have views := policy_views_equal prepared
  have old : (step prepared).oldState.get "clock/now" = some (Int.ofNat prepared.clock.clock.now) :=
    (read_law_sees_clock prepared prepared.observed.before.payload.logical).1
  exact ⟨old, views ▸ old, prepared.clock.clockExact⟩

/-! The two poles of a positive clock law on reads, "no reads before the
time in field 1": `resource/field/1/after <= clock/now + 0`, a positive
slot-to-slot atom (no fail-open `not`). -/

def opensAt : Minidregg.Pred.Pred :=
  .leSlotsOff "resource/field/1/after" "clock/now" 0

/-- The read state of the poles: the clock slots first (as `project` puts
them), then the law's constant. -/
def poleState (clock : Kernel.ClockCell.Clock) (t : Nat) : Minidregg.Pred.State :=
  ⟨Kernel.ClockCell.slots clock ++ [("resource/field/1/after", Int.ofNat t)]⟩

/-- **Refuting pole**: at the genesis clock (now 0) a law opening reads at
100 refuses the read. -/
theorem read_before_tick_refused :
    Minidregg.Pred.eval opensAt (poleState ⟨0, 0⟩ 100) (poleState ⟨0, 0⟩ 100) = false := by
  decide +kernel

/-- **Admitting pole**: after a tick to 100 the same law admits the read. -/
theorem read_after_tick_admitted :
    Minidregg.Pred.eval opensAt (poleState ⟨100, 0⟩ 100) (poleState ⟨100, 0⟩ 100) = true := by
  decide +kernel

#assert_axioms read_law_sees_clock
#assert_axioms read_now_slot_exact
#assert_axioms read_before_tick_refused
#assert_axioms read_after_tick_admitted

/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.authorizeChecked_lawDenied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorizeChecked_lawDenied
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.authorizeChecked_leaf_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorizeChecked_leaf_fails

end Minidregg.Kernel.ResourceObservationAdmission
