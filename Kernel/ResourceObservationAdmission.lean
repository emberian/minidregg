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
                  | some values => .ok ⟨observed, observeExact, domainExact, semanticsExact,
                      policyExact, epochExact, revisionExact, values, balancesExact⟩
                else .error (.of .staleRoot)
              else .error (.of .staleRoot)
            else .error (.of .malformed)
          else .error (.of .malformed)
        else .error (.of .malformed)
      else .error (.of .malformed)

variable {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
  {wanted : Request kind} {marker : Nat} {capability : CapabilityId} {contextBytes : List UInt8}

/-- The law's view of one cell for a request that writes nothing to it: the
request's slots, the context bytes, the cell's bytes, the account view and the
cell's resource slots. Observation admission and the room birth gate
(`Kernel.RoomBirthGate`) read a cell's law through this one projection. -/
def projectWith {kind : ResourceKind} (wanted : Request kind) (contextBytes : List UInt8)
    (physical : CanonicalCellRegistry.Kind) (accountBalances : List (Nat × Int))
    (logical : Store (CanonicalCellRegistry.layout physical)) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 contextBytes ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer physical).codec.encode logical) ++
    ResourceAuthorityProjection.bytesSlots "account/bytes" 0
      (CanonicalAccountView.balanceStream.encode accountBalances) ++
    accountBalances.map (fun pair => (s!"account/balance/{pair.1}", pair.2)) ++
    resourceSlots wanted.target.value physical logical⟩

def project (prepared : Prepared context profile wanted marker capability contextBytes)
    (logical : Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) : Minidregg.Pred.State :=
  projectWith wanted contextBytes prepared.observed.before.kind prepared.accountBalances logical

def step (prepared : Prepared context profile wanted marker capability contextBytes) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (readCandidate wanted prepared.observed.before.kind prepared.observed.before.payload prepared.observed.rootExact)

def policyConfig (prepared : Prepared context profile wanted marker capability contextBytes) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile context.authority.snapshot (sourceStore context)
    (sourceCapabilityPortal context.authority.snapshot marker) (step prepared)

def portal (prepared : Prepared context profile wanted marker capability contextBytes) : Portal :=
  (policyConfig prepared).portal

/-- The fields the reader's capability names (K-FIELDS), which narrow what a law refusal
tells it (`Refusal.lawDeniedFor`, FIX-DISCLOSE). A capability that does not read names no
field (`some ∅`): its refusal then names no clause over the cell's state. -/
def readerFields (context : Context deployment durable) (kind : ResourceKind)
    (capability : CapabilityId) : Option (Finset CellField) :=
  match CredentialAuthorityState.readCapability context.authority.snapshot.cell kind capability with
  | some stored => stored.head.scope.fields
  | none => some ∅

/-- Read admission after the requester's signature has verified. Capability
failures carry the reason of the component that decided them
(`sourceCapabilityOnlyEvidenceChecked`); a missing or failing committed law is
`lawDenied`, and a failing law names its failing clause on the very witness states the
law was admitted against, narrowed to the reader's own fields (`Refusal.lawDeniedFor`):
a clause over a field outside the grant is not named, and no such value is shown. -/
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
          | none => .error (Refusal.lawDeniedFor (readerFields context kind capability)
              committed.record.predicate witness.oldState witness.newState)
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
    authorizeChecked prepared signature = .error (Refusal.lawDeniedFor
      (readerFields context kind capability)
      committed.record.predicate (step prepared).oldState (step prepared).newState) := by
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
  · simp only [Except.error.injEq] at refused
    obtain ⟨at_, _, fails⟩ := lawDeniedFor_fails _ _ _ _ leaf refused
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

/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.authorizeChecked_lawDenied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorizeChecked_lawDenied
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.authorizeChecked_leaf_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorizeChecked_leaf_fails
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
  unfold authorize authorizeChecked at accepted
  dsimp only at accepted
  cases supplied : sourceCapabilityOnlyEvidenceChecked profile.compilerProfile context.authority.snapshot
      (sourceStore context) marker (step prepared) wanted capability signature with
  | error reason =>
    simp [supplied, Except.toOption] at accepted
  | ok evidence =>
  cases resolved : (policyConfig prepared).registry.resolve wanted.policyId wanted.policyRevision with
  | none =>
    simp [supplied, resolved, Except.toOption] at accepted
  | some committed =>
  simp only [supplied, resolved] at accepted
  split at accepted
  · simp [Except.toOption] at accepted
  · rename_i authorized admitted
    simp only [Except.toOption] at accepted
    injection accepted with same
    subst same
    have someEvidence : sourceCapabilityOnlyEvidence profile.compilerProfile context.authority.snapshot
        (sourceStore context) marker (step prepared) wanted capability signature = some evidence := by
      rw [← sourceCapabilityOnlyEvidenceChecked_toOption, supplied]
      rfl
    obtain ⟨stored, read, named⟩ := sourceCapabilityOnlyEvidence_names_parent
      profile.compilerProfile context.authority.snapshot (sourceStore context) marker (step prepared)
      wanted capability signature someEvidence
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

/-! ## Fields of a cell (K-FIELDS): what a write changed, what a read returns

A declared cell's field is its typed state key's coordinate: `slot n` for
object field `n`, `balance a` for an account's asset `a`, `code` for a program.
A content cell has two fields: `annotations` (the links, marks and annotations
namespaces) and `body` (every other namespace).  Kinds a resource scope never
reads or writes (authority, Book, event history, policy source) have no fields. -/

def declaredField : EffectDeclaration.StateKey → CellField
  | .objectField _ field => .slot field.value
  | .accountBalance _ asset => .balance asset.value
  | .programCode _ => .code

def contentField : Hyperdocument.Namespace → CellField
  | .links | .marks | .annotations => .annotations
  | _ => .body

/-- The field of one address of a registry cell, when the kind has fields. -/
def fieldOf : (kind : CanonicalCellRegistry.Kind) →
    Address (CanonicalCellRegistry.layout kind) → Option CellField
  | .content, address => some (contentField address.1)
  | .declaredObject, address | .accountMetadata, address | .declaredProgram, address =>
      some (declaredField address.2)
  -- A stream's entries are its body: a scope naming fields reads and appends a
  -- stream only when it names `body`.
  | .stream, _ => some .body
  -- Exhaustive on purpose: a new registry kind must say whether it has fields.
  | .eventHistory, _ | .authority, _ | .resourceBook, _ | .policySource, _ | .pay, _
  | .nockProgram, _ | .clock, _ => none
  -- An entry cell is read through its stream's `tail`, never observed itself.
  | .streamEntry, _ => none

/-- A read under `fields` keeps an address exactly when its field is named;
an address with no field is kept only by a scope naming every field. -/
def Kept {L : Layout.{0, 0, 0}} (fields : Option (Finset CellField))
    (field : Address L → Option CellField) (address : Address L) : Prop :=
  match field address with
  | some named => CellField.NamedBy fields named
  | none => fields = none

instance keptDecidable {L : Layout.{0, 0, 0}} (fields : Option (Finset CellField))
    (field : Address L → Option CellField) (address : Address L) :
    Decidable (Kept fields field address) := by
  unfold Kept; split <;> infer_instance

/-- The store a reader under `fields` receives: every other address absent. -/
def narrowStore {L : Layout.{0, 0, 0}} (fields : Option (Finset CellField))
    (field : Address L → Option CellField) (store : Store L) : Store L :=
  DFinsupp.filter (Kept fields field) store

/-- **Observation returns only named fields.**  Every present address of the
narrowed store is one the scope keeps. -/
theorem observe_returns_only_named_fields {L : Layout.{0, 0, 0}}
    {fields : Option (Finset CellField)} {field : Address L → Option CellField}
    {store : Store L} {address : Address L}
    (present : narrowStore fields field store address ≠ none) :
    Kept fields field address := by
  by_contra dropped
  exact present (DFinsupp.filter_apply_neg store dropped)

/-- And every kept address is returned unchanged. -/
theorem observe_returns_named_fields {L : Layout.{0, 0, 0}}
    {fields : Option (Finset CellField)} {field : Address L → Option CellField}
    (store : Store L) {address : Address L} (kept : Kept fields field address) :
    narrowStore fields field store address = store address :=
  DFinsupp.filter_apply_pos store kept

/-- A scope naming every field reads the whole cell. -/
theorem narrowStore_all {L : Layout.{0, 0, 0}} (field : Address L → Option CellField)
    (store : Store L) : narrowStore none field store = store := by
  refine DFinsupp.ext fun address => observe_returns_named_fields store ?_
  unfold Kept; split <;> trivial

/-- Pole: a reviewer naming `annotations` keeps a content link and drops the
body's atoms (any keys). -/
theorem reviewer_reads_annotations_not_body
    (link : Hyperdocument.Key .links) (atom : Hyperdocument.Key .atoms)
    (store : Store (CanonicalCellRegistry.layout .content)) :
    narrowStore (some {.annotations}) (fieldOf .content) store ⟨.links, link⟩ =
        store ⟨.links, link⟩ ∧
      narrowStore (some {.annotations}) (fieldOf .content) store ⟨.atoms, atom⟩ = none :=
  ⟨observe_returns_named_fields store
      (show CellField.NamedBy (some {.annotations}) .annotations by decide),
    DFinsupp.filter_apply_neg store
      (show ¬ CellField.NamedBy (some {.annotations}) .body by decide)⟩

/-- Pole: a reader naming field 1 of a declared object keeps field 1 and not
field 2. -/
theorem reader_reads_field_one_not_two (object : ResourceId .object)
    (store : Store (CanonicalCellRegistry.layout .declaredObject)) :
    narrowStore (some {.slot 1}) (fieldOf .declaredObject) store
        ⟨(), .objectField object ⟨1⟩⟩ = store ⟨(), .objectField object ⟨1⟩⟩ ∧
      narrowStore (some {.slot 1}) (fieldOf .declaredObject) store
        ⟨(), .objectField object ⟨2⟩⟩ = none :=
  ⟨observe_returns_named_fields store
      (show CellField.NamedBy (some {.slot 1}) (.slot 1) by decide),
    DFinsupp.filter_apply_neg store
      (show ¬ CellField.NamedBy (some {.slot 1}) (.slot 2) by decide)⟩

/-- A packed resource cell as a reader under `fields` receives it. -/
def narrowPacked (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) : PackedCell CanonicalCellRegistry.registry :=
  ⟨packed.kind, materialize _ (narrowStore fields (fieldOf packed.kind) packed.payload.logical)⟩

/-- An account cut as a reader under `fields` receives it: the `balance`
coordinates the scope names. -/
def narrowBalances (fields : Option (Finset CellField)) (balances : List (Nat × Int)) :
    List (Nat × Int) :=
  balances.filter fun pair => decide (CellField.NamedBy fields (.balance pair.1))

theorem narrowBalances_only_named {fields : Option (Finset CellField)}
    {balances : List (Nat × Int)} {pair : Nat × Int}
    (member : pair ∈ narrowBalances fields balances) :
    CellField.NamedBy fields (.balance pair.1) := by
  simpa [narrowBalances] using (List.mem_filter.mp member).2

/-- The addresses among `candidates` one write changed. -/
def changedWithin {L : Layout.{0, 0, 0}} (candidates : Finset (Address L)) (pre post : Store L) :
    Finset (Address L) :=
  candidates.filter fun address => pre address ≠ post address

/-- Every address one write changed. -/
def changed {L : Layout.{0, 0, 0}} (pre post : Store L) : Finset (Address L) :=
  changedWithin (pre.support ∪ post.support) pre post

theorem mem_changed {L : Layout.{0, 0, 0}} {pre post : Store L} {address : Address L} :
    address ∈ changed pre post ↔ pre address ≠ post address := by
  constructor
  · intro member; exact (Finset.mem_filter.mp member).2
  · intro different
    refine Finset.mem_filter.mpr ⟨?_, different⟩
    by_cases before : pre address = none
    · exact Finset.mem_union_right _ (DFinsupp.mem_support_iff.mpr (by
        rw [before] at different; exact fun h => different h.symm))
    · exact Finset.mem_union_left _ (DFinsupp.mem_support_iff.mpr before)

/-- Any candidate set outside which nothing changed finds exactly the changed
addresses. The controller's candidates are the patch's write footprint
(`Patch.run_frame`), so it never scans the whole cell. -/
theorem changedWithin_eq_changed {L : Layout.{0, 0, 0}} {candidates : Finset (Address L)}
    {pre post : Store L} (frame : ∀ address, address ∉ candidates → pre address = post address) :
    changedWithin candidates pre post = changed pre post := by
  ext address
  rw [mem_changed]
  constructor
  · intro member; exact (Finset.mem_filter.mp member).2
  · intro different
    exact Finset.mem_filter.mpr ⟨by_contra fun outside => different (frame address outside),
      different⟩

/-- What a write changed, field by field, over a set of changed addresses: the
touched fields, and on each the summed change of its numeric values
(`amount`; absence counts as `0`). -/
def footprintOf {L : Layout.{0, 0, 0}} (changedSet : Finset (Address L))
    (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L) :
    Footprint :=
  let value := fun (store : Store L) (address : Address L) =>
    match store address with | some v => amount address v | none => 0
  { touched := changedSet.image field
    delta := fun named => ∑ address ∈ changedSet.filter (fun a => field a = named),
      (value post address - value pre address) }

/-- The footprint of a write: `footprintOf` at every changed address. -/
def footprint {L : Layout.{0, 0, 0}} (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L) :
    Footprint :=
  footprintOf (changed pre post) field amount pre post

/-- A field is touched exactly when some address of it changed. -/
theorem footprint_touched_exact {L : Layout.{0, 0, 0}} (field : Address L → CellField)
    (amount : (address : Address L) → L.Value address.1 → Int) (pre post : Store L)
    (named : CellField) :
    named ∈ (footprint field amount pre post).touched ↔
      ∃ address, pre address ≠ post address ∧ field address = named := by
  simp only [footprint, footprintOf, Finset.mem_image, mem_changed]

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
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.observe_returns_only_named_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.observe_returns_only_named_fields
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.observe_returns_named_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.observe_returns_named_fields
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.narrowStore_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.narrowStore_all
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.reviewer_reads_annotations_not_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.reviewer_reads_annotations_not_body
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.reader_reads_field_one_not_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.reader_reads_field_one_not_two
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.mem_changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.mem_changed
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.narrowBalances_only_named' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.narrowBalances_only_named
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.changedWithin_eq_changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.changedWithin_eq_changed
/-- info: 'Minidregg.Kernel.ResourceObservationAdmission.footprint_touched_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceObservationAdmission.footprint_touched_exact
