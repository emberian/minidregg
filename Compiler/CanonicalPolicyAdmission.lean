/-
# Compiler.CanonicalPolicyAdmission -- committed `Pred` is the policy gate

The former address-free policy verifier permitted a caller to install a
Boolean function without first selecting committed policy content.
This module supplies the canonical constructor: the policy verifier is derived
only from a versioned, content-addressed `Pred` record and acceptance of
`PredCompile.lower`.  The other verifier portals remain explicit inputs.

The construction is honest about its boundary.  The request commits a policy
identifier and source revision, while a deployment registry resolves that pair to an
addressed record.  Exact digest equalities bind the record and the `(old,new)`
policy step.  Collision resistance, registry authenticity, signature
soundness, and the concrete field/cast label remain deployment obligations;
none is synthesized as a proposition by this adapter.

The core authorization judgment now supplies the exact address selected from
authenticated authorization state, verifies its membership under the policy
root, and requires the witness to name that address.  This module owns the
canonical `PredCompile` implementation of that committed verifier.
-/
import Compiler.PredCompile
import Compiler.Tower256ConcreteBackend
import Compiler.Sp800185Cshake256
import Theory.PolicyInstall
import Theory.TypedAuthorization
import Kernel.MultiCellHyperedge

namespace Minidregg.Compiler.CanonicalPolicyAdmission

open Minidregg.Compiler
open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization

/-! ## 1. Versioned, content-addressed policy source. -/

/-- The complete first-order policy source selected by a request.  `previous`
is the version-chain link; `domain` and `semantics` prevent a policy record from
being replayed into a different semantic universe. -/
structure PolicyRecord where
  policyId : PolicyId
  version : PolicyRevision
  domain : Digest
  semantics : Digest
  previous : Option Digest
  predicate : Pred
  deriving DecidableEq, Repr

def PolicyRecord.source (record : PolicyRecord) :
    Minidregg.Theory.PolicyInstall.Source Pred where
  policyId := record.policyId
  version := record.version
  domain := record.domain
  semantics := record.semantics
  previous := record.previous
  body := record.predicate

/-- A registry entry names the exact content address beside its source record.
The verifier independently recomputes `recordDigest record` and checks it
against `address`; the registry does not get to assert that equality. -/
structure CommittedPolicy where
  address : Digest
  record : PolicyRecord
  deriving DecidableEq, Repr

/-- The deployment-owned resolution of `(PolicyId, source revision)`.  Authenticating
this finite/durable registry and its root is deliberately outside this module. -/
structure PolicyRegistry where
  resolve : PolicyId → PolicyRevision → Option CommittedPolicy

/-- The only policy witness type installed by the canonical portal.  It carries
the exact policy step and the AIR auxiliary assignment.  There is no predicate
or verifier function in the witness. -/
structure CompiledPolicyWitness (F : Type) where
  address : Digest
  oldState : State
  newState : State
  auxiliary : List ℕ → ℕ → F

/-- A step context can be constructed only from a source-derived candidate.
Its roots, effect identity and projected states are read-only projections of
that construction, never independently decoded request fields. -/
structure PolicyStepContext where
  private mk ::
  preStateRoot : Digest
  effectsDigest : Digest
  semantics : Digest
  oldState : State
  newState : State

/-- A receiving module fixes `project` and its semantic pin in source. The
concrete receiving API must not accept either from a host or a request. Mode
evidence and patch validation precede policy authorization, avoiding a cycle. -/
def PolicyStepContext.ofCandidate
    {S : Minidregg.Theory.CellState.Schema}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : Minidregg.Theory.CellState.Materializer S Digest}
    {Nullifier : Type}
    {family : Minidregg.Theory.SemanticEffectFamily S M Nullifier}
    {pre : Minidregg.Theory.CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (project : Minidregg.Theory.CellState.LogicalState S → State)
    (semantics : Digest)
    (candidate : Minidregg.Theory.PolicyInstall.Candidate family pre declaration outcome) :
    PolicyStepContext :=
  ⟨pre.root, family.effectDigest declaration, semantics,
    project pre.logical, project candidate.post.logical⟩

universe u v w x y z

/-- Joint policy inputs come from the same source-owned preparation plan that
later produces the existing heterogeneous turn. The primary incidence chooses
the actual request pre-root; every new-state component is the corresponding
validated final patch result. Neither roots nor predicate states are arguments.

The receiving source fixes `project` and the semantic profile. In particular,
an unchanged factory cell can inspect changed authority and resource cells
without a caller supplying independent old/new predicate views. -/
def PolicyStepContext.ofPreparedTuple
    {Incidence : Type z}
    {layout : Minidregg.Kernel.MultiCellHyperedge.CellLayout.{u, v, w, x, z} Incidence}
    {Source : Type z}
    {plan : Minidregg.Kernel.MultiCellHyperedge.PreparationPlan.{u, v, w, x, y, z}
      layout Source}
    (project : Source →
      ((incidence : Incidence) → Minidregg.Theory.CellState.LogicalState (layout.schema incidence)) →
      State)
    (semantics : Digest)
    (prepared : Minidregg.Kernel.MultiCellHyperedge.PreparedTuple plan) : PolicyStepContext :=
  ⟨(prepared.pre prepared.primary).root, plan.legEffectsDigest prepared.source prepared.primary, semantics,
    project prepared.source prepared.logicalPre,
    project prepared.source prepared.logicalPost⟩

theorem PolicyStepContext.prepared_tuple_exact
    {Incidence : Type z}
    {layout : Minidregg.Kernel.MultiCellHyperedge.CellLayout.{u, v, w, x, z} Incidence}
    {Source : Type z}
    {plan : Minidregg.Kernel.MultiCellHyperedge.PreparationPlan.{u, v, w, x, y, z}
      layout Source}
    (project : Source →
      ((incidence : Incidence) → Minidregg.Theory.CellState.LogicalState (layout.schema incidence)) →
      State)
    (semantics : Digest)
    (prepared : Minidregg.Kernel.MultiCellHyperedge.PreparedTuple plan) :
    (ofPreparedTuple project semantics prepared).preStateRoot =
        (prepared.pre prepared.primary).root ∧
      (ofPreparedTuple project semantics prepared).effectsDigest = plan.legEffectsDigest prepared.source prepared.primary ∧
      (ofPreparedTuple project semantics prepared).oldState = project prepared.source prepared.logicalPre ∧
      (ofPreparedTuple project semantics prepared).newState = project prepared.source prepared.logicalPost :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The abstract digest model survives only as an explicitly chosen research
adapter. Production constructors select `canonical`; no decoded request can
choose the adapter or its state projection. -/
inductive PolicyStepBinding where
  | model (stateDigest : State → Digest) (stepDigest : State → State → Digest)
  | canonical (context : PolicyStepContext)

def PolicyStepBinding.matches {kind : ResourceKind} (binding : PolicyStepBinding)
    (request : Request kind) (oldState newState : State) : Bool :=
  match binding with
  | .model stateDigest stepDigest =>
      decide (stateDigest oldState = request.preStateRoot) &&
      decide (stepDigest oldState newState = request.effectsDigest)
  | .canonical context =>
      decide (request.preStateRoot = context.preStateRoot) &&
      decide (request.effectsDigest = context.effectsDigest) &&
      decide (request.semantics = context.semantics) &&
      decide (oldState = context.oldState) && decide (newState = context.newState)

theorem canonical_step_matches_iff {kind : ResourceKind}
    (context : PolicyStepContext) (request : Request kind) (oldState newState : State) :
    (PolicyStepBinding.canonical context).matches request oldState newState = true ↔
      request.preStateRoot = context.preStateRoot ∧
      request.effectsDigest = context.effectsDigest ∧
      request.semantics = context.semantics ∧
      oldState = context.oldState ∧ newState = context.newState := by
  simp [PolicyStepBinding.matches, and_assoc]

/-- Identical predicate views do not erase a distinct declaration commitment.
This is precisely what a digest function of only `(old,new)` cannot express. -/
theorem equal_views_do_not_erase_effect_identity {kind : ResourceKind}
    (left right : PolicyStepContext) (request : Request kind)
    (oldEqual : left.oldState = right.oldState)
    (newEqual : left.newState = right.newState)
    (different : left.effectsDigest ≠ right.effectsDigest) :
    (PolicyStepBinding.canonical right).matches
      { request with effectsDigest := left.effectsDigest }
      left.oldState left.newState = false := by
  rw [oldEqual, newEqual]
  simp [PolicyStepBinding.matches, different]

/-! ## Source-owned compiler semantics -/

/-- Every arithmetic parameter is committed in the canonical source profile bytes.
The receiver label names the complete compatible runtime across its operation families.
The backend/field identity is selected by receiving source. Its characteristic is
additionally tied to the actual Lean field by `CharP`, never inferred from a name. -/
structure CompilerSemanticDescriptor where
  receiverSemantics : Digest
  compilerVersion : Nat
  fieldIdentity : Digest
  characteristic : Nat
  orderWidth : Option Nat
  deriving DecidableEq, Repr

def compilerSemanticVersion : Nat := 1

open Minidregg.Compiler.Tower256ConcreteBackend in
def compilerDescriptorStream :
    StreamCodec (Digest × (Nat × (Digest × (Nat × Option Nat)))) :=
  StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.option StreamCodec.nat))))

def CompilerSemanticDescriptor.tuple (descriptor : CompilerSemanticDescriptor) :
    Digest × (Nat × (Digest × (Nat × Option Nat))) :=
  (descriptor.receiverSemantics, descriptor.compilerVersion, descriptor.fieldIdentity,
    descriptor.characteristic, descriptor.orderWidth)

def CompilerSemanticDescriptor.encode (descriptor : CompilerSemanticDescriptor) : List UInt8 :=
  compilerDescriptorStream.encode descriptor.tuple

/-- Canonical profile bytes preserve every descriptor component before hashing. -/
theorem CompilerSemanticDescriptor.encode_injective :
    Function.Injective CompilerSemanticDescriptor.encode := by
  intro left right same
  have decoded := congrArg compilerDescriptorStream.toLawful.decode same
  have leftDecoded := compilerDescriptorStream.toLawful.decode_encode left.tuple
  have rightDecoded := compilerDescriptorStream.toLawful.decode_encode right.tuple
  change compilerDescriptorStream.toLawful.decode
    (compilerDescriptorStream.encode left.tuple) = some left.tuple at leftDecoded
  change compilerDescriptorStream.toLawful.decode
    (compilerDescriptorStream.encode right.tuple) = some right.tuple at rightDecoded
  change compilerDescriptorStream.toLawful.decode
    (compilerDescriptorStream.encode left.tuple) =
      compilerDescriptorStream.toLawful.decode
        (compilerDescriptorStream.encode right.tuple) at decoded
  rw [leftDecoded, rightDecoded] at decoded
  cases left
  cases right
  simp_all [CompilerSemanticDescriptor.tuple]

/-- Domain-separated cSHAKE binds compatible receiving-runtime semantics, version, field and arithmetic
profile. Hash collision resistance is not asserted as an injectivity theorem. -/
def CompilerSemanticDescriptor.digest (descriptor : CompilerSemanticDescriptor) : Digest :=
  (Sp800185Cshake256.hash "DREGG.POLICY.COMPILER.PROFILE/v1".toUTF8.toList
    descriptor.encode).digest

/-- Only receiving source constructs these values. A source profile derives its
semantic identity from canonical descriptor bytes and carries its actual field
and no-wrap premises. The research constructor exists for explicit model fixtures;
canonical state bindings reject it, including when their predicates contain no order. -/
inductive PolicyCompilerProfile (F : Type) [Field F] where
  | source (receiverSemantics fieldIdentity : Digest) (characteristic : Nat)
      (characteristicCorrect : CharP F characteristic) (compiler : CompilerProfile)
      (admissible : compiler.Admissible F)
  | researchDisabled (semantics : Digest)

def PolicyCompilerProfile.compiler {F : Type} [Field F] :
    PolicyCompilerProfile F → CompilerProfile
  | .source _ _ _ _ compiler _ => compiler
  | .researchDisabled _ => CompilerProfile.disabled

theorem PolicyCompilerProfile.admissible {F : Type} [Field F] :
    (profile : PolicyCompilerProfile F) → profile.compiler.Admissible F
  | .source _ _ _ _ _ admissible => admissible
  | .researchDisabled _ => True.intro

def sourceCompilerDescriptor (receiverSemantics fieldIdentity : Digest)
    (characteristic : Nat) (compiler : CompilerProfile) : CompilerSemanticDescriptor where
  receiverSemantics := receiverSemantics
  fieldIdentity := fieldIdentity
  characteristic := characteristic
  compilerVersion := compilerSemanticVersion
  orderWidth := match compiler.order with | .disabled => none | .scalar width => some width

def PolicyCompilerProfile.descriptor? {F : Type} [Field F] :
    PolicyCompilerProfile F → Option CompilerSemanticDescriptor
  | .source receiverSemantics fieldIdentity characteristic _ compiler _ =>
      some (sourceCompilerDescriptor receiverSemantics fieldIdentity characteristic compiler)
  | .researchDisabled _ => none

def PolicyCompilerProfile.semantics {F : Type} [Field F] :
    PolicyCompilerProfile F → Digest
  | .source receiverSemantics fieldIdentity characteristic _ compiler _ =>
      (sourceCompilerDescriptor receiverSemantics fieldIdentity characteristic compiler).digest
  | .researchDisabled semantics => semantics

def PolicyCompilerProfile.compatible {F : Type} [Field F]
    (profile : PolicyCompilerProfile F) : PolicyStepBinding → Bool
  | .model _ _ => true
  | .canonical _ => profile.descriptor?.isSome

/-- Canonical bindings never accept the explicit research profile. -/
theorem research_profile_canonical_refused {F : Type} [Field F]
    (semantics : Digest) (context : PolicyStepContext) :
    (PolicyCompilerProfile.researchDisabled (F := F) semantics).compatible (.canonical context) = false :=
  rfl

/-! ## 2. Canonical portal construction. -/

/-- All inputs to the canonical policy verifier.  The base portal's policy
verifier and old witness type are intentionally ignored by `portal`; only the non-policy
verifier families are retained. -/
structure CanonicalPolicyConfig (F : Type) [Field F] [DecidableEq F] where
  base : Portal
  registry : PolicyRegistry
  recordDigest : PolicyRecord → Digest
  stepBinding : PolicyStepBinding
  compilerProfile : PolicyCompilerProfile F

/-- The exact conjunction checked by the policy gate.  In particular, the
verdict is acceptance of `PredCompile.lower`, not a second hand-written mirror
of the predicate evaluator. -/
def CanonicalPolicyConfig.verifies {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) : Bool :=
  match config.registry.resolve request.policyId request.policyRevision with
  | none => false
  | some committed =>
      decide (committed.record.policyId = request.policyId) &&
      decide (committed.record.version = request.policyRevision) &&
      decide (committed.record.domain = request.domain) &&
      decide (committed.record.semantics = request.semantics) &&
      decide (config.recordDigest committed.record = committed.address) &&
      decide (witness.address = committed.address) &&
      config.stepBinding.matches request witness.oldState witness.newState &&
      config.compilerProfile.compatible config.stepBinding &&
      decide (request.semantics = config.compilerProfile.semantics) &&
      supported config.compilerProfile.compiler committed.record.predicate &&
      inputsInRange config.compilerProfile.compiler committed.record.predicate
        witness.oldState witness.newState &&
      decide (castInjOn F
        (intsOf committed.record.predicate witness.oldState witness.newState)) &&
      decide (systemAccepts
        (stepAsg witness.oldState witness.newState witness.auxiliary)
        (lower config.compilerProfile.compiler committed.record.predicate))

/-- Source selection is independent of capability generation. The common
`Authorized` gate still requires exact generation equality; this law does not
transfer evidence or signatures across a generation change. -/
theorem verifies_policy_generation_independent
    {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) (generation : Epoch) :
    config.verifies { request with policyEpoch := generation } witness =
      config.verifies request witness := by
  unfold CanonicalPolicyConfig.verifies
  cases config.registry.resolve request.policyId request.policyRevision with
  | none => rfl
  | some committed =>
      cases config.stepBinding <;> rfl

/-- Replace the arbitrary policy face of a portal by the committed compiler
gate.  The inherited policy witness and inherited policy verifier are erased. -/
def CanonicalPolicyConfig.portal {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) : Portal where
  SignatureWitness := config.base.SignatureWitness
  ProofWitness := config.base.ProofWitness
  CapabilityCommitmentWitness := config.base.CapabilityCommitmentWitness
  CapabilityUseWitness := config.base.CapabilityUseWitness
  MembershipWitness := config.base.MembershipWitness
  IssuerWitness := config.base.IssuerWitness
  NonRevocationWitness := config.base.NonRevocationWitness
  PolicyWitness := CompiledPolicyWitness F
  policyAddress := fun witness => witness.address
  verifySignature := config.base.verifySignature
  verifyProof := config.base.verifyProof
  verifyCapabilityCommitment := config.base.verifyCapabilityCommitment
  verifyCapabilityUse := config.base.verifyCapabilityUse
  verifyMembership := config.base.verifyMembership
  verifyIssuer := config.base.verifyIssuer
  verifyNonRevocation := config.base.verifyNonRevocation
  verifyCommittedPolicy := fun committedAddress _ request witness =>
    decide (committedAddress = witness.address) && config.verifies request witness

@[simp] theorem portal_verifyCommittedPolicy {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (committedAddress : Digest) (request : Request kind)
    (witness : CompiledPolicyWitness F) :
    config.portal.verifyCommittedPolicy committedAddress request witness =
      (decide (committedAddress = witness.address) &&
        config.verifies request witness) :=
  rfl

/-! ## 3. Exact executable reading and compiler reflection. -/

/-- Propositional spelling of every check made by `verifies`.  It is useful at
the trust boundary because no Boolean conjunct remains implicit. -/
def Verified {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) : Prop :=
  ∃ committed,
    config.registry.resolve request.policyId request.policyRevision = some committed ∧
    committed.record.policyId = request.policyId ∧
    committed.record.version = request.policyRevision ∧
    committed.record.domain = request.domain ∧
    committed.record.semantics = request.semantics ∧
    config.recordDigest committed.record = committed.address ∧
    witness.address = committed.address ∧
    config.stepBinding.matches request witness.oldState witness.newState = true ∧
    config.compilerProfile.compatible config.stepBinding = true ∧
    request.semantics = config.compilerProfile.semantics ∧
    supported config.compilerProfile.compiler committed.record.predicate = true ∧
    inputsInRange config.compilerProfile.compiler committed.record.predicate
      witness.oldState witness.newState = true ∧
    castInjOn F (intsOf committed.record.predicate witness.oldState witness.newState) ∧
    systemAccepts
      (stepAsg witness.oldState witness.newState witness.auxiliary)
      (lower config.compilerProfile.compiler committed.record.predicate)

/-- The executable verifier has exactly the explicit reading above. -/
theorem verifies_iff_verified {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) :
    config.verifies request witness = true ↔ Verified config request witness := by
  cases hresolve : config.registry.resolve request.policyId request.policyRevision with
  | none => simp [CanonicalPolicyConfig.verifies, Verified, hresolve]
  | some committed =>
      simp [CanonicalPolicyConfig.verifies, Verified, hresolve]
      all_goals tauto

/-- Soundness is inherited from the GENERAL `PredCompile.lower_sound`: every
accepting auxiliary assignment forces the selected source predicate to hold. -/
theorem verifies_sound {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {witness : CompiledPolicyWitness F}
    (accepted : config.verifies request witness = true) :
    ∃ committed,
      config.registry.resolve request.policyId request.policyRevision = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        witness.oldState witness.newState = true := by
  rcases (verifies_iff_verified config request witness).mp accepted with
    ⟨committed, resolved, _, _, _, _, _, _, _, _, _, supportedExact,
      rangesExact, castExact, compiled⟩
  exact ⟨committed, resolved, lower_sound config.compilerProfile.compiler config.compilerProfile.admissible
    castExact supportedExact rangesExact compiled⟩

/-- The receiving theorem speaks about the source-derived context, not free
predicate-state witnesses. Both the actual pre-root and full declaration
commitment survive the projection into predicate slots. -/
theorem canonical_context_verifies_sound {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {witness : CompiledPolicyWitness F}
    (context : PolicyStepContext)
    (canonical : config.stepBinding = .canonical context)
    (accepted : config.verifies request witness = true) :
    request.preStateRoot = context.preStateRoot ∧
    request.effectsDigest = context.effectsDigest ∧
    request.semantics = context.semantics ∧
    ∃ committed,
      config.registry.resolve request.policyId request.policyRevision = some committed ∧
      Minidregg.Pred.eval committed.record.predicate context.oldState context.newState = true := by
  rcases (verifies_iff_verified config request witness).mp accepted with
    ⟨committed, resolved, _, _, _, _, _, _, matched, _, _, supported, ranges, cast, compiled⟩
  rw [canonical] at matched
  rcases (canonical_step_matches_iff context request witness.oldState witness.newState).mp
      matched with ⟨rootExact, effectsExact, semanticsExact, oldExact, newExact⟩
  have evaluated := lower_sound config.compilerProfile.compiler config.compilerProfile.admissible
    cast supported ranges compiled
  rw [oldExact, newExact] at evaluated
  exact ⟨rootExact, effectsExact, semanticsExact, committed, resolved, evaluated⟩

/-- The accepted canonical request names a descriptor-derived semantic identity,
with the actual field characteristic, fixed compiler version and no-wrap law.
The field/backend tag is a source-owned identifier, not a proof of deployment. -/
theorem canonical_verifies_profile_bound {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {witness : CompiledPolicyWitness F}
    (context : PolicyStepContext)
    (canonical : config.stepBinding = .canonical context)
    (accepted : config.verifies request witness = true) :
    ∃ descriptor, config.compilerProfile.descriptor? = some descriptor ∧
      request.semantics = descriptor.digest ∧
      descriptor.compilerVersion = compilerSemanticVersion ∧
      CharP F descriptor.characteristic ∧
      (match descriptor.orderWidth with | none => True | some width => PredOrder.NoWrap F width) := by
  rcases (verifies_iff_verified config request witness).mp accepted with
    ⟨_, _, _, _, _, _, _, _, _, compatible, semanticsExact, _, _, _, _⟩
  rw [canonical] at compatible
  cases hp : config.compilerProfile with
  | researchDisabled semantics =>
      simp [hp, PolicyCompilerProfile.compatible, PolicyCompilerProfile.descriptor?] at compatible
  | source receiver field characteristic characteristicCorrect compiler admissible =>
      refine ⟨sourceCompilerDescriptor receiver field characteristic compiler, ?_, ?_, rfl,
        characteristicCorrect, ?_⟩
      · simp [PolicyCompilerProfile.descriptor?]
      · simpa only [hp, PolicyCompilerProfile.semantics] using semanticsExact
      · cases compiler with
        | mk order => cases order <;> exact admissible

/-- The canonical prover witness is derived from the same lowering fold. -/
def canonicalWitness {F : Type} [Field F] [DecidableEq F]
    (profile : CompilerProfile) (committed : CommittedPolicy) (oldState newState : State) :
    CompiledPolicyWitness F where
  address := committed.address
  oldState := oldState
  newState := newState
  auxiliary := wit profile committed.record.predicate oldState newState

/-- Exact reflection for a resolved, digest-bound deployment instance.  The
forward implication is adversarial soundness; the reverse implication uses the
witness generator emitted by the same compiler fold. -/
theorem canonical_verifies_iff_eval {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    {oldState newState : State}
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (versionExact : committed.record.version = request.policyRevision)
    (domainExact : committed.record.domain = request.domain)
    (semanticsExact : committed.record.semantics = request.semantics)
    (recordDigestExact : config.recordDigest committed.record = committed.address)
    (stepExact : config.stepBinding.matches request oldState newState = true)
    (profileCompatible : config.compilerProfile.compatible config.stepBinding = true)
    (profileSemanticsExact : request.semantics = config.compilerProfile.semantics)
    (supportedExact : supported config.compilerProfile.compiler committed.record.predicate = true)
    (rangesExact : inputsInRange config.compilerProfile.compiler committed.record.predicate
      oldState newState = true)
    (castExact : castInjOn F
      (intsOf committed.record.predicate oldState newState)) :
    config.verifies request (canonicalWitness config.compilerProfile.compiler committed oldState newState) = true ↔
      Minidregg.Pred.eval committed.record.predicate oldState newState = true := by
  constructor
  · intro accepted
    rcases verifies_sound accepted with ⟨selected, selectedExact, evaluated⟩
    rw [resolved] at selectedExact
    cases selectedExact
    exact evaluated
  · intro evaluated
    apply (verifies_iff_verified config request
      (canonicalWitness config.compilerProfile.compiler committed oldState newState)).mpr
    refine ⟨committed, resolved, policyIdExact, versionExact, domainExact,
      semanticsExact, recordDigestExact, rfl, stepExact,
      profileCompatible, profileSemanticsExact, supportedExact, rangesExact, castExact, ?_⟩
    exact lower_complete config.compilerProfile.compiler config.compilerProfile.admissible
      castExact supportedExact rangesExact evaluated

/-! ## 4. Admission adapter and negative teeth. -/

/-- The canonical authorization target.  Its policy verifier is definitionally
the compiled committed verifier above; no policy function is an argument. -/
abbrev CanonicalAuthorized {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type :=
  Authorized config.portal state request

/-- Executable admission: after evidence and the exact current generation and source revision are
present, the only remaining branch is the canonical compiled verifier. -/
def admit {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal state request)
    (witness : CompiledPolicyWitness F)
    (policyMembershipWitness : config.portal.MembershipWitness)
    (policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId)
    (policyRevisionExact : request.policyRevision = state.policyRevision request.policyId) :
    Option (CanonicalAuthorized config state request) :=
  if addressExact : witness.address =
      state.policyAddress request.policyId request.policyRevision then
    if membershipAccepted : config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyRevision)
        policyMembershipWitness = true then
      if accepted : config.verifies request witness = true then
        some
          { evidence := evidence
            policyWitness := witness
            policyMembershipWitness := policyMembershipWitness
            policyEpochExact := policyEpochExact
            policyRevisionExact := policyRevisionExact
            policyAddressExact := addressExact
            policyMembershipVerified := membershipAccepted
            policyVerified := by
              simp [CanonicalPolicyConfig.portal, addressExact, accepted] }
      else none
    else none
  else none

/-- The receiving constructor retains the exact evidence supplied by its caller.
In particular, parent-capability identity is not erased by the policy gate. -/
theorem admit_preserves_evidence {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal state request)
    (witness : CompiledPolicyWitness F)
    (policyMembershipWitness : config.portal.MembershipWitness)
    (policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId)
    (policyRevisionExact : request.policyRevision = state.policyRevision request.policyId)
    {authorized : CanonicalAuthorized config state request}
    (accepted : admit config state request evidence witness policyMembershipWitness
      policyEpochExact policyRevisionExact = some authorized) :
    authorized.evidence = evidence := by
  unfold admit at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  rfl

theorem admit_isSome_iff {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal state request)
    (witness : CompiledPolicyWitness F)
    (policyMembershipWitness : config.portal.MembershipWitness)
    (policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId)
    (policyRevisionExact : request.policyRevision = state.policyRevision request.policyId) :
    (admit config state request evidence witness policyMembershipWitness
      policyEpochExact policyRevisionExact).isSome = true ↔
      witness.address = state.policyAddress request.policyId request.policyRevision ∧
      config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyRevision)
        policyMembershipWitness = true ∧
      config.verifies request witness = true := by
  by_cases addressExact :
      witness.address = state.policyAddress request.policyId request.policyRevision
  · by_cases membershipAccepted : config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyRevision)
        policyMembershipWitness = true
    · by_cases accepted : config.verifies request witness = true <;>
        simp [admit, addressExact, membershipAccepted, accepted]
    · simp [admit, addressExact, membershipAccepted]
  · simp [admit, addressExact]

/-- A missing `(policyId,version)` record fails closed. -/
theorem unresolved_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} (witness : CompiledPolicyWitness F)
    (unresolved : config.registry.resolve request.policyId request.policyRevision = none) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, unresolved]

/-- A registry entry whose internal policy id does not equal the request is
rejected even if it was returned from the requested lookup key. -/
theorem wrong_policy_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (wrong : committed.record.policyId ≠ request.policyId) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- A registry entry cannot lie about the version under which it was found. -/
theorem wrong_version_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (wrong : committed.record.version ≠ request.policyRevision) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, policyIdExact, wrong]

/-- Content-address substitution fails before policy evaluation. -/
theorem wrong_address_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (wrong : witness.address ≠ committed.address) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- A registry address is not self-authenticating: recomputing a different
digest from the selected source record rejects the entry. -/
theorem wrong_content_digest_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (wrong : config.recordDigest committed.record ≠ committed.address) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- Mutating the policy step without updating its request commitment fails. -/
theorem wrong_step_binding_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (wrong : config.stepBinding.matches request witness.oldState witness.newState = false) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- A witness cannot select different compiler semantics by rebinding the record alone. -/
theorem wrong_compiler_semantics_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} (witness : CompiledPolicyWitness F)
    (wrong : request.semantics ≠ config.compilerProfile.semantics) :
    config.verifies request witness = false := by
  cases resolved : config.registry.resolve request.policyId request.policyRevision <;>
    simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- Source bounds are checked independently of the supplied AIR auxiliary values. -/
theorem out_of_range_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyRevision = some committed)
    (outside : inputsInRange config.compilerProfile.compiler committed.record.predicate
      witness.oldState witness.newState = false) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, outside]

/-- An explicit research profile cannot serve any canonical receiving context. -/
theorem research_profile_verifier_refused {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} (witness : CompiledPolicyWitness F)
    (context : PolicyStepContext) (semantics : Digest)
    (canonical : config.stepBinding = .canonical context)
    (research : config.compilerProfile = .researchDisabled semantics) :
    config.verifies request witness = false := by
  cases resolved : config.registry.resolve request.policyId request.policyRevision <;>
    simp [CanonicalPolicyConfig.verifies, resolved, canonical, research,
      PolicyCompilerProfile.compatible, PolicyCompilerProfile.descriptor?]

/-- Even if all digest equalities collide or are rebound, a source-level policy
failure cannot be hidden by a malicious auxiliary assignment. -/
theorem policy_false_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {witness : CompiledPolicyWitness F}
    (policyFalse : ∀ committed,
      config.registry.resolve request.policyId request.policyRevision = some committed →
      Minidregg.Pred.eval committed.record.predicate
        witness.oldState witness.newState = false) :
    config.verifies request witness = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  rcases verifies_sound accepted with ⟨committed, resolved, evaluated⟩
  rw [policyFalse committed resolved] at evaluated
  contradiction

/-! ## 5. Computed keystone.  Its digest functions are intentionally tiny and
collision-prone; they witness the interface, not cryptographic deployment. -/

def demoRecord : PolicyRecord where
  policyId := demoRequest.policyId
  version := demoRequest.policyRevision
  domain := demoRequest.domain
  semantics := demoRequest.semantics
  previous := none
  predicate := kPol

def demoRecordDigest (record : PolicyRecord) : Digest :=
  ⟨record.policyId.value + record.version + record.domain.value +
    record.semantics.value + 100⟩

def demoCommitted : CommittedPolicy where
  address := demoRecordDigest demoRecord
  record := demoRecord

def demoRegistry : PolicyRegistry where
  resolve := fun policyId version =>
    if policyId = demoRequest.policyId ∧ version = demoRequest.policyRevision then
      some demoCommitted
    else
      none

def demoStateDigest (state : State) : Digest :=
  if state = kOld then demoRequest.preStateRoot else ⟨9000⟩

def demoStepDigest (oldState newState : State) : Digest :=
  if oldState = kOld ∧ newState = kNew then demoRequest.effectsDigest else ⟨9001⟩

def demoConfig : CanonicalPolicyConfig (ZMod 13) where
  base := demoPortal
  registry := demoRegistry
  recordDigest := demoRecordDigest
  stepBinding := .model demoStateDigest demoStepDigest
  compilerProfile := .researchDisabled demoRequest.semantics

/-- Authorization state selects the exact content address resolved by the
demo registry.  The registry root is illustrative; membership is discharged
by `demoPortal` and carries no cryptographic claim. -/
def demoAuthState : AuthState :=
  { demoState with
    policyAddress := fun policyId version =>
      if policyId = demoRequest.policyId ∧ version = demoRequest.policyRevision then
        demoCommitted.address
      else ⟨0⟩ }

def demoWitness : CompiledPolicyWitness (ZMod 13) :=
  canonicalWitness demoConfig.compilerProfile.compiler demoCommitted kOld kNew

/-- Positive pole: the exact versioned policy, state commitment, effect
commitment, and emitted AIR witness are accepted. -/
theorem demo_policy_accepts : demoConfig.verifies demoRequest demoWitness = true := by
  decide

def demoWrongPolicyRequest : Request .object :=
  { demoRequest with policyId := ⟨999⟩ }

def demoWrongVersionRequest : Request .object :=
  { demoRequest with policyRevision := demoRequest.policyRevision + 1 }

def demoWrongAddressWitness : CompiledPolicyWitness (ZMod 13) :=
  { demoWitness with address := ⟨9999⟩ }

def demoMutatedWitness : CompiledPolicyWitness (ZMod 13) :=
  canonicalWitness demoConfig.compilerProfile.compiler demoCommitted kOld kBad

/-- Wrong policy id and version both fail closed at registry resolution. -/
theorem demo_wrong_policy_rejected :
    demoConfig.verifies demoWrongPolicyRequest demoWitness = false := by decide

theorem demo_wrong_version_rejected :
    demoConfig.verifies demoWrongVersionRequest demoWitness = false := by decide

/-- The correct record at a substituted content address is rejected. -/
theorem demo_wrong_address_rejected :
    demoConfig.verifies demoRequest demoWrongAddressWitness = false := by decide

/-- A hostile post-state is rejected.  Here both teeth bite: the exact effect
digest changes and `kPol` itself is false on the mutation. -/
theorem demo_mutation_rejected :
    demoConfig.verifies demoRequest demoMutatedWitness = false := by decide

def demoEvidence : Evidence demoConfig.portal demoAuthState demoRequest :=
  .proof () rfl

/-- The adapter produces an actual request-indexed authorization from the
compiled gate; this is not merely a standalone Boolean-verifier example. -/
theorem demo_admission_isSome :
    (admit demoConfig demoAuthState demoRequest demoEvidence demoWitness () rfl rfl).isSome = true := by
  decide

/-- The theorem-level reflection really fires on the deployed keystone. -/
theorem demo_reflects_source :
    demoConfig.verifies demoRequest demoWitness = true ↔
      Minidregg.Pred.eval demoRecord.predicate kOld kNew = true := by
  apply canonical_verifies_iff_eval
  all_goals decide

/-! ## 6. Axiom audit. -/

/-- info: 'Minidregg.Compiler.CanonicalPolicyAdmission.canonical_verifies_iff_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_verifies_iff_eval

/-- info: 'Minidregg.Compiler.CanonicalPolicyAdmission.canonical_verifies_profile_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_verifies_profile_bound
/-- info: 'Minidregg.Compiler.CanonicalPolicyAdmission.CompilerSemanticDescriptor.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CompilerSemanticDescriptor.encode_injective

end Minidregg.Compiler.CanonicalPolicyAdmission
