/-
# Compiler.CanonicalPolicyAdmission -- committed `Pred` is the policy gate

The former address-free policy verifier permitted a caller to install a
Boolean function without first selecting committed policy content.
This module supplies the canonical constructor: the policy verifier is derived
only from a versioned, content-addressed `Pred` record and acceptance of
`PredCompile.lower`.  The other verifier portals remain explicit inputs.

The construction is honest about its boundary.  The request commits a policy
identifier and epoch, while a deployment registry resolves that pair to an
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
import Theory.TypedAuthorization

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
  version : Epoch
  domain : Digest
  semantics : Digest
  previous : Option Digest
  predicate : Pred
  deriving DecidableEq, Repr

/-- A registry entry names the exact content address beside its source record.
The verifier independently recomputes `recordDigest record` and checks it
against `address`; the registry does not get to assert that equality. -/
structure CommittedPolicy where
  address : Digest
  record : PolicyRecord
  deriving DecidableEq, Repr

/-- The deployment-owned resolution of `(PolicyId, Epoch)`.  Authenticating
this finite/durable registry and its root is deliberately outside this module. -/
structure PolicyRegistry where
  resolve : PolicyId → Epoch → Option CommittedPolicy

/-- The only policy witness type installed by the canonical portal.  It carries
the exact policy step and the AIR auxiliary assignment.  There is no predicate
or verifier function in the witness. -/
structure CompiledPolicyWitness (F : Type) where
  address : Digest
  oldState : State
  newState : State
  auxiliary : List ℕ → ℕ → F

/-! ## 2. Canonical portal construction. -/

/-- All inputs to the canonical policy verifier.  The base portal's policy
verifier and old witness type are intentionally ignored by `portal`; only the non-policy
verifier families are retained. -/
structure CanonicalPolicyConfig (F : Type) [Field F] [DecidableEq F] where
  base : Portal
  registry : PolicyRegistry
  recordDigest : PolicyRecord → Digest
  stateDigest : State → Digest
  stepDigest : State → State → Digest

/-- The exact conjunction checked by the policy gate.  In particular, the
verdict is acceptance of `PredCompile.lower`, not a second hand-written mirror
of the predicate evaluator. -/
def CanonicalPolicyConfig.verifies {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) : Bool :=
  match config.registry.resolve request.policyId request.policyEpoch with
  | none => false
  | some committed =>
      decide (committed.record.policyId = request.policyId) &&
      decide (committed.record.version = request.policyEpoch) &&
      decide (committed.record.domain = request.domain) &&
      decide (committed.record.semantics = request.semantics) &&
      decide (config.recordDigest committed.record = committed.address) &&
      decide (witness.address = committed.address) &&
      decide (config.stateDigest witness.oldState = request.preStateRoot) &&
      decide (config.stepDigest witness.oldState witness.newState = request.effectsDigest) &&
      supported committed.record.predicate &&
      decide (castInjOn F
        (intsOf committed.record.predicate witness.oldState witness.newState)) &&
      decide (systemAccepts
        (stepAsg witness.oldState witness.newState witness.auxiliary)
        (lower committed.record.predicate))

/-- Replace the arbitrary policy face of a portal by the committed compiler
gate.  The inherited policy witness and inherited policy verifier are erased. -/
def CanonicalPolicyConfig.portal {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) : Portal where
  SignatureWitness := config.base.SignatureWitness
  ProofWitness := config.base.ProofWitness
  CapabilityCommitmentWitness := config.base.CapabilityCommitmentWitness
  MembershipWitness := config.base.MembershipWitness
  IssuerWitness := config.base.IssuerWitness
  NonRevocationWitness := config.base.NonRevocationWitness
  PolicyWitness := CompiledPolicyWitness F
  policyAddress := fun witness => witness.address
  verifySignature := config.base.verifySignature
  verifyProof := config.base.verifyProof
  verifyCapabilityCommitment := config.base.verifyCapabilityCommitment
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
    config.registry.resolve request.policyId request.policyEpoch = some committed ∧
    committed.record.policyId = request.policyId ∧
    committed.record.version = request.policyEpoch ∧
    committed.record.domain = request.domain ∧
    committed.record.semantics = request.semantics ∧
    config.recordDigest committed.record = committed.address ∧
    witness.address = committed.address ∧
    config.stateDigest witness.oldState = request.preStateRoot ∧
    config.stepDigest witness.oldState witness.newState = request.effectsDigest ∧
    supported committed.record.predicate = true ∧
    castInjOn F (intsOf committed.record.predicate witness.oldState witness.newState) ∧
    systemAccepts
      (stepAsg witness.oldState witness.newState witness.auxiliary)
      (lower committed.record.predicate)

/-- The executable verifier has exactly the explicit reading above. -/
theorem verifies_iff_verified {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F) :
    config.verifies request witness = true ↔ Verified config request witness := by
  cases hresolve : config.registry.resolve request.policyId request.policyEpoch with
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
      config.registry.resolve request.policyId request.policyEpoch = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        witness.oldState witness.newState = true := by
  rcases (verifies_iff_verified config request witness).mp accepted with
    ⟨committed, resolved, _, _, _, _, _, _, _, _, supportedExact,
      castExact, compiled⟩
  exact ⟨committed, resolved, lower_sound castExact supportedExact compiled⟩

/-- The canonical prover witness is derived from the same lowering fold. -/
def canonicalWitness {F : Type} [Field F] [DecidableEq F]
    (committed : CommittedPolicy) (oldState newState : State) :
    CompiledPolicyWitness F where
  address := committed.address
  oldState := oldState
  newState := newState
  auxiliary := wit committed.record.predicate oldState newState

/-- Exact reflection for a resolved, digest-bound deployment instance.  The
forward implication is adversarial soundness; the reverse implication uses the
witness generator emitted by the same compiler fold. -/
theorem canonical_verifies_iff_eval {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    {oldState newState : State}
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (versionExact : committed.record.version = request.policyEpoch)
    (domainExact : committed.record.domain = request.domain)
    (semanticsExact : committed.record.semantics = request.semantics)
    (recordDigestExact : config.recordDigest committed.record = committed.address)
    (preRootExact : config.stateDigest oldState = request.preStateRoot)
    (effectDigestExact : config.stepDigest oldState newState = request.effectsDigest)
    (supportedExact : supported committed.record.predicate = true)
    (castExact : castInjOn F
      (intsOf committed.record.predicate oldState newState)) :
    config.verifies request (canonicalWitness committed oldState newState) = true ↔
      Minidregg.Pred.eval committed.record.predicate oldState newState = true := by
  constructor
  · intro accepted
    rcases verifies_sound accepted with ⟨selected, selectedExact, evaluated⟩
    rw [resolved] at selectedExact
    cases selectedExact
    exact evaluated
  · intro evaluated
    apply (verifies_iff_verified config request
      (canonicalWitness committed oldState newState)).mpr
    refine ⟨committed, resolved, policyIdExact, versionExact, domainExact,
      semanticsExact, recordDigestExact, rfl, preRootExact, effectDigestExact,
      supportedExact, castExact, ?_⟩
    exact lower_complete castExact supportedExact evaluated

/-! ## 4. Admission adapter and negative teeth. -/

/-- The canonical authorization target.  Its policy verifier is definitionally
the compiled committed verifier above; no policy function is an argument. -/
abbrev CanonicalAuthorized {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type :=
  Authorized config.portal state request

/-- Executable admission: after evidence and the exact current epoch are
present, the only remaining branch is the canonical compiled verifier. -/
def admit {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal state request)
    (witness : CompiledPolicyWitness F)
    (policyMembershipWitness : config.portal.MembershipWitness)
    (policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId) :
    Option (CanonicalAuthorized config state request) :=
  if addressExact : witness.address =
      state.policyAddress request.policyId request.policyEpoch then
    if membershipAccepted : config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyEpoch)
        policyMembershipWitness = true then
      if accepted : config.verifies request witness = true then
        some
          { evidence := evidence
            policyWitness := witness
            policyMembershipWitness := policyMembershipWitness
            policyEpochExact := policyEpochExact
            policyAddressExact := addressExact
            policyMembershipVerified := membershipAccepted
            policyVerified := by
              simp [CanonicalPolicyConfig.portal, addressExact, accepted] }
      else none
    else none
  else none

theorem admit_isSome_iff {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) (state : AuthState)
    {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal state request)
    (witness : CompiledPolicyWitness F)
    (policyMembershipWitness : config.portal.MembershipWitness)
    (policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId) :
    (admit config state request evidence witness policyMembershipWitness
      policyEpochExact).isSome = true ↔
      witness.address = state.policyAddress request.policyId request.policyEpoch ∧
      config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyEpoch)
        policyMembershipWitness = true ∧
      config.verifies request witness = true := by
  by_cases addressExact :
      witness.address = state.policyAddress request.policyId request.policyEpoch
  · by_cases membershipAccepted : config.portal.verifyMembership state.policyRoot
        (state.policyAddress request.policyId request.policyEpoch)
        policyMembershipWitness = true
    · by_cases accepted : config.verifies request witness = true <;>
        simp [admit, addressExact, membershipAccepted, accepted]
    · simp [admit, addressExact, membershipAccepted]
  · simp [admit, addressExact]

/-- A missing `(policyId,version)` record fails closed. -/
theorem unresolved_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} (witness : CompiledPolicyWitness F)
    (unresolved : config.registry.resolve request.policyId request.policyEpoch = none) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, unresolved]

/-- A registry entry whose internal policy id does not equal the request is
rejected even if it was returned from the requested lookup key. -/
theorem wrong_policy_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (wrong : committed.record.policyId ≠ request.policyId) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- A registry entry cannot lie about the version under which it was found. -/
theorem wrong_version_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (wrong : committed.record.version ≠ request.policyEpoch) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, policyIdExact, wrong]

/-- Content-address substitution fails before policy evaluation. -/
theorem wrong_address_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
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
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (wrong : config.recordDigest committed.record ≠ committed.address) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- Mutating the policy step without updating its request commitment fails. -/
theorem wrong_step_digest_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {committed : CommittedPolicy}
    (witness : CompiledPolicyWitness F)
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (wrong : config.stepDigest witness.oldState witness.newState ≠
      request.effectsDigest) :
    config.verifies request witness = false := by
  simp [CanonicalPolicyConfig.verifies, resolved, wrong]

/-- Even if all digest equalities collide or are rebound, a source-level policy
failure cannot be hidden by a malicious auxiliary assignment. -/
theorem policy_false_rejected {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F} {kind : ResourceKind}
    {request : Request kind} {witness : CompiledPolicyWitness F}
    (policyFalse : ∀ committed,
      config.registry.resolve request.policyId request.policyEpoch = some committed →
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
  version := demoRequest.policyEpoch
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
    if policyId = demoRequest.policyId ∧ version = demoRequest.policyEpoch then
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
  stateDigest := demoStateDigest
  stepDigest := demoStepDigest

/-- Authorization state selects the exact content address resolved by the
demo registry.  The registry root is illustrative; membership is discharged
by `demoPortal` and carries no cryptographic claim. -/
def demoAuthState : AuthState :=
  { demoState with
    policyAddress := fun policyId version =>
      if policyId = demoRequest.policyId ∧ version = demoRequest.policyEpoch then
        demoCommitted.address
      else ⟨0⟩ }

def demoWitness : CompiledPolicyWitness (ZMod 13) :=
  canonicalWitness demoCommitted kOld kNew

/-- Positive pole: the exact versioned policy, state commitment, effect
commitment, and emitted AIR witness are accepted. -/
theorem demo_policy_accepts : demoConfig.verifies demoRequest demoWitness = true := by
  decide

def demoWrongPolicyRequest : Request .object :=
  { demoRequest with policyId := ⟨999⟩ }

def demoWrongVersionRequest : Request .object :=
  { demoRequest with policyEpoch := demoRequest.policyEpoch + 1 }

def demoWrongAddressWitness : CompiledPolicyWitness (ZMod 13) :=
  { demoWitness with address := ⟨9999⟩ }

def demoMutatedWitness : CompiledPolicyWitness (ZMod 13) :=
  canonicalWitness demoCommitted kOld kBad

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
    (admit demoConfig demoAuthState demoRequest demoEvidence demoWitness () rfl).isSome = true := by
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

end Minidregg.Compiler.CanonicalPolicyAdmission
