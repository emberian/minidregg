/- Authenticated composition portal. The receiving source supplies the target,
step, extra structural roots, and guards; requests supply none of these. -/
import Compiler.PolicyComponentResolution
import Compiler.ResolvedLawCompilation

namespace Minidregg.Compiler.ComposedPolicyAdmission

open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyComponentResolution
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

private def keyWords (key : Key) : List Nat :=
  [key.policyId.value, key.facet.tag, key.revision, key.sourceDigest.value]

/-- Source digest and effective closure digest are distinct identities. Fixed
key widths plus counted vectors give unambiguous canonical manifest bytes.
Source addresses bind component bodies; the snapshot binds live parent edges. -/
def closureDigest {input : GraphInput} (resolved : ResolvedDAG input) : Digest :=
  let nodes := canonicalOrder resolved.postorder
  let words := [input.snapshot.domain.value, input.snapshot.semantics.value,
    input.snapshot.authorityRoot.value, input.snapshot.parentageRoot.value,
    input.roots.length] ++ input.roots.flatMap keyWords ++
    [nodes.length] ++ nodes.flatMap (fun node => keyWords node.key)
  (Minidregg.Compiler.Sp800185Cshake256.hash
    Minidregg.Theory.LawComposition.closureCustomization
    ((StreamCodec.list StreamCodec.nat).encode words)).digest

structure Config (F : Type) [Field F] [DecidableEq F] where
  snapshot : Snapshot
  store : PayloadStore
  base : Portal
  profile : PolicyCompilerProfile F
  step : PolicyStepContext
  target : Nat
  /-- Derived from physical descriptor cells by receiving source, with guards. -/
  additional : List PolicyRef := []
  resolutionBudget : Nat

abbrev Witness := ResolvedLawCompilation.Witness

def Config.verifies {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (witness : Witness F) : Bool :=
  match loadPolicy config.snapshot config.store ⟨config.target⟩
      (config.snapshot.authState.policyRevision ⟨config.target⟩),
    loadTarget config.snapshot config.store config.profile.semantics config.target
      config.resolutionBudget config.additional with
  | some head, .ok graph =>
      decide (request.target.value = config.target) &&
      decide (request.policyId = head.committed.record.policyId) &&
      decide (request.policyRevision = head.committed.record.version) &&
      decide (request.domain = config.snapshot.domain) &&
      decide (request.semantics = config.profile.semantics) &&
      (PolicyStepBinding.canonical config.step).matches request
        witness.compiled.oldState witness.compiled.newState &&
      config.profile.compatible (.canonical config.step) &&
      ResolvedLawCompilation.checks config.profile graph.resolved
        head.committed.address (closureDigest graph.resolved) witness
  | _, _ => false

/-- The other authority faces remain the canonical snapshot's domain portal.
Only source-loaded closure checking supplies the policy face. -/
def Config.portal {F : Type} [Field F] [DecidableEq F] (config : Config F) : Portal :=
  let base := domainPortal config.snapshot config.base
  { SignatureWitness := base.SignatureWitness
    ProofWitness := base.ProofWitness
    CapabilityCommitmentWitness := base.CapabilityCommitmentWitness
    CapabilityUseWitness := base.CapabilityUseWitness
    MembershipWitness := base.MembershipWitness
    IssuerWitness := base.IssuerWitness
    NonRevocationWitness := base.NonRevocationWitness
    PolicyWitness := Witness F
    policyAddress := fun witness => witness.compiled.address
    verifySignature := base.verifySignature
    verifyProof := base.verifyProof
    verifyCapabilityCommitment := base.verifyCapabilityCommitment
    verifyCapabilityUse := base.verifyCapabilityUse
    verifyMembership := base.verifyMembership
    verifyIssuer := base.verifyIssuer
    verifyNonRevocation := base.verifyNonRevocation
    verifyCommittedPolicy := fun address _ request witness =>
      decide (address = witness.compiled.address) && config.verifies request witness }

/-- Accepted composition is tied to the actual target, source-derived step,
compatible compiler, and the resolved law loaded from the same snapshot. -/
theorem verifies_sound {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (witness : Witness F) (accepted : config.verifies request witness = true) :
    ∃ graph : LoadedGraph config.snapshot config.store config.profile.semantics
        config.target config.additional,
      loadTarget config.snapshot config.store config.profile.semantics config.target
        config.resolutionBudget config.additional = .ok graph ∧
      request.target.value = config.target ∧
      witness.compiled.oldState = config.step.oldState ∧
      witness.compiled.newState = config.step.newState ∧
      witness.closureDigest = closureDigest graph.resolved ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        config.step.oldState config.step.newState = true := by
  unfold Config.verifies at accepted
  cases headFound : loadPolicy config.snapshot config.store ⟨config.target⟩
      (config.snapshot.authState.policyRevision ⟨config.target⟩) with
  | none => simp [headFound] at accepted
  | some head =>
    cases graphFound : loadTarget config.snapshot config.store config.profile.semantics
        config.target config.resolutionBudget config.additional with
    | error reason => simp [headFound, graphFound] at accepted
    | ok graph =>
      simp only [headFound, graphFound, Bool.and_eq_true, decide_eq_true_eq] at accepted
      rcases accepted with ⟨⟨⟨⟨⟨⟨⟨targetExact, _⟩, _⟩, _⟩, _⟩, stepExact⟩, _⟩, checked⟩
      have step := (canonical_step_matches_iff config.step request
        witness.compiled.oldState witness.compiled.newState).mp stepExact
      have result := ResolvedLawCompilation.checks_sound config.profile graph.resolved
        head.committed.address (closureDigest graph.resolved) witness checked
      exact ⟨graph, rfl, targetExact, step.2.2.2.1, step.2.2.2.2, result.2.1,
        by simpa only [step.2.2.2.1, step.2.2.2.2] using result.2.2⟩

/-- The same source capability constructor used by the original portal. Portal
replacement cannot skip holder/scope, native use, membership or revocation. -/
def Config.capabilityEvidenceChecked {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (identifier : CapabilityId)
    (commitment : config.portal.CapabilityCommitmentWitness)
    (use : config.portal.CapabilityUseWitness) (issuer : config.portal.IssuerWitness)
    (revocation : RevocationKey → config.portal.NonRevocationWitness) :
    Except RefusalReason
      (Evidence config.portal config.snapshot.authState request) :=
  (capabilityEvidenceCheckedFor config.snapshot config.portal request identifier
    commitment use issuer revocation (fun id => .capability kind id)).map Subtype.val

structure PreparedLaw {F : Type} [Field F] [DecidableEq F] (config : Config F) where
  head : LoadedPolicy config.snapshot config.store ⟨config.target⟩
    (config.snapshot.authState.policyRevision ⟨config.target⟩)
  headExact : loadPolicy config.snapshot config.store ⟨config.target⟩
    (config.snapshot.authState.policyRevision ⟨config.target⟩) = some head
  graph : LoadedGraph config.snapshot config.store config.profile.semantics
    config.target config.additional
  graphExact : loadTarget config.snapshot config.store config.profile.semantics config.target
    config.resolutionBudget config.additional = .ok graph

def Config.resolve? {F : Type} [Field F] [DecidableEq F] (config : Config F) :
    Option (PreparedLaw config) :=
  match headExact : loadPolicy config.snapshot config.store ⟨config.target⟩
      (config.snapshot.authState.policyRevision ⟨config.target⟩) with
  | none => none
  | some head =>
      match exact : loadTarget config.snapshot config.store config.profile.semantics config.target
          config.resolutionBudget config.additional with
      | .error _ => none
      | .ok graph => some ⟨head, headExact, graph, exact⟩

/-- Reuse a resolution from this exact configuration. The supplied witness is
still checked in full; a retained graph is not itself authorization. -/
def PreparedLaw.verifies {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind)
    (witness : Witness F) : Bool :=
  decide (request.target.value = config.target) &&
  decide (request.policyId = law.head.committed.record.policyId) &&
  decide (request.policyRevision = law.head.committed.record.version) &&
  decide (request.domain = config.snapshot.domain) &&
  decide (request.semantics = config.profile.semantics) &&
  (PolicyStepBinding.canonical config.step).matches request
    witness.compiled.oldState witness.compiled.newState &&
  config.profile.compatible (.canonical config.step) &&
  ResolvedLawCompilation.checks config.profile law.graph.resolved
    law.head.committed.address (closureDigest law.graph.resolved) witness

/-- Exact Boolean equality, including every rejecting branch and arbitrary
supplied witnesses; no assumption about a successful policy evaluation. -/
theorem PreparedLaw.verifies_eq {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind)
    (witness : Witness F) : law.verifies request witness = config.verifies request witness := by
  simp only [Config.verifies, law.headExact, law.graphExact, PreparedLaw.verifies]

def PreparedLaw.predicate {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (law : PreparedLaw config) : Pred := ResolvedLawCompilation.predicate law.graph.resolved

def PreparedLaw.witness {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (law : PreparedLaw config) : Witness F :=
  ⟨ResolvedLawCompilation.witness config.profile.compiler law.graph.resolved
    law.head.committed.address config.step.oldState config.step.newState,
    closureDigest law.graph.resolved⟩

def PreparedLaw.binding {F : Type} [Field F] [DecidableEq F] {config : Config F}
    (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind) : Bool :=
  decide (request.target.value = config.target) &&
  decide (request.policyId = law.head.committed.record.policyId) &&
  decide (request.policyRevision = law.head.committed.record.version) &&
  decide (request.domain = config.snapshot.domain) &&
  decide (request.semantics = config.profile.semantics) &&
  (PolicyStepBinding.canonical config.step).matches request config.step.oldState config.step.newState &&
  config.profile.compatible (.canonical config.step)

/-- The same lowering fold both constructs witnesses and decides the effective
law. Binding facts remain explicit; diagnostic evaluation cannot authorize an
unbound or stale request. -/
theorem PreparedLaw.verifies_iff_eval {F : Type} [Field F] [DecidableEq F]
    {config : Config F} (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind)
    (bound : law.binding request = true)
    (supportedExact : supported config.profile.compiler law.predicate = true)
    (rangesExact : inputsInRange config.profile.compiler law.predicate
      config.step.oldState config.step.newState = true)
    (casts : castInjOn F (intsOf law.predicate config.step.oldState config.step.newState)) :
    config.verifies request law.witness = true ↔
      Minidregg.Pred.eval law.predicate config.step.oldState config.step.newState = true := by
  have same : config.verifies request law.witness =
      (law.binding request && compiledLawAccepts config.profile law.predicate law.witness.compiled) := by
    simp [Config.verifies, law.headExact, law.graphExact, PreparedLaw.binding,
      ResolvedLawCompilation.checks, PreparedLaw.witness, ResolvedLawCompilation.witness,
      PreparedLaw.predicate, Bool.and_assoc]
  rw [same, bound, Bool.true_and]
  constructor
  · intro accepted
    exact compiledLawAccepts_sound config.profile law.predicate law.witness.compiled accepted
  · intro evaluated
    have lowered := lower_complete config.profile.compiler config.profile.admissible
      casts supportedExact rangesExact evaluated
    simp only [compiledLawAccepts, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨supportedExact, rangesExact⟩, casts⟩, lowered⟩

theorem Config.capabilityEvidence_names_stored {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (identifier : CapabilityId) (commitment : config.portal.CapabilityCommitmentWitness)
    (use : config.portal.CapabilityUseWitness) (issuer : config.portal.IssuerWitness)
    (revocation : RevocationKey → config.portal.NonRevocationWitness)
    {evidence : Evidence config.portal config.snapshot.authState request}
    (accepted : config.capabilityEvidenceChecked request identifier commitment use issuer revocation = .ok evidence) :
    NamesStored config.snapshot identifier evidence := by
  unfold Config.capabilityEvidenceChecked at accepted
  cases result : capabilityEvidenceCheckedFor config.snapshot config.portal request identifier
      commitment use issuer revocation (fun id => .capability kind id) with
  | error reason => simp [result, Except.map] at accepted
  | ok checked =>
      simp only [result, Except.map, Except.ok.injEq] at accepted
      rw [← accepted]
      exact checked.property

/-- Witness construction uses the same loaded closure and the receiver's exact
pre/post projection. Failure never supplies a permissive fallback witness. -/
def Config.witness? {F : Type} [Field F] [DecidableEq F]
    (config : Config F) : Option (Witness F) := do
  let head ← loadPolicy config.snapshot config.store ⟨config.target⟩
    (config.snapshot.authState.policyRevision ⟨config.target⟩)
  let graph ← (loadTarget config.snapshot config.store config.profile.semantics config.target
    config.resolutionBudget config.additional).toOption
  pure ⟨ResolvedLawCompilation.witness config.profile.compiler graph.resolved
    head.committed.address config.step.oldState config.step.newState,
    closureDigest graph.resolved⟩

/-- One admission gate for ordinary and already-resolved policy checks. The
check remains lazy until address and membership pass, preserving refusal order. -/
private def admitWithCheck {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId)
    (check : Unit → Bool) (checkExact : check () = config.verifies request witness) :
    Option (Authorized config.portal config.snapshot.authState request) :=
  if addressExact : witness.compiled.address =
      config.snapshot.authState.policyAddress request.policyId request.policyRevision then
    if membershipAccepted : config.portal.verifyMembership config.snapshot.authState.policyRoot
        (config.snapshot.authState.policyAddress request.policyId request.policyRevision) membership = true then
      if accepted : check () = true then
        some
          { evidence := evidence
            policyWitness := witness
            policyMembershipWitness := membership
            policyEpochExact := epochExact
            policyRevisionExact := revisionExact
            policyAddressExact := addressExact
            policyMembershipVerified := membershipAccepted
            policyVerified := by
              have verified := checkExact.symm.trans accepted
              simp [Config.portal, addressExact, verified] }
      else none
    else none
  else none

/-- Ordinary callers perform the complete source resolution as before. -/
def admit {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId) :
    Option (Authorized config.portal config.snapshot.authState request) :=
  admitWithCheck config request evidence witness membership epochExact revisionExact
    (fun _ => config.verifies request witness) rfl

/-- Reuse only the head/graph whose exact source equations this value retains.
All other authorization checks run through the same ordinary gate. -/
def PreparedLaw.admit {F : Type} [Field F] [DecidableEq F]
    {config : Config F} (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId) :
    Option (Authorized config.portal config.snapshot.authState request) :=
  admitWithCheck config request evidence witness membership epochExact revisionExact
    (fun _ => law.verifies request witness) (law.verifies_eq request witness)

/-- The complete authorization result, including refusals and retained
witness/evidence values, is identical to ordinary source resolution. -/
theorem PreparedLaw.admit_eq {F : Type} [Field F] [DecidableEq F]
    {config : Config F} (law : PreparedLaw config) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId) :
    law.admit request evidence witness membership epochExact revisionExact =
      ComposedPolicyAdmission.admit config request evidence witness membership epochExact revisionExact := by
  simp only [PreparedLaw.admit, ComposedPolicyAdmission.admit, PreparedLaw.verifies_eq]

/-! ## Authorization with the law's verdict left to the Receiver -/

/-- **Authorization, the law's verdict not included.**  Every fact `admit`
establishes about a request except the committed law's verdict on the step: the
capability evidence; the target's committed head and closure resolved from this
configuration (`law`); the request bound to that head, this domain, these
semantics and this step (`PreparedLaw.binding`); its epoch and revision current;
the head's address the one the authority state commits to, and a member of the
policy root.  A family on `Kernel.Receiving.Family` whose write to
`config.target` projects `config.step` as its law step leaves the verdict to the
Receiver (`Kernel.ReceivingLaw.judgeWrite`), so the law is judged once;
`Bound.admit_of_verifies` shows that with the verdict this is `admit`. -/
structure Bound {F : Type} [Field F] [DecidableEq F] (config : Config F) {kind : ResourceKind}
    (request : Request kind) where
  evidence : Evidence config.portal config.snapshot.authState request
  law : PreparedLaw config
  bound : law.binding request = true
  membership : config.portal.MembershipWitness
  epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId
  revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId
  addressExact : law.witness.compiled.address =
    config.snapshot.authState.policyAddress request.policyId request.policyRevision
  membershipVerified : config.portal.verifyMembership config.snapshot.authState.policyRoot
    (config.snapshot.authState.policyAddress request.policyId request.policyRevision) membership = true

/-- Bind a request to a resolved law: the checks of `admit` up to, and not
including, the law's verdict. -/
def bind {F : Type} [Field F] [DecidableEq F] (config : Config F) {kind : ResourceKind}
    (request : Request kind) (evidence : Evidence config.portal config.snapshot.authState request)
    (law : PreparedLaw config) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId) :
    Option (Bound config request) :=
  if bound : law.binding request = true then
    if addressExact : law.witness.compiled.address =
        config.snapshot.authState.policyAddress request.policyId request.policyRevision then
      if membershipVerified : config.portal.verifyMembership config.snapshot.authState.policyRoot
          (config.snapshot.authState.policyAddress request.policyId request.policyRevision)
          membership = true then
        some ⟨evidence, law, bound, membership, epochExact, revisionExact, addressExact,
          membershipVerified⟩
      else none
    else none
  else none

/-- **With the law's verdict, a bound request is admitted**: the compiled verdict
on the bound law's witness is all `admit` adds. -/
theorem Bound.admit_of_verifies {F : Type} [Field F] [DecidableEq F] {config : Config F}
    {kind : ResourceKind} {request : Request kind} (bound : Bound config request)
    (verified : config.verifies request bound.law.witness = true) :
    ∃ authorized, admit config request bound.evidence bound.law.witness bound.membership
      bound.epochExact bound.revisionExact = some authorized := by
  unfold admit admitWithCheck
  dsimp only
  rw [dif_pos bound.addressExact, dif_pos bound.membershipVerified, dif_pos verified]
  exact ⟨_, rfl⟩

/-- **The compiled verdict of a bound request is the law's `Pred.eval`**, under
the three compiler verdicts the Receiver reads (`PhysicalLawResolution.Judged`). -/
theorem Bound.verifies_iff_eval {F : Type} [Field F] [DecidableEq F] {config : Config F}
    {kind : ResourceKind} {request : Request kind} (bound : Bound config request)
    (supportedExact : supported config.profile.compiler bound.law.predicate = true)
    (rangesExact : inputsInRange config.profile.compiler bound.law.predicate
      config.step.oldState config.step.newState = true)
    (casts : castInjOn F (intsOf bound.law.predicate config.step.oldState config.step.newState)) :
    config.verifies request bound.law.witness = true ↔
      Minidregg.Pred.eval bound.law.predicate config.step.oldState config.step.newState = true :=
  bound.law.verifies_iff_eval request bound.bound supportedExact rangesExact casts

theorem admit_preserves_evidence {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId)
    {authorized : Authorized config.portal config.snapshot.authState request}
    (accepted : admit config request evidence witness membership epochExact revisionExact = some authorized) :
    authorized.evidence = evidence := by
  unfold admit admitWithCheck at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted; rfl
      · cases accepted
    · cases accepted
  · cases accepted

theorem authorized_effective_law {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (authorized : Authorized config.portal config.snapshot.authState request) :
    ∃ graph : LoadedGraph config.snapshot config.store config.profile.semantics
        config.target config.additional,
      loadTarget config.snapshot config.store config.profile.semantics config.target
        config.resolutionBudget config.additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        config.step.oldState config.step.newState = true := by
  have checked := authorized.policyVerified
  change (_ && config.verifies request authorized.policyWitness) = true at checked
  simp only [Bool.and_eq_true] at checked
  have accepted := checked.2
  obtain ⟨graph, loaded, _, _, _, _, law⟩ :=
    verifies_sound config request authorized.policyWitness accepted
  exact ⟨graph, loaded, law⟩

/-- info: 'Minidregg.Compiler.ComposedPolicyAdmission.PreparedLaw.verifies_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedLaw.verifies_eq
/-- info: 'Minidregg.Compiler.ComposedPolicyAdmission.PreparedLaw.admit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedLaw.admit_eq

#assert_axioms Bound.admit_of_verifies
#assert_axioms Bound.verifies_iff_eval

end Minidregg.Compiler.ComposedPolicyAdmission
