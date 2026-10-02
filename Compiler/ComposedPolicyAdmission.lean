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
    "DREGG.POLICY.EFFECTIVE.CLOSURE/v1".toUTF8.toList
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

/-- The ordinary TypedAuthorization gate, now using the composed source portal.
Evidence, generation, revision, root membership and effective law all remain
mandatory; no policy-only result is presented as authorization. -/
def admit {F : Type} [Field F] [DecidableEq F]
    (config : Config F) {kind : ResourceKind} (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (witness : Witness F) (membership : config.portal.MembershipWitness)
    (epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId)
    (revisionExact : request.policyRevision = config.snapshot.authState.policyRevision request.policyId) :
    Option (Authorized config.portal config.snapshot.authState request) :=
  if addressExact : witness.compiled.address =
      config.snapshot.authState.policyAddress request.policyId request.policyRevision then
    if membershipAccepted : config.portal.verifyMembership config.snapshot.authState.policyRoot
        (config.snapshot.authState.policyAddress request.policyId request.policyRevision) membership = true then
      if accepted : config.verifies request witness = true then
        some
          { evidence := evidence
            policyWitness := witness
            policyMembershipWitness := membership
            policyEpochExact := epochExact
            policyRevisionExact := revisionExact
            policyAddressExact := addressExact
            policyMembershipVerified := membershipAccepted
            policyVerified := by simp [Config.portal, addressExact, accepted] }
      else none
    else none
  else none

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

end Minidregg.Compiler.ComposedPolicyAdmission
