/-
# Theory.CredentialAuthorityFamily — one authority family, several credential carriers

`TypedAuthorization.Authorized` is the sole authorization judgment.  This module
does not add a signature policy, a proof policy, or a token policy.  It gives the
existing request-indexed judgment one common semantic envelope and makes legacy
credential *carriers* explicit:

* signatures and arbitrary proofs are exact-request grants;
* capabilities carry their committed holder, scope, time window, epochs, and
  revocation lineage;
* token-style credentials are a transport presentation of capability evidence,
  not a fourth route around the common policy gate.

The canonical request word is retained beside any deployment digest.  Lean proves
that the digest is computed from that exact word; collision resistance of a
deployment hash remains a cryptographic portal premise and is not manufactured as
a theorem about `Nat`.

Strict attenuation includes holder narrowing. Explicit subject delegation uses
a distinct edge carrying its complete producing request and payload bounds;
the mutation family additionally requires actual parent authorization. Both
forms reject a bearer child from a subject parent and retain checked lineage.
-/
import Theory.AuthorizationDeclaration

namespace Minidregg.Theory.CredentialAuthorityFamily

open TypedAuthorization
open AuthorizationDeclaration

/-! Delegation is an explicitly authorized production step. Its retained
first-order origin is historical data, not a cryptographic certificate. -/

def delegateVerb : (kind : ResourceKind) → Verb kind
  | .object => .delegateObject
  | .account => .delegateAccount
  | .program => .delegateProgram

inductive LineageOrigin (kind : ResourceKind) where
  | strict
  | delegated (request : Request kind)
  deriving DecidableEq

structure ParentLink (kind : ResourceKind) where
  parent : Capability kind
  origin : LineageOrigin kind
  deriving DecidableEq

/-- The static shape of a recorded subject delegation. Creation additionally
requires actual exact-parent capability authorization in the effect mode.
Historical grantor keys are deliberately not reauthorized at descendant use. -/
structure DelegationShape {kind : ResourceKind} (request : Request kind)
    (child parent : Capability kind) : Prop where
  payload : child.Attenuates parent
  grantor : parent.holder = .subject request.subject
  recipient : child.holder ≠ .bearer
  delegate : request.verb = delegateVerb kind
  target : child.scope.targets = {request.target}
  parentScope : parent.scope.Covers request
  validFrom : parent.notBefore ≤ request.height
  validUntil : request.height ≤ parent.notAfter
  policyId : parent.policyId = request.policyId
  policyEpoch : parent.policyEpoch = request.policyEpoch

theorem DelegationShape.recipient_is_subject {kind : ResourceKind}
    {request : Request kind} {child parent : Capability kind}
    (shape : DelegationShape request child parent) :
    ∃ subject, child.holder = .subject subject := by
  cases holder : child.holder with
  | bearer => exact False.elim (shape.recipient holder)
  | subject subject => exact ⟨subject, rfl⟩

theorem DelegationShape.requires_delegate_verb {kind : ResourceKind}
    {request : Request kind} {child parent : Capability kind}
    (shape : DelegationShape request child parent) :
    delegateVerb kind ∈ parent.scope.verbs := by
  simpa only [shape.delegate] using shape.parentScope.verb

theorem DelegationShape.no_other_target {kind : ResourceKind}
    {request : Request kind} {child parent : Capability kind}
    (shape : DelegationShape request child parent)
    (target : ResourceId kind) (member : target ∈ child.scope.targets) :
    target = request.target := by
  simpa only [shape.target, Finset.mem_singleton] using member

/-! ## 1. An exact canonical request word underneath every deployment digest -/

/-- A deployment chooses how to digest the lossless authorization request word.
No collision-resistance proposition is hidden in this data-only interface. -/
structure RequestDigestScheme where
  digestWire : RequestWire → Digest

/-- The digest retained by an accepted credential is derived from the exact,
lossless request word.  Neither the word nor the digest is supplied independently
of the request index. -/
structure RequestBinding (scheme : RequestDigestScheme)
    {kind : ResourceKind} (request : Request kind) where
  wire : RequestWire
  wireExact : wire = encodeRequest ⟨kind, request⟩
  digest : Digest
  digestExact : digest = scheme.digestWire wire

def RequestBinding.canonical (scheme : RequestDigestScheme)
    {kind : ResourceKind} (request : Request kind) : RequestBinding scheme request where
  wire := encodeRequest ⟨kind, request⟩
  wireExact := rfl
  digest := scheme.digestWire (encodeRequest ⟨kind, request⟩)
  digestExact := rfl

/-- Losslessness is structural: equal canonical words decode to equal dependent
requests.  Hash collision resistance is needed only when a verifier discards the
word and compares digests alone. -/
theorem encodeRequest_injective {left right : SomeRequest}
    (same : encodeRequest left = encodeRequest right) : left = right := by
  have decoded := congrArg decodeRequest same
  simpa using decoded

theorem RequestBinding.digest_is_canonical
    {scheme : RequestDigestScheme} {kind : ResourceKind}
    {request : Request kind} (binding : RequestBinding scheme request) :
    binding.digest = scheme.digestWire (encodeRequest ⟨kind, request⟩) := by
  rw [binding.digestExact, binding.wireExact]

/-- A caller cannot replace the retained digest by a different value while still
constructing the exact binding. -/
theorem RequestBinding.reject_digest_substitution
    {scheme : RequestDigestScheme} {kind : ResourceKind}
    {request : Request kind} (binding : RequestBinding scheme request)
    {substitute : Digest}
    (different : substitute ≠ scheme.digestWire (encodeRequest ⟨kind, request⟩)) :
    binding.digest ≠ substitute := by
  rw [binding.digest_is_canonical]
  exact Ne.symm different

/-- Retargeting changes the canonical request word.  This is the information-
theoretic tooth below the deployment digest seam. -/
theorem retarget_changes_wire {kind : ResourceKind} (request : Request kind)
    (target : ResourceId kind) (different : target ≠ request.target) :
    encodeRequest ⟨kind, request.retarget target⟩ ≠
      encodeRequest ⟨kind, request⟩ := by
  intro same
  apply different
  cases target
  cases request
  simp_all [encodeRequest, Request.retarget]

/-! ## 2. Holder-aware attenuation and proof-relevant lineage -/

end Minidregg.Theory.CredentialAuthorityFamily

namespace Minidregg.Theory.TypedAuthorization.Holder

/-- Holder attenuation is semantic inclusion: every subject covered by the child
was already covered by the parent. -/
def Narrows (child parent : Holder) : Prop :=
  ∀ subject, child.Covers subject → parent.Covers subject

theorem narrows_refl (holder : Holder) : holder.Narrows holder := by
  intro subject covered
  exact covered

theorem narrows_trans {young middle old : Holder}
    (first : young.Narrows middle) (second : middle.Narrows old) :
    young.Narrows old := by
  intro subject covered
  exact second subject (first subject covered)

theorem subject_narrows_bearer (subject : SubjectId) :
    (Holder.subject subject).Narrows .bearer := by
  intro _ _
  trivial

/-- Negative tooth: changing a subject-bound parent into a bearer child is an
authority amplification and therefore cannot be a strict attenuation edge. -/
theorem bearer_not_narrows_subject (subject : SubjectId) :
    ¬ Holder.bearer.Narrows (.subject subject) := by
  intro narrows
  let other : SubjectId := ⟨subject.value + 1⟩
  have bound : subject = other := by
    simpa [Holder.Covers] using narrows other (by trivial)
  have equal : other = subject := bound.symm
  have values := congrArg SubjectId.value equal
  simp [other] at values

end Holder
end Minidregg.Theory.TypedAuthorization

namespace Minidregg.Theory.CredentialAuthorityFamily

open TypedAuthorization
open AuthorizationDeclaration

end Minidregg.Theory.CredentialAuthorityFamily

namespace Minidregg.Theory.TypedAuthorization.Capability

/-- Complete attenuation adds the holder order omitted by the transport-level
`Capability.Attenuates` record. -/
structure StrictAttenuates {kind : ResourceKind}
    (child parent : Capability kind) : Prop where
  payload : child.Attenuates parent
  holder : child.holder.Narrows parent.holder

/-- Strict attenuation is fully monotone; no extra caller-supplied parent-holder
premise remains. -/
theorem strict_attenuation_admits_subset {kind : ResourceKind}
    {child parent : Capability kind} {state : AuthState}
    {request : Request kind}
    (edge : child.StrictAttenuates parent)
    (admitted : child.Admissible state request) :
    parent.Admissible state request :=
  Capability.attenuation_admits_subset edge.payload admitted
    (edge.holder request.subject admitted.holder)

/-- The transitive payload bounds of a lineage, forgetting only the immediate
parent marker and holder. This is a theorem projection, not another admission
or executable authority relation. -/
structure LineageBounds {kind : ResourceKind} (child ancestor : Capability kind) : Prop where
  root : child.root = ancestor.root
  issuer : child.issuer = ancestor.issuer
  scope : child.scope.Narrows ancestor.scope
  notBefore : ancestor.notBefore ≤ child.notBefore
  notAfter : child.notAfter ≤ ancestor.notAfter
  issuerEpoch : child.issuerEpoch = ancestor.issuerEpoch
  policyId : child.policyId = ancestor.policyId
  policyEpoch : child.policyEpoch = ancestor.policyEpoch
  ancestors : ancestor.ancestors ⊆ child.ancestors
  channels : ancestor.channels ⊆ child.channels

theorem LineageBounds.refl {kind : ResourceKind} (capability : Capability kind) :
    LineageBounds capability capability :=
  ⟨rfl, rfl, ⟨fun _ member => member, fun _ member => member, le_rfl⟩,
    le_rfl, le_rfl, rfl, rfl, rfl, fun _ member => member, fun _ member => member⟩

theorem LineageBounds.trans {kind : ResourceKind}
    {young middle old : Capability kind}
    (first : LineageBounds young middle) (second : LineageBounds middle old) :
    LineageBounds young old where
  root := first.root.trans second.root
  issuer := first.issuer.trans second.issuer
  scope :=
    ⟨fun _ member => second.scope.targets (first.scope.targets member),
      fun _ member => second.scope.verbs (first.scope.verbs member),
      le_trans first.scope.maxCost second.scope.maxCost⟩
  notBefore := le_trans second.notBefore first.notBefore
  notAfter := le_trans first.notAfter second.notAfter
  issuerEpoch := first.issuerEpoch.trans second.issuerEpoch
  policyId := first.policyId.trans second.policyId
  policyEpoch := first.policyEpoch.trans second.policyEpoch
  ancestors := fun _ member => first.ancestors (second.ancestors member)
  channels := fun _ member => first.channels (second.channels member)

theorem Attenuates.lineageBounds {kind : ResourceKind}
    {child parent : Capability kind} (edge : child.Attenuates parent) :
    LineageBounds child parent where
  root := edge.root
  issuer := edge.issuer
  scope := edge.scopeNarrows
  notBefore := edge.notBefore
  notAfter := edge.notAfter
  issuerEpoch := edge.issuerEpoch
  policyId := edge.policyId
  policyEpoch := edge.policyEpoch
  ancestors := by
    intro ancestor member
    rw [edge.ancestors]
    exact Finset.mem_insert_of_mem member
  channels := edge.channels

/-- A capability's parent/root identifiers become meaningful only with this
proof-relevant derivation. Each edge retains its actual parent and either strict
holder narrowing or the static shape of an explicit subject delegation. -/
inductive Lineage {kind : ResourceKind} : Capability kind → Type
  | root (cap : Capability kind)
      (parentNone : cap.parent = none)
      (rootSelf : cap.root = cap.id)
      (ancestorsEmpty : cap.ancestors = ∅) : cap.Lineage
  | attenuate (child parent : Capability kind)
      (parentLineage : parent.Lineage)
      (edge : child.StrictAttenuates parent) : child.Lineage
  | delegate (child parent : Capability kind) (request : Request kind)
      (parentLineage : parent.Lineage)
      (shape : CredentialAuthorityFamily.DelegationShape request child parent) : child.Lineage

def Lineage.rootCapability {kind : ResourceKind}
    {cap : Capability kind} : cap.Lineage → Capability kind
  | .root rootCap _ _ _ => rootCap
  | .attenuate _ _ parentLineage _ => parentLineage.rootCapability
  | .delegate _ _ _ parentLineage _ => parentLineage.rootCapability

def Lineage.IsStrict {kind : ResourceKind} {cap : Capability kind} : cap.Lineage → Prop
  | .root .. => True
  | .attenuate _ _ parentLineage _ => parentLineage.IsStrict
  | .delegate .. => False

theorem Lineage.root_bounds {kind : ResourceKind} {cap : Capability kind}
    (lineage : cap.Lineage) : LineageBounds cap lineage.rootCapability := by
  induction lineage with
  | root rootCap _ _ _ => exact LineageBounds.refl rootCap
  | attenuate child parent parentLineage edge induction =>
      exact edge.payload.lineageBounds.trans induction
  | delegate child parent request parentLineage shape induction =>
      exact shape.payload.lineageBounds.trans induction

/-- Same-request root admission remains true for strict-only lineages.
Subject transfer deliberately changes who may use the child, so mixed lineage
has `root_bounds` instead of a false same-holder monotonicity claim. -/
theorem Lineage.root_admissible_of_strict {kind : ResourceKind}
    {cap : Capability kind} {state : AuthState} {request : Request kind}
    (lineage : cap.Lineage) (strict : lineage.IsStrict)
    (admitted : cap.Admissible state request) :
    lineage.rootCapability.Admissible state request := by
  induction lineage with
  | root => simpa [Lineage.rootCapability] using admitted
  | attenuate child parent parentLineage edge ih =>
      exact ih strict (strict_attenuation_admits_subset edge admitted)
  | delegate child parent request parentLineage shape ih => exact False.elim strict

end Capability
end Minidregg.Theory.TypedAuthorization

namespace Minidregg.Theory.CredentialAuthorityFamily

open TypedAuthorization
open AuthorizationDeclaration

/-! ## 3. One semantic envelope for every existing evidence constructor -/

/-- Direct signature/proof authority covers exactly one target and one verb, with
exactly the request's budget.  It cannot silently authorize a wider effect. -/
def exactRequestScope {kind : ResourceKind} (request : Request kind) : Scope kind where
  targets := {request.target}
  verbs := {request.verb}
  maxCost := request.cost

theorem exactRequestScope_covers {kind : ResourceKind} (request : Request kind) :
    (exactRequestScope request).Covers request := by
  exact ⟨by simp [exactRequestScope], by simp [exactRequestScope], by simp [exactRequestScope]⟩

end Minidregg.Theory.CredentialAuthorityFamily

namespace Minidregg.Theory.TypedAuthorization.Evidence

def authorityHolder {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind} :
    Evidence portal state request → Holder
  | .signature .. => .subject request.subject
  | .proof .. => .subject request.subject
  | .capability cap .. => cap.holder

def authorityScope {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind} :
    Evidence portal state request → Scope kind
  | .signature .. => CredentialAuthorityFamily.exactRequestScope request
  | .proof .. => CredentialAuthorityFamily.exactRequestScope request
  | .capability cap .. => cap.scope

/-- Mode-specific freshness is exposed under one name.  A proof portal verifies
the exact request and may choose its own credential-freshness statement; current
policy remains mandatory below.  Signature key epochs and all capability issuer /
revocation facts are explicit here. -/
def Current {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind} :
    Evidence portal state request → Prop
  | .signature _ keyEpochExact _ =>
      request.subjectKeyEpoch = state.subjectKeyEpoch request.subject
  | .proof .. => True
  | .capability cap _ _ _ _ _ _ _ .. =>
      cap.issuerEpoch = state.issuerEpoch cap.issuer ∧
      RevocationKey.capability cap.id ∉ state.revoked ∧
      (∀ ancestor ∈ cap.ancestors,
        RevocationKey.capability ancestor ∉ state.revoked) ∧
      (∀ channel ∈ cap.channels,
        RevocationKey.channel channel ∉ state.revoked)

/-- Capability evidence must carry a real attenuation derivation.  Direct
signature/proof grants have no lineage and therefore use `PUnit`. -/
def LineageRequirement {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind} :
    Evidence portal state request → Type
  | .signature .. => PUnit
  | .proof .. => PUnit
  | .capability cap .. => cap.Lineage

structure SemanticEnvelope {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence portal state request) : Prop where
  holder : evidence.authorityHolder.Covers request.subject
  scope : evidence.authorityScope.Covers request
  current : evidence.Current

theorem semanticEnvelope {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence portal state request) : evidence.SemanticEnvelope := by
  cases evidence with
  | signature witness keyEpochExact verified =>
      exact ⟨rfl, CredentialAuthorityFamily.exactRequestScope_covers request,
        keyEpochExact⟩
  | proof witness verified =>
      exact ⟨rfl, CredentialAuthorityFamily.exactRequestScope_covers request,
        trivial⟩
  | capability cap commitment commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified
      commitmentVerified membershipVerified issuerVerified
      selfRevocationVerified ancestorVerified channelVerified =>
      exact ⟨semantic.holder, semantic.scope,
        semantic.issuerCurrent, semantic.selfNotRevoked,
        semantic.ancestorNotRevoked, semantic.channelNotRevoked⟩

end Evidence
end Minidregg.Theory.TypedAuthorization

namespace Minidregg.Theory.CredentialAuthorityFamily

open TypedAuthorization
open AuthorizationDeclaration

/-! ## 4. Credential carriers classify evidence; they do not authorize -/

inductive CarrierKind where
  | signature
  | proof
  | capability
  | token
  deriving DecidableEq, Repr

end Minidregg.Theory.CredentialAuthorityFamily

namespace Minidregg.Theory.TypedAuthorization.Evidence

open CredentialAuthorityFamily

/-- A token-style carrier is supported only by capability evidence.  Thus a
macaroon/Biscuit-like encoding may transport attenuation data, but cannot become
an early-return authorization mode. -/
def Supports {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence portal state request) : CarrierKind → Prop :=
  match evidence with
  | .signature .. => fun carrier => carrier = .signature
  | .proof .. => fun carrier => carrier = .proof
  | .capability .. => fun carrier => carrier = .capability ∨ carrier = .token

theorem supports_token_iff_capability
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence portal state request) :
    evidence.Supports .token ↔ evidence.Supports .capability := by
  cases evidence <;> simp [Evidence.Supports]

end Evidence
end Minidregg.Theory.TypedAuthorization

namespace Minidregg.Theory.CredentialAuthorityFamily

open TypedAuthorization
open AuthorizationDeclaration

/-- The single accepted credential family.  Its only authority field is the
existing `Authorized`; therefore every carrier necessarily passes the same final
policy epoch and policy verifier checks. -/
structure AcceptedCredential (scheme : RequestDigestScheme)
    (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type where
  authorization : Authorized portal state request
  carrier : CarrierKind
  carrierSupported : authorization.evidence.Supports carrier
  requestBinding : RequestBinding scheme request
  lineage : authorization.evidence.LineageRequirement

theorem AcceptedCredential.policy_epoch_current
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    request.policyEpoch = state.policyEpoch request.policyId :=
  accepted.authorization.policyEpochExact

theorem AcceptedCredential.policy_revision_current
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    request.policyRevision = state.policyRevision request.policyId :=
  accepted.authorization.policyRevisionExact

theorem AcceptedCredential.policy_selected
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    portal.verifyCommittedPolicy
      (state.policyAddress request.policyId request.policyRevision)
      request accepted.authorization.policyWitness = true :=
  accepted.authorization.policyVerified

theorem AcceptedCredential.holder_covers
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    accepted.authorization.evidence.authorityHolder.Covers request.subject :=
  accepted.authorization.evidence.semanticEnvelope.holder

theorem AcceptedCredential.effect_scope_and_budget
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    accepted.authorization.evidence.authorityScope.Covers request :=
  accepted.authorization.evidence.semanticEnvelope.scope

theorem AcceptedCredential.current
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request) :
    accepted.authorization.evidence.Current :=
  accepted.authorization.evidence.semanticEnvelope.current

/-- Negative tooth: token transport and capability transport are exactly the
same semantic evidence class. -/
theorem AcceptedCredential.token_has_no_bypass
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request)
    (token : accepted.carrier = .token) :
    accepted.authorization.evidence.Supports .capability := by
  apply (accepted.authorization.evidence.supports_token_iff_capability).mp
  simpa [token] using accepted.carrierSupported

/-- Negative tooth: no accepted credential can exceed its semantic scope budget. -/
theorem AcceptedCredential.reject_over_budget
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request)
    (overBudget : accepted.authorization.evidence.authorityScope.maxCost < request.cost) : False := by
  exact (Nat.not_lt_of_ge accepted.effect_scope_and_budget.cost) overBudget

/-- Negative tooth shared by every carrier: stale policy selection is
incompatible with acceptance, including token-style presentations. -/
theorem AcceptedCredential.reject_stale_policy
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request)
    (stale : request.policyEpoch ≠ state.policyEpoch request.policyId) : False :=
  stale accepted.policy_epoch_current

/-- A token-style credential cannot smuggle a revoked capability: its underlying
capability evidence retains the semantic non-revocation theorem. -/
theorem AcceptedCredential.token_current
    {scheme : RequestDigestScheme} {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (accepted : AcceptedCredential scheme portal state request)
    (_token : accepted.carrier = .token) :
    accepted.authorization.evidence.Current :=
  accepted.current

/-! ## 5. Concrete pole: token transport still uses capability authorization -/

def demoDigestScheme : RequestDigestScheme where
  digestWire := fun wire => ⟨wire.domain + wire.semantics + wire.target + wire.nonce⟩

def demoCapabilityLineage : demoCapability.Lineage :=
  .root demoCapability rfl rfl rfl

/-- This is deliberately only a semantic/API pole.  `demoDigestScheme` is not a
cryptographic digest, and `demoPortal` is not a production verifier. -/
def demoTokenAccepted :
    AcceptedCredential demoDigestScheme demoPortal demoState demoRequest where
  authorization := demo_authorized_positive
  carrier := .token
  carrierSupported := by
    simp [demo_authorized_positive, demoEvidence, Evidence.Supports]
  requestBinding := .canonical demoDigestScheme demoRequest
  lineage := demoCapabilityLineage

theorem demoToken_uses_common_policy :
    demoPortal.verifyCommittedPolicy
      (demoState.policyAddress demoRequest.policyId demoRequest.policyRevision)
      demoRequest
      demoTokenAccepted.authorization.policyWitness = true :=
  demoTokenAccepted.policy_selected

theorem demoToken_is_capability_evidence :
    demoTokenAccepted.authorization.evidence.Supports .capability :=
  demoTokenAccepted.token_has_no_bypass rfl

/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.encodeRequest_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encodeRequest_injective
/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.retarget_changes_wire' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms retarget_changes_wire
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.strict_attenuation_admits_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.strict_attenuation_admits_subset
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.Lineage.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.Lineage.root_admissible_of_strict
/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.AcceptedCredential.token_has_no_bypass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedCredential.token_has_no_bypass
/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.AcceptedCredential.reject_over_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedCredential.reject_over_budget
/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.demoToken_is_capability_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demoToken_is_capability_evidence

end Minidregg.Theory.CredentialAuthorityFamily
