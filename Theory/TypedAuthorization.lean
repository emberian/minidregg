/-
# Theory.TypedAuthorization — request-indexed authority for a typed effect machine

This is a clean-sheet authorization kernel.  It deliberately does not inherit
an account-system permission lattice, positional capability slots, or a family
of credential-shaped bypass modes.  Every authorization witness is indexed by
the COMPLETE semantic request that it authorizes.  A witness for one target,
verb, argument/effect commitment, nonce, epoch, or pre-state therefore does not
have the type required for another request.

Cryptography stays on the executable side of the verify/find seam.  `Portal`
contains concrete Boolean verifier predicates and witness types; it contains no
`soundness : Prop` escape hatch.  The pure `Capability.Admissible` relation is
the semantic statement those verifiers must accompany.

The capability commitment verifier receives the whole `Capability`, including
its exact issuer/policy epochs, ancestry, and revocation channels.  Membership
is checked against the current capability root, and non-revocation witnesses
are checked against the current revocation root for the capability itself,
EVERY committed ancestor, and EVERY committed channel.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Minidregg.Theory.TypedAuthorization

/-! ## §1. Typed names and the complete semantic request. -/

structure SubjectId where
  value : Nat
  deriving DecidableEq, Repr

structure IssuerId where
  value : Nat
  deriving DecidableEq, Repr

structure PolicyId where
  value : Nat
  deriving DecidableEq, Repr

structure FederationId where
  value : Nat
  deriving DecidableEq, Repr

structure CapabilityId where
  value : Nat
  deriving DecidableEq, Repr

structure ChannelId where
  value : Nat
  deriving DecidableEq, Repr

structure Digest where
  value : Nat
  deriving DecidableEq, Repr

abbrev Epoch := Nat
abbrev Height := Nat

/-- Resource kinds index both resource identifiers and their legal verbs. -/
inductive ResourceKind where
  | object
  | account
  | program
  deriving DecidableEq, Repr

/-- An identifier whose resource kind is present in its type. -/
structure ResourceId (_kind : ResourceKind) where
  value : Nat
  deriving DecidableEq, Repr

/-- Verbs are indexed by the kind on which they are meaningful.  A program
installation cannot accidentally be presented as an account transfer. -/
inductive Verb : ResourceKind → Type
  | observeObject : Verb .object
  | mutateObject : Verb .object
  | observeAccount : Verb .account
  | transfer : Verb .account
  | observeProgram : Verb .program
  | installProgram : Verb .program
  | delegateObject : Verb .object
  | delegateAccount : Verb .account
  | delegateProgram : Verb .program
  deriving DecidableEq, Repr

/-- The complete semantic authorization request.  Verifiers receive this value
directly; there are no prover-carried "bound target" strings to trust. -/
structure Request (kind : ResourceKind) where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  target : ResourceId kind
  verb : Verb kind
  argsDigest : Digest
  effectsDigest : Digest
  nonce : Nat
  height : Height
  preStateRoot : Digest
  policyId : PolicyId
  policyEpoch : Epoch
  cost : Nat
  deriving DecidableEq, Repr

/-- Change only the target of a request.  This produces a DIFFERENT request
index; existing `Evidence portal state request` cannot be reused at this type. -/
def Request.retarget {kind : ResourceKind} (request : Request kind)
    (target : ResourceId kind) : Request kind :=
  { request with target := target }

theorem Request.retarget_ne {kind : ResourceKind} (request : Request kind)
    (target : ResourceId kind) (hne : target ≠ request.target) :
    request.retarget target ≠ request := by
  intro heq
  have htarget := congrArg (fun r : Request kind => r.target) heq
  exact hne (by simpa [Request.retarget] using htarget)

/-! ## §2. Holders, scopes, and monotone attenuation. -/

/-- Bearer authority and subject-bound authority are different constructors.
A bearer capability intentionally authenticates possession, not identity. -/
inductive Holder where
  | bearer
  | subject (id : SubjectId)
  deriving DecidableEq, Repr

def Holder.Covers (holder : Holder) (subject : SubjectId) : Prop :=
  match holder with
  | .bearer => True
  | .subject bound => bound = subject

/-- A finite, typed authority scope. -/
structure Scope (kind : ResourceKind) where
  targets : Finset (ResourceId kind)
  verbs : Finset (Verb kind)
  maxCost : Nat
  deriving DecidableEq

structure Scope.Covers {kind : ResourceKind} (scope : Scope kind)
    (request : Request kind) : Prop where
  target : request.target ∈ scope.targets
  verb : request.verb ∈ scope.verbs
  cost : request.cost ≤ scope.maxCost

/-- `child.Narrows parent` is the authority preorder: fewer targets, fewer
verbs, and no larger budget. -/
structure Scope.Narrows {kind : ResourceKind} (child parent : Scope kind) : Prop where
  targets : child.targets ⊆ parent.targets
  verbs : child.verbs ⊆ parent.verbs
  maxCost : child.maxCost ≤ parent.maxCost

theorem Scope.covers_of_narrows {kind : ResourceKind}
    {child parent : Scope kind} {request : Request kind}
    (hn : child.Narrows parent) (hc : child.Covers request) :
    parent.Covers request :=
  { target := hn.targets hc.target
    verb := hn.verbs hc.verb
    cost := le_trans hc.cost hn.maxCost }

/-! ## §3. Capabilities and current committed authorization state. -/

/-- A capability's entire semantic payload.  A production commitment must bind
ALL of these fields without lossy folding. -/
structure Capability (kind : ResourceKind) where
  id : CapabilityId
  root : CapabilityId
  parent : Option CapabilityId
  issuer : IssuerId
  holder : Holder
  scope : Scope kind
  notBefore : Height
  notAfter : Height
  issuerEpoch : Epoch
  policyId : PolicyId
  policyEpoch : Epoch
  ancestors : Finset CapabilityId
  channels : Finset ChannelId
  deriving DecidableEq

inductive RevocationKey where
  | capability (id : CapabilityId)
  | channel (id : ChannelId)
  deriving DecidableEq, Repr

/-- The authorization-relevant projection of current state.  Epoch comparisons
are exact equalities, never lower bounds and never optional. -/
structure AuthState where
  capabilityRoot : Digest
  revocationRoot : Digest
  revoked : Finset RevocationKey
  issuerEpoch : IssuerId → Epoch
  policyEpoch : PolicyId → Epoch
  subjectKeyEpoch : SubjectId → Epoch

namespace Capability

/-- Pure semantic admission for one capability and one COMPLETE request. -/
structure Admissible {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) : Prop where
  holder : cap.holder.Covers request.subject
  scope : cap.scope.Covers request
  validFrom : cap.notBefore ≤ request.height
  validUntil : request.height ≤ cap.notAfter
  policyId : cap.policyId = request.policyId
  policyEpoch : cap.policyEpoch = request.policyEpoch
  policyCurrent : cap.policyEpoch = state.policyEpoch cap.policyId
  issuerCurrent : cap.issuerEpoch = state.issuerEpoch cap.issuer
  selfNotRevoked : RevocationKey.capability cap.id ∉ state.revoked
  ancestorNotRevoked :
    ∀ ancestor, ancestor ∈ cap.ancestors →
      RevocationKey.capability ancestor ∉ state.revoked
  channelNotRevoked :
    ∀ channel, channel ∈ cap.channels →
      RevocationKey.channel channel ∉ state.revoked

/-- A derived capability commits its exact parent/root lineage, retains the
issuer and both epochs, narrows scope/time, records the parent plus every prior
ancestor, and may only ADD revocation channels. -/
structure Attenuates {kind : ResourceKind} (child parent : Capability kind) : Prop where
  parentId : child.parent = some parent.id
  root : child.root = parent.root
  issuer : child.issuer = parent.issuer
  scopeNarrows : child.scope.Narrows parent.scope
  notBefore : parent.notBefore ≤ child.notBefore
  notAfter : child.notAfter ≤ parent.notAfter
  issuerEpoch : child.issuerEpoch = parent.issuerEpoch
  policyId : child.policyId = parent.policyId
  policyEpoch : child.policyEpoch = parent.policyEpoch
  ancestors : child.ancestors = insert parent.id parent.ancestors
  channels : parent.channels ⊆ child.channels

/-- The central attenuation law: anything inside the child scope was already
inside the parent scope. -/
theorem attenuation_scope_monotone {kind : ResourceKind}
    {child parent : Capability kind} {request : Request kind}
    (ha : child.Attenuates parent) (hc : child.scope.Covers request) :
    parent.scope.Covers request :=
  Scope.covers_of_narrows ha.scopeNarrows hc

/-- Full semantic monotonicity.  Holder delegation is intentionally explicit:
the caller must show that the parent holder covers the presented subject.  All
other authority facts follow from child admission and attenuation, including
the parent's revocation status because the parent id is a committed ancestor. -/
theorem attenuation_admits_subset {kind : ResourceKind}
    {child parent : Capability kind} {state : AuthState}
    {request : Request kind}
    (ha : child.Attenuates parent)
    (hc : child.Admissible state request)
    (parentHolder : parent.holder.Covers request.subject) :
    parent.Admissible state request := by
  refine
    { holder := parentHolder
      scope := attenuation_scope_monotone ha hc.scope
      validFrom := le_trans ha.notBefore hc.validFrom
      validUntil := le_trans hc.validUntil ha.notAfter
      policyId := ha.policyId.symm.trans hc.policyId
      policyEpoch := ha.policyEpoch.symm.trans hc.policyEpoch
      policyCurrent := ?_
      issuerCurrent := ?_
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · calc
      parent.policyEpoch = child.policyEpoch := ha.policyEpoch.symm
      _ = state.policyEpoch child.policyId := hc.policyCurrent
      _ = state.policyEpoch parent.policyId := congrArg state.policyEpoch ha.policyId
  · calc
      parent.issuerEpoch = child.issuerEpoch := ha.issuerEpoch.symm
      _ = state.issuerEpoch child.issuer := hc.issuerCurrent
      _ = state.issuerEpoch parent.issuer := congrArg state.issuerEpoch ha.issuer
  · apply hc.ancestorNotRevoked parent.id
    rw [ha.ancestors]
    exact Finset.mem_insert_self parent.id parent.ancestors
  · intro ancestor hmem
    apply hc.ancestorNotRevoked ancestor
    rw [ha.ancestors]
    exact Finset.mem_insert_of_mem hmem
  · intro channel hmem
    exact hc.channelNotRevoked channel (ha.channels hmem)

end Capability

/-! ## §4. Explicit verifier portals and request-indexed evidence. -/

/-- Executable cryptographic verifier boundary.  Every predicate returns a
Boolean and receives the exact statement it checks.  There is deliberately no
global proposition asserting that an arbitrary implementation is sound. -/
structure Portal where
  SignatureWitness : Type
  ProofWitness : Type
  CapabilityCommitmentWitness : Type
  MembershipWitness : Type
  IssuerWitness : Type
  NonRevocationWitness : Type
  PolicyWitness : Type
  verifySignature : {kind : ResourceKind} → Request kind → SignatureWitness → Bool
  verifyProof : {kind : ResourceKind} → Request kind → ProofWitness → Bool
  verifyCapabilityCommitment :
    {kind : ResourceKind} → Capability kind → Digest →
      CapabilityCommitmentWitness → Bool
  verifyMembership : Digest → Digest → MembershipWitness → Bool
  verifyIssuer : IssuerId → Epoch → Digest → IssuerWitness → Bool
  verifyNonRevocation : Digest → RevocationKey → NonRevocationWitness → Bool
  verifyPolicy : {kind : ResourceKind} → Request kind → PolicyWitness → Bool

/-- Evidence is indexed by the COMPLETE request.  Each constructor's verifier
therefore checks that exact value, not a separately supplied action/resource
claim.  Capability evidence additionally binds the complete cap, current root,
issuer epoch, and every exact revocation key used by semantic admission. -/
inductive Evidence (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type where
  | signature
      (witness : portal.SignatureWitness)
      (keyEpochExact : request.subjectKeyEpoch = state.subjectKeyEpoch request.subject)
      (verified : portal.verifySignature request witness = true) :
      Evidence portal state request
  | proof
      (witness : portal.ProofWitness)
      (verified : portal.verifyProof request witness = true) :
      Evidence portal state request
  | capability
      (cap : Capability kind)
      (commitment : Digest)
      (commitmentWitness : portal.CapabilityCommitmentWitness)
      (membershipWitness : portal.MembershipWitness)
      (issuerWitness : portal.IssuerWitness)
      (selfRevocationWitness : portal.NonRevocationWitness)
      (semantic : cap.Admissible state request)
      (commitmentVerified :
        portal.verifyCapabilityCommitment cap commitment commitmentWitness = true)
      (membershipVerified :
        portal.verifyMembership state.capabilityRoot commitment membershipWitness = true)
      (issuerVerified :
        portal.verifyIssuer cap.issuer cap.issuerEpoch commitment issuerWitness = true)
      (selfRevocationVerified :
        portal.verifyNonRevocation state.revocationRoot
          (.capability cap.id) selfRevocationWitness = true)
      (ancestorVerified :
        ∀ ancestor, ancestor ∈ cap.ancestors →
          ∃ witness : portal.NonRevocationWitness,
            portal.verifyNonRevocation state.revocationRoot
              (.capability ancestor) witness = true)
      (channelVerified :
        ∀ channel, channel ∈ cap.channels →
          ∃ witness : portal.NonRevocationWitness,
            portal.verifyNonRevocation state.revocationRoot
              (.channel channel) witness = true) :
      Evidence portal state request

/-- Policy selection is one common final gate for every evidence constructor;
no evidence mode may return before it. -/
structure Authorized (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) : Type where
  evidence : Evidence portal state request
  policyWitness : portal.PolicyWitness
  policyEpochExact : request.policyEpoch = state.policyEpoch request.policyId
  policyVerified : portal.verifyPolicy request policyWitness = true

/-! ## §5. Negative teeth. -/

/-- Target substitution fails semantically, in addition to producing the wrong
`Evidence` type, whenever the substituted target is outside the committed
scope. -/
theorem target_substitution_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (target : ResourceId kind) (outside : target ∉ cap.scope.targets) :
    ¬ cap.Admissible state (request.retarget target) := by
  intro admitted
  apply outside
  simpa [Request.retarget] using admitted.scope.target

/-- A caller cannot pre-load a capability with a future issuer epoch.  Exact
equality to current state rejects every strictly forward epoch. -/
theorem forward_issuer_epoch_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (forward : state.issuerEpoch cap.issuer < cap.issuerEpoch) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact (Nat.ne_of_lt forward) admitted.issuerCurrent.symm

/-- Revoking ANY committed ancestor kills the descendant capability. -/
theorem ancestor_revocation_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (ancestor : CapabilityId) (isAncestor : ancestor ∈ cap.ancestors)
    (isRevoked : RevocationKey.capability ancestor ∈ state.revoked) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact admitted.ancestorNotRevoked ancestor isAncestor isRevoked

/-- Revocation channels have the same committed, fail-closed semantics. -/
theorem channel_revocation_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (channel : ChannelId) (isChannel : channel ∈ cap.channels)
    (isRevoked : RevocationKey.channel channel ∈ state.revoked) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact admitted.channelNotRevoked channel isChannel isRevoked

/-- Stale policy epochs fail for the same exact-equality reason. -/
theorem stale_policy_epoch_rejected {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind)
    (stale : cap.policyEpoch ≠ state.policyEpoch cap.policyId) :
    ¬ cap.Admissible state request := by
  intro admitted
  exact stale admitted.policyCurrent

/-! ## §6. Concrete positive and negative poles. -/

def demoTarget : ResourceId .object := ⟨10⟩
def demoOtherTarget : ResourceId .object := ⟨11⟩

def demoRequest : Request .object where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  target := demoTarget
  verb := .mutateObject
  argsDigest := ⟨5⟩
  effectsDigest := ⟨6⟩
  nonce := 7
  height := 10
  preStateRoot := ⟨8⟩
  policyId := ⟨9⟩
  policyEpoch := 5
  cost := 4

def demoScope : Scope .object where
  targets := {demoTarget}
  verbs := {.mutateObject}
  maxCost := 8

def demoCapability : Capability .object where
  id := ⟨20⟩
  root := ⟨20⟩
  parent := none
  issuer := ⟨7⟩
  holder := .subject ⟨4⟩
  scope := demoScope
  notBefore := 3
  notAfter := 20
  issuerEpoch := 3
  policyId := ⟨9⟩
  policyEpoch := 5
  ancestors := ∅
  channels := {⟨21⟩}

def demoState : AuthState where
  capabilityRoot := ⟨30⟩
  revocationRoot := ⟨31⟩
  revoked := ∅
  issuerEpoch := fun _ => 3
  policyEpoch := fun _ => 5
  subjectKeyEpoch := fun _ => 2

theorem demoCapability_admissible :
    demoCapability.Admissible demoState demoRequest := by
  refine
    { holder := ?_
      scope := ?_
      validFrom := ?_
      validUntil := ?_
      policyId := ?_
      policyEpoch := ?_
      policyCurrent := ?_
      issuerCurrent := ?_
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · simp [Holder.Covers, demoCapability, demoRequest]
  · exact
      { target := by simp [demoCapability, demoScope, demoRequest, demoTarget]
        verb := by simp [demoCapability, demoScope, demoRequest]
        cost := by norm_num [demoCapability, demoScope, demoRequest] }
  · norm_num [demoCapability, demoRequest]
  · norm_num [demoCapability, demoRequest]
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [demoCapability, demoState]
  · intro ancestor hmem
    simp [demoCapability] at hmem
  · intro channel hmem
    simp [demoState]

/-- A concrete portal used only to show that the indexed API is inhabited.
Production code supplies real verifier functions; no theorem below infers
cryptographic soundness from this example. -/
def demoPortal : Portal where
  SignatureWitness := Unit
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Unit
  verifySignature := fun _ _ => true
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyMembership := fun _ _ _ => true
  verifyIssuer := fun _ _ _ _ => true
  verifyNonRevocation := fun _ _ _ => true
  verifyPolicy := fun _ _ => true

def demoEvidence : Evidence demoPortal demoState demoRequest :=
  .capability demoCapability ⟨32⟩ () () () () demoCapability_admissible
    rfl rfl rfl rfl
    (by
      intro ancestor hmem
      simp [demoCapability] at hmem)
    (by
      intro channel _
      exact ⟨(), rfl⟩)

/-- Positive tooth: a subject-bound, current-epoch, live, unrevoked capability
with explicit commitment/membership/issuer/non-revocation checks authorizes. -/
def demo_authorized_positive : Authorized demoPortal demoState demoRequest where
  evidence := demoEvidence
  policyWitness := ()
  policyEpochExact := rfl
  policyVerified := rfl

/-- Negative tooth: the same capability cannot authorize a different target. -/
theorem demo_target_substitution_rejected :
    ¬ demoCapability.Admissible demoState
      (demoRequest.retarget demoOtherTarget) := by
  apply target_substitution_rejected
  simp [demoCapability, demoScope, demoOtherTarget, demoTarget]

def demoForwardEpochCapability : Capability .object :=
  { demoCapability with issuerEpoch := 4 }

/-- Negative tooth: an epoch from the future is rejected, rather than surviving
future revocation bumps. -/
theorem demo_forward_epoch_rejected :
    ¬ demoForwardEpochCapability.Admissible demoState demoRequest := by
  apply forward_issuer_epoch_rejected
  norm_num [demoForwardEpochCapability, demoCapability, demoState]

def demoAncestorCapability : Capability .object :=
  { demoCapability with ancestors := {⟨99⟩} }

def demoAncestorRevokedState : AuthState :=
  { demoState with revoked := {.capability ⟨99⟩} }

/-- Negative tooth: revoking a committed ancestor rejects the descendant. -/
theorem demo_ancestor_revocation_rejected :
    ¬ demoAncestorCapability.Admissible demoAncestorRevokedState demoRequest := by
  apply ancestor_revocation_rejected
      (ancestor := (⟨99⟩ : CapabilityId))
  · simp [demoAncestorCapability]
  · simp [demoAncestorRevokedState]

end Minidregg.Theory.TypedAuthorization
