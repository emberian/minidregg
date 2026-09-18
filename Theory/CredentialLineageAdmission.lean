/-
# Theory.CredentialLineageAdmission — executable source lineage checks

Every decision below reflects the existing semantic relation. In particular,
holder narrowing is not replaced by a scope-only comparison: a subject-owned
parent cannot silently become another subject's authority.
-/
import Theory.CredentialAuthorityState

namespace Minidregg.Theory.CredentialLineageAdmission

open TypedAuthorization
open CredentialAuthorityState
open CredentialAuthorityFamily

set_option autoImplicit false

/-- Capability identifiers share one revocation namespace. Freshness therefore
quantifies over every storage kind, rather than only the new capability's kind. -/
def CapabilityIdFresh {M : Materializer} (pre : Cell M) (identifier : CapabilityId) : Prop :=
  ∀ kind, readCapability pre kind identifier = none

def capabilityIdFreshCheck {M : Materializer} (pre : Cell M)
    (identifier : CapabilityId) : Bool :=
  (readCapability pre .object identifier).isNone &&
    ((readCapability pre .account identifier).isNone &&
      (readCapability pre .program identifier).isNone)

theorem capabilityIdFreshCheck_iff {M : Materializer} (pre : Cell M)
    (identifier : CapabilityId) :
    capabilityIdFreshCheck pre identifier = true ↔ CapabilityIdFresh pre identifier := by
  simp only [capabilityIdFreshCheck, Bool.and_eq_true, Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨object, account, program⟩ kind
    cases kind with
    | object => exact object
    | account => exact account
    | program => exact program
  · intro fresh
    exact ⟨fresh .object, fresh .account, fresh .program⟩

instance capabilityIdFreshDecidable {M : Materializer} (pre : Cell M)
    (identifier : CapabilityId) : Decidable (CapabilityIdFresh pre identifier) :=
  decidable_of_iff (capabilityIdFreshCheck pre identifier = true)
    (capabilityIdFreshCheck_iff pre identifier)

theorem existing_capability_not_fresh {M : Materializer} (pre : Cell M)
    (identifier : CapabilityId) {kind : ResourceKind} (stored : StoredCapability kind)
    (present : readCapability pre kind identifier = some stored) :
    ¬CapabilityIdFresh pre identifier := by
  intro fresh
  have absent := fresh kind
  rw [present] at absent
  contradiction

theorem scopeNarrows_iff_components {kind : ResourceKind}
    (child parent : Scope kind) :
    child.Narrows parent ↔ child.targets ⊆ parent.targets ∧
      child.verbs ⊆ parent.verbs ∧ child.maxCost ≤ parent.maxCost := by
  constructor
  · intro narrowed
    exact ⟨narrowed.targets, narrowed.verbs, narrowed.maxCost⟩
  · rintro ⟨targets, verbs, cost⟩
    exact ⟨targets, verbs, cost⟩

instance scopeNarrowsDecidable {kind : ResourceKind} (child parent : Scope kind) :
    Decidable (child.Narrows parent) :=
  decidable_of_iff _ (scopeNarrows_iff_components child parent).symm

def holderNarrowsCheck (child parent : Holder) : Bool :=
  match child, parent with
  | _, .bearer => true
  | .bearer, .subject _ => false
  | .subject childSubject, .subject parentSubject => decide (childSubject = parentSubject)

theorem holderNarrowsCheck_iff (child parent : Holder) :
    holderNarrowsCheck child parent = true ↔ child.Narrows parent := by
  cases child with
  | bearer =>
      cases parent with
      | bearer =>
          exact ⟨fun _ => Holder.narrows_refl _, fun _ => rfl⟩
      | subject subject =>
          constructor
          · intro accepted
            contradiction
          · intro narrowed
            exact False.elim (Holder.bearer_not_narrows_subject subject narrowed)
  | subject childSubject =>
      cases parent with
      | bearer =>
          exact ⟨fun _ => Holder.subject_narrows_bearer _, fun _ => rfl⟩
      | subject parentSubject =>
          constructor
          · intro accepted
            have equal : childSubject = parentSubject := of_decide_eq_true accepted
            subst parentSubject
            exact Holder.narrows_refl _
          · intro narrowed
            have equal : parentSubject = childSubject := narrowed childSubject rfl
            exact decide_eq_true equal.symm

instance holderNarrowsDecidable (child parent : Holder) :
    Decidable (child.Narrows parent) :=
  decidable_of_iff (holderNarrowsCheck child parent = true)
    (holderNarrowsCheck_iff child parent)

theorem attenuates_iff_components {kind : ResourceKind}
    (child parent : Capability kind) :
    child.Attenuates parent ↔
      child.parent = some parent.id ∧ child.root = parent.root ∧
      child.issuer = parent.issuer ∧ child.scope.Narrows parent.scope ∧
      parent.notBefore ≤ child.notBefore ∧ child.notAfter ≤ parent.notAfter ∧
      child.issuerEpoch = parent.issuerEpoch ∧ child.policyId = parent.policyId ∧
      child.policyEpoch = parent.policyEpoch ∧
      child.ancestors = insert parent.id parent.ancestors ∧
      parent.channels ⊆ child.channels := by
  constructor
  · intro edge
    exact ⟨edge.parentId, edge.root, edge.issuer, edge.scopeNarrows,
      edge.notBefore, edge.notAfter, edge.issuerEpoch, edge.policyId,
      edge.policyEpoch, edge.ancestors, edge.channels⟩
  · rintro ⟨parentId, root, issuer, scope, validFrom, validUntil,
      issuerEpoch, policyId, policyEpoch, ancestors, channels⟩
    exact ⟨parentId, root, issuer, scope, validFrom, validUntil,
      issuerEpoch, policyId, policyEpoch, ancestors, channels⟩

instance attenuatesDecidable {kind : ResourceKind} (child parent : Capability kind) :
    Decidable (child.Attenuates parent) :=
  decidable_of_iff _ (attenuates_iff_components child parent).symm

theorem strictAttenuates_iff_components {kind : ResourceKind}
    (child parent : Capability kind) :
    child.StrictAttenuates parent ↔ child.Attenuates parent ∧
      child.holder.Narrows parent.holder := by
  constructor
  · intro edge
    exact ⟨edge.payload, edge.holder⟩
  · rintro ⟨payload, holder⟩
    exact ⟨payload, holder⟩

instance strictAttenuatesDecidable {kind : ResourceKind}
    (child parent : Capability kind) : Decidable (child.StrictAttenuates parent) :=
  decidable_of_iff _ (strictAttenuates_iff_components child parent).symm

def strictAttenuatesCheck {kind : ResourceKind} (child parent : Capability kind) : Bool :=
  decide (child.StrictAttenuates parent)

theorem strictAttenuatesCheck_iff {kind : ResourceKind}
    (child parent : Capability kind) :
    strictAttenuatesCheck child parent = true ↔ child.StrictAttenuates parent := by
  simp [strictAttenuatesCheck]

/-- Reuse the existing request-scope decision, rather than inventing a
second delegation-specific notion of which operations a parent permits. -/
instance scopeCoversDecidable {kind : ResourceKind} (scope : Scope kind)
    (request : Request kind) : Decidable (scope.Covers request) :=
  decidable_of_iff (AuthorizationDeclaration.scopeCoversCheck scope request = true)
    (AuthorizationDeclaration.scopeCoversCheck_eq_true_iff scope request)

theorem delegationShape_iff_components {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind) :
    DelegationShape request child parent ↔
      child.Attenuates parent ∧ parent.holder = .subject request.subject ∧
      child.holder ≠ .bearer ∧ request.verb = delegateVerb kind ∧
      child.scope.targets = {request.target} ∧ parent.scope.Covers request ∧
      parent.notBefore ≤ request.height ∧ request.height ≤ parent.notAfter ∧
      parent.policyId = request.policyId ∧ parent.policyEpoch = request.policyEpoch := by
  constructor
  · intro shape
    exact ⟨shape.payload, shape.grantor, shape.recipient, shape.delegate,
      shape.target, shape.parentScope, shape.validFrom, shape.validUntil,
      shape.policyId, shape.policyEpoch⟩
  · rintro ⟨payload, grantor, recipient, delegate, target, scope,
      validFrom, validUntil, policyId, policyEpoch⟩
    exact ⟨payload, grantor, recipient, delegate, target, scope,
      validFrom, validUntil, policyId, policyEpoch⟩

instance delegationShapeDecidable {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind) :
    Decidable (DelegationShape request child parent) :=
  decidable_of_iff _ (delegationShape_iff_components request child parent).symm

def delegationShapeCheck {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind) : Bool :=
  decide (DelegationShape request child parent)

theorem delegationShapeCheck_iff {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind) :
    delegationShapeCheck request child parent = true ↔ DelegationShape request child parent := by
  simp [delegationShapeCheck]

/-- A delegated edge never interprets ordinary mutation permission as the
right to give authority to another subject. -/
theorem delegationShapeCheck_refuses_missing_delegate {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind)
    (missing : delegateVerb kind ∉ parent.scope.verbs) :
    delegationShapeCheck request child parent = false := by
  cases checked : delegationShapeCheck request child parent with
  | false => rfl
  | true =>
      have shape := (delegationShapeCheck_iff request child parent).mp checked
      exact False.elim (missing (shape.delegate ▸ shape.parentScope.verb))

theorem delegationShapeCheck_refuses_bearer {kind : ResourceKind}
    (request : Request kind) (child parent : Capability kind)
    (bearer : child.holder = .bearer) :
    delegationShapeCheck request child parent = false := by
  cases checked : delegationShapeCheck request child parent with
  | false => rfl
  | true =>
      exact False.elim (((delegationShapeCheck_iff request child parent).mp checked).recipient bearer)

def parentLinkCheck {kind : ResourceKind}
    (child : Capability kind) (link : ParentLink kind) : Bool :=
  match link.origin with
  | .strict => strictAttenuatesCheck child link.parent
  | .delegated request => delegationShapeCheck request child link.parent

/-- Every stored parent is opened from the same canonical pre-state, with
exactly the remaining suffix, including all explicit origin records. -/
def lineageAnchoredAux {M : Materializer} (pre : Cell M) {kind : ResourceKind} :
    List (ParentLink kind) → Prop
  | [] => True
  | link :: tail =>
      readCapability pre kind link.parent.id = some ⟨link.parent, tail⟩ ∧
        lineageAnchoredAux pre tail

def LineageAnchored {M : Materializer} (pre : Cell M) {kind : ResourceKind}
    (stored : StoredCapability kind) : Prop := lineageAnchoredAux pre stored.ancestry

/-- Extending a stored ancestry must open the exact parent record, including
its full remaining suffix. The origin marker does not weaken this obligation. -/
theorem LineageAnchored.cons {M : Materializer} {pre : Cell M}
    {kind : ResourceKind} (child parent : Capability kind)
    (tail : List (ParentLink kind)) (origin : LineageOrigin kind)
    (present : readCapability pre kind parent.id = some ⟨parent, tail⟩)
    (anchored : LineageAnchored pre ⟨parent, tail⟩) :
    LineageAnchored pre ⟨child, ⟨parent, origin⟩ :: tail⟩ :=
  ⟨present, anchored⟩

theorem LineageAnchored.parent_exact {M : Materializer} {pre : Cell M}
    {kind : ResourceKind} {child parent : Capability kind}
    {tail : List (ParentLink kind)} {origin : LineageOrigin kind}
    (anchored : LineageAnchored pre ⟨child, ⟨parent, origin⟩ :: tail⟩) :
    readCapability pre kind parent.id = some ⟨parent, tail⟩ := anchored.1

/-- Inserting a fresh capability may change an absent slot. It preserves a
stored lineage when every previously present capability remains exact. This
is the premise a concrete source patch must prove, rather than a blanket
whole-state equality requirement. -/
theorem LineageAnchored.of_present_reads_preserved {M N : Materializer}
    {pre : Cell M} {post : Cell N} {kind : ResourceKind}
    {stored : StoredCapability kind} (anchored : LineageAnchored pre stored)
    (preserved : ∀ (readKind : ResourceKind) (identifier : CapabilityId)
      (record : StoredCapability readKind),
      readCapability pre readKind identifier = some record →
      readCapability post readKind identifier = some record) :
    LineageAnchored post stored := by
  rcases stored with ⟨head, ancestry⟩
  change lineageAnchoredAux pre ancestry at anchored
  change lineageAnchoredAux post ancestry
  induction ancestry with
  | nil => trivial
  | cons link tail induction =>
      exact ⟨preserved kind link.parent.id ⟨link.parent, tail⟩ anchored.1,
        induction anchored.2⟩

/-- The stored origin selects the exact semantic edge relation. No heuristic
infers a delegated edge from a changed holder, and no historical signature is
rechecked against today's grantor key. Creation authorization is retained by
the accepted source transition; this pure check validates its stored shape. -/
def lineageCheckAux {kind : ResourceKind} :
    List (ParentLink kind) → Capability kind → Bool
  | [], head => decide (head.parent = none ∧ head.root = head.id ∧ head.ancestors = ∅)
  | link :: tail, head => parentLinkCheck head link && lineageCheckAux tail link.parent

theorem lineageCheckAux_iff {kind : ResourceKind}
    (ancestry : List (ParentLink kind)) (head : Capability kind) :
    lineageCheckAux ancestry head = true ↔ LineageValid ⟨head, ancestry⟩ := by
  induction ancestry generalizing head with
  | nil =>
      simp only [lineageCheckAux, decide_eq_true_eq]
      constructor
      · rintro ⟨parent, root, ancestors⟩
        exact .root head parent root ancestors
      · intro valid
        cases valid with
        | root _ parent root ancestors => exact ⟨parent, root, ancestors⟩
  | cons link tail induction =>
      rcases link with ⟨parent, origin⟩
      cases origin with
      | strict =>
          rw [lineageCheckAux, parentLinkCheck, Bool.and_eq_true,
            strictAttenuatesCheck_iff, induction]
          constructor
          · rintro ⟨edge, valid⟩
            exact .attenuate head parent tail valid edge
          · intro valid
            cases valid with
            | attenuate _ _ _ parentValid edge => exact ⟨edge, parentValid⟩
      | delegated request =>
          rw [lineageCheckAux, parentLinkCheck, Bool.and_eq_true,
            delegationShapeCheck_iff, induction]
          constructor
          · rintro ⟨shape, valid⟩
            exact .delegate head parent tail request valid shape
          · intro valid
            cases valid with
            | delegate _ _ _ _ parentValid shape => exact ⟨shape, parentValid⟩

def storedEqualCheck {kind : ResourceKind}
    (left right : StoredCapability kind) : Bool :=
  decide (left.head = right.head ∧ left.ancestry = right.ancestry)

theorem storedEqualCheck_iff {kind : ResourceKind}
    (left right : StoredCapability kind) :
    storedEqualCheck left right = true ↔ left = right := by
  cases left
  cases right
  simp [storedEqualCheck]

def lineageAnchoredCheck {M : Materializer} (pre : Cell M) {kind : ResourceKind} :
    List (ParentLink kind) → Bool
  | [] => true
  | link :: tail =>
      match readCapability pre kind link.parent.id with
      | none => false
      | some stored => storedEqualCheck stored ⟨link.parent, tail⟩ && lineageAnchoredCheck pre tail

theorem lineageAnchoredCheck_iff {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (ancestry : List (ParentLink kind)) :
    lineageAnchoredCheck pre ancestry = true ↔ lineageAnchoredAux pre ancestry := by
  induction ancestry with
  | nil => simp [lineageAnchoredCheck, lineageAnchoredAux]
  | cons link tail induction =>
      cases selected : readCapability pre kind link.parent.id with
      | none => simp [lineageAnchoredCheck, lineageAnchoredAux, selected]
      | some stored =>
          simp [lineageAnchoredCheck, lineageAnchoredAux, selected,
            storedEqualCheck_iff, induction]

/-- The same mandatory source gate now handles explicit strict and delegated
origins. Invocation cannot replace it with a head-only check. -/
def storedLineageCheck {M : Materializer} (pre : Cell M) {kind : ResourceKind}
    (stored : StoredCapability kind) : Bool :=
  lineageCheckAux stored.ancestry stored.head && lineageAnchoredCheck pre stored.ancestry

theorem storedLineageCheck_iff {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (stored : StoredCapability kind) :
    storedLineageCheck pre stored = true ↔ LineageValid stored ∧ LineageAnchored pre stored := by
  cases stored
  simp only [storedLineageCheck, Bool.and_eq_true, lineageCheckAux_iff,
    lineageAnchoredCheck_iff, LineageAnchored]

theorem storedLineageCheck_refuses_invalid {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (stored : StoredCapability kind) (invalid : ¬LineageValid stored) :
    storedLineageCheck pre stored = false := by
  cases checked : storedLineageCheck pre stored with
  | false => rfl
  | true => exact False.elim (invalid ((storedLineageCheck_iff pre stored).mp checked).1)

theorem storedLineageCheck_refuses_unanchored {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (stored : StoredCapability kind) (missing : ¬LineageAnchored pre stored) :
    storedLineageCheck pre stored = false := by
  cases checked : storedLineageCheck pre stored with
  | false => rfl
  | true => exact False.elim (missing ((storedLineageCheck_iff pre stored).mp checked).2)

/-- A well-shaped copy of a parent is insufficient when either the parent
payload or its remaining origin suffix disagrees with canonical storage. -/
theorem storedLineageCheck_refuses_parent_substitution {M : Materializer}
    (pre : Cell M) {kind : ResourceKind} (child parent : Capability kind)
    (tail : List (ParentLink kind)) (origin : LineageOrigin kind)
    (different : readCapability pre kind parent.id ≠ some ⟨parent, tail⟩) :
    storedLineageCheck pre ⟨child, ⟨parent, origin⟩ :: tail⟩ = false :=
  storedLineageCheck_refuses_unanchored pre _
    (fun anchored => different anchored.parent_exact)

/-- Historical lineage reads only canonical capability records. Current
subject keys and key epochs belong to invocation authentication, not to
reauthentication of every old grantor at descendant use time. -/
theorem lineageAnchoredCheck_congr {M N : Materializer}
    (left : Cell M) (right : Cell N)
    (same : ∀ kind identifier, readCapability left kind identifier =
      readCapability right kind identifier)
    {kind : ResourceKind} (ancestry : List (ParentLink kind)) :
    lineageAnchoredCheck left ancestry = lineageAnchoredCheck right ancestry := by
  induction ancestry with
  | nil => rfl
  | cons link tail induction =>
      simp only [lineageAnchoredCheck]
      rw [same kind link.parent.id]
      cases readCapability right kind link.parent.id <;> simp [induction]

theorem storedLineageCheck_congr {M N : Materializer}
    (left : Cell M) (right : Cell N)
    (same : ∀ kind identifier, readCapability left kind identifier =
      readCapability right kind identifier)
    {kind : ResourceKind} (stored : StoredCapability kind) :
    storedLineageCheck left stored = storedLineageCheck right stored := by
  simp only [storedLineageCheck, lineageAnchoredCheck_congr left right same]

end Minidregg.Theory.CredentialLineageAdmission
