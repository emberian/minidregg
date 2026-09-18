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

/-- Every stored parent is opened from the same canonical pre-state, with
exactly the remaining suffix. A well-shaped invented parent is insufficient. -/
def lineageAnchoredAux {M : Materializer} (pre : Cell M) {kind : ResourceKind} :
    List (Capability kind) → Prop
  | [] => True
  | parent :: tail =>
      readCapability pre kind parent.id = some ⟨parent, tail⟩ ∧ lineageAnchoredAux pre tail

def LineageAnchored {M : Materializer} (pre : Cell M) {kind : ResourceKind}
    (stored : StoredCapability kind) : Prop := lineageAnchoredAux pre stored.ancestry

/-- Current strict lineage is reflected completely, including terminal root
markers and every holder-aware attenuation edge. Mixed subject delegation
requires the separate explicit origin representation; it is not guessed here. -/
def strictLineageCheckAux {kind : ResourceKind} :
    List (Capability kind) → Capability kind → Bool
  | [], head => decide (head.parent = none ∧ head.root = head.id ∧ head.ancestors = ∅)
  | parent :: tail, head =>
      strictAttenuatesCheck head parent && strictLineageCheckAux tail parent

theorem strictLineageCheckAux_iff {kind : ResourceKind}
    (ancestry : List (Capability kind)) (head : Capability kind) :
    strictLineageCheckAux ancestry head = true ↔ LineageValid ⟨head, ancestry⟩ := by
  induction ancestry generalizing head with
  | nil =>
      simp only [strictLineageCheckAux, decide_eq_true_eq]
      constructor
      · rintro ⟨parent, root, ancestors⟩
        exact .root head parent root ancestors
      · intro valid
        cases valid with
        | root _ parent root ancestors => exact ⟨parent, root, ancestors⟩
  | cons parent tail induction =>
      rw [strictLineageCheckAux, Bool.and_eq_true, strictAttenuatesCheck_iff, induction]
      constructor
      · rintro ⟨edge, valid⟩
        exact .attenuate head parent tail valid edge
      · intro valid
        cases valid with
        | attenuate _ _ _ parentValid edge => exact ⟨edge, parentValid⟩

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
    List (Capability kind) → Bool
  | [] => true
  | parent :: tail =>
      match readCapability pre kind parent.id with
      | none => false
      | some stored => storedEqualCheck stored ⟨parent, tail⟩ && lineageAnchoredCheck pre tail

theorem lineageAnchoredCheck_iff {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (ancestry : List (Capability kind)) :
    lineageAnchoredCheck pre ancestry = true ↔ lineageAnchoredAux pre ancestry := by
  induction ancestry with
  | nil => simp [lineageAnchoredCheck, lineageAnchoredAux]
  | cons parent tail induction =>
      cases selected : readCapability pre kind parent.id with
      | none => simp [lineageAnchoredCheck, lineageAnchoredAux, selected]
      | some stored =>
          simp [lineageAnchoredCheck, lineageAnchoredAux, selected,
            storedEqualCheck_iff, induction]

/-- The single source lineage gate used at both creation and invocation. -/
def storedLineageCheck {M : Materializer} (pre : Cell M) {kind : ResourceKind}
    (stored : StoredCapability kind) : Bool :=
  strictLineageCheckAux stored.ancestry stored.head &&
    lineageAnchoredCheck pre stored.ancestry

theorem storedLineageCheck_iff {M : Materializer} (pre : Cell M)
    {kind : ResourceKind} (stored : StoredCapability kind) :
    storedLineageCheck pre stored = true ↔ LineageValid stored ∧ LineageAnchored pre stored := by
  cases stored
  simp only [storedLineageCheck, Bool.and_eq_true, strictLineageCheckAux_iff,
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

end Minidregg.Theory.CredentialLineageAdmission
