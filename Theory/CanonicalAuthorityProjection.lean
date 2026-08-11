/-
# Theory.CanonicalAuthorityProjection -- derive the revocation universe

`CredentialAuthorityState.authState` needs a finite `ProjectionUniverse` so its
revoked set is executable.  That universe must not be a caller-authored list:
omitting a live revocation key would make the projected authorization state lie
about the canonical authority cell.

The repaired `CellState.FieldStore` is a dependent finite map, so the required
universe is already present in the cell itself.  This module extracts exactly
the revocation addresses in its finite support and proves that every true
revocation is projected.  It adds no signature, policy, or persistence claim.
-/
import Theory.CredentialAuthorityState

namespace Minidregg.Theory.CanonicalAuthorityProjection

open CellState
open CredentialAuthorityState
open TypedAuthorization

set_option autoImplicit false

deriving instance DecidableEq for StoredCapability

instance authorityValueDecidableEq (field : AuthorityField) :
    DecidableEq (AuthorityField.Value field) := by
  cases field <;> simp [AuthorityField.Value] <;> infer_instance

instance authorityOptionNeZero (field : CredentialAuthorityState.schema.Field)
    (value : Option (CredentialAuthorityState.schema.FieldType field)) :
    Decidable (value ≠ 0) := by
  change Decidable (value ≠ none)
  exact inferInstance

/-! ## Canonical finite extraction -/

/-- Every supported revocation address contributes its exact typed key; other
authority planes contribute nothing. -/
def keysAtField : AuthorityField → Finset RevocationKey
  | .revoked key => {key}
  | _ => ∅

/-- The sole canonical revocation universe of one authority cell. -/
def revocationKeys {M : Materializer} (pre : Cell M) : Finset RevocationKey :=
  pre.logical.fields.support.biUnion keysAtField

/-- Package the derived finite set for the existing authorization projection.
No caller supplies or prunes this list. -/
def projection {M : Materializer} (pre : Cell M) : ProjectionUniverse where
  revocationKeys := revocationKeys pre

@[simp] theorem mem_revocationKeys_iff {M : Materializer} (pre : Cell M)
    (key : RevocationKey) :
    key ∈ revocationKeys pre ↔
      AuthorityField.revoked key ∈ pre.logical.fields.support := by
  constructor
  · rw [revocationKeys, Finset.mem_biUnion]
    rintro ⟨field, supported, contributes⟩
    cases field <;> simp [keysAtField] at contributes
    subst key
    exact supported
  · intro supported
    rw [revocationKeys, Finset.mem_biUnion]
    exact ⟨.revoked key, supported, by simp [keysAtField]⟩

/-- A true sparse revocation read is necessarily represented in finite support.
This is the load-bearing completeness direction. -/
theorem supported_of_isRevoked {M : Materializer} (pre : Cell M)
    (key : RevocationKey) (revoked : isRevoked pre key = true) :
    AuthorityField.revoked key ∈ pre.logical.fields.support := by
  have present : pre.logical.fields (.revoked key) ≠ none := by
    intro absent
    simp [isRevoked, absent] at revoked
  exact DFinsupp.mem_support_iff.mpr present

/-- No true revocation can disappear from the derived projection universe. -/
theorem complete {M : Materializer} (pre : Cell M) (key : RevocationKey)
    (revoked : isRevoked pre key = true) :
    key ∈ (projection pre).revocationKeys := by
  change key ∈ revocationKeys pre
  rw [mem_revocationKeys_iff]
  exact supported_of_isRevoked pre key revoked

/-- Under the canonical projection, membership in the authorization revocation
set is exactly the canonical Boolean read--not Boolean read plus a caller list.
-/
@[simp] theorem mem_authState_revoked_iff {M : Materializer} (pre : Cell M)
    (key : RevocationKey) :
    key ∈ (authState (projection pre) pre).revoked ↔ isRevoked pre key = true := by
  rw [CredentialAuthorityState.mem_authState_revoked_iff]
  constructor
  · exact And.right
  · intro revoked
    exact ⟨complete pre key revoked, revoked⟩

/-- A key absent from finite support reads false and cannot enter the projected
revocation set. -/
theorem absent_is_not_revoked {M : Materializer} (pre : Cell M)
    (key : RevocationKey)
    (absent : AuthorityField.revoked key ∉ pre.logical.fields.support) :
    isRevoked pre key = false ∧
      key ∉ (authState (projection pre) pre).revoked := by
  have readAbsent : pre.logical.fields (.revoked key) = none := by
    exact DFinsupp.notMem_support_iff.mp absent
  constructor
  · simp [isRevoked, readAbsent]
  · rw [mem_authState_revoked_iff]
    simp [isRevoked, readAbsent]

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.CanonicalAuthorityProjection.mem_authState_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_authState_revoked_iff
/-- info: 'Minidregg.Theory.CanonicalAuthorityProjection.absent_is_not_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_is_not_revoked

end Minidregg.Theory.CanonicalAuthorityProjection
