/-
# Theory.CredentialAuthorityState -- canonical sparse authority state

The authorization projection is not an independently supplied cache.  This
module places capability records, issuer/policy/subject epochs, revocations,
and single-use operation nullifiers in one typed `CellState`.  A finite
deployment universe turns the sparse revocation plane into the exact `Finset`
required by `TypedAuthorization.AuthState`; both authenticated-set roots are
the root of the same canonical materialization.

Capability lineage is retained as first-order capability data.  Its Lean
validity predicate checks every adjacent strict-attenuation edge, including
holder narrowing, rather than trusting parent identifiers.

`CellState.LogicalState` stores a finite dependent map.  Absent epoch and
membership entries are read through explicit zero/false defaults below;
capability absence remains the primitive optional lookup result.  Thus the
word "sparse" here is representation, not merely vocabulary.
-/
import Theory.AcceptedCellEffect
import Theory.CredentialAuthorityFamily

namespace Minidregg.Theory.CredentialAuthorityState

open IndexedProgram
open TypedAuthorization
open CredentialAuthorityFamily

/-! ## Canonical typed sparse addresses -/

/-- One address space for all authorization-relevant state.  Optional
capability slots and Boolean set-membership cells give the sparse planes their
absent value without adding side tables to the cell record. -/
inductive AuthorityField where
  | capability (kind : ResourceKind) (id : CapabilityId)
  | issuerEpoch (issuer : IssuerId)
  | policyEpoch (policy : PolicyId)
  | subjectKeyEpoch (subject : SubjectId)
  | revoked (key : RevocationKey)
  | nullifier (id : Nat)
  deriving DecidableEq, Repr

/-- A stored lineage is data: the head capability followed by its parent,
grandparent, and so on.  Validity is a separate Lean proposition below. -/
structure StoredCapability (kind : ResourceKind) where
  head : Capability kind
  ancestry : List (Capability kind)

/-- Dependent values prevent a capability for one resource kind from being
written into another kind's slot. -/
def AuthorityField.Value : AuthorityField → Type
  | .capability kind _ => StoredCapability kind
  | .issuerEpoch _ => Epoch
  | .policyEpoch _ => Epoch
  | .subjectKeyEpoch _ => Epoch
  | .revoked _ => Bool
  | .nullifier _ => Bool

/-- The authority schema has no separate resource lane: the typed sparse field
address already distinguishes every state plane. -/
def schema : CellState.Schema where
  Field := AuthorityField
  FieldType := AuthorityField.Value
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := by
  change DecidableEq AuthorityField
  infer_instance

instance : DecidableEq schema.Resource := by
  change DecidableEq Empty
  infer_instance

abbrev Materializer := CellState.Materializer schema Digest
abbrev Cell (M : Materializer) := CellState.Materialized M

def readCapability {M : Materializer} (pre : Cell M)
    (kind : ResourceKind) (id : CapabilityId) : Option (StoredCapability kind) :=
  pre.logical.fields (.capability kind id)

def issuerEpochAt {M : Materializer} (pre : Cell M) (issuer : IssuerId) : Epoch :=
  (pre.logical.fields (.issuerEpoch issuer)).getD (show Epoch from 0)

def policyEpochAt {M : Materializer} (pre : Cell M) (policy : PolicyId) : Epoch :=
  (pre.logical.fields (.policyEpoch policy)).getD (show Epoch from 0)

def subjectKeyEpochAt {M : Materializer} (pre : Cell M)
    (subject : SubjectId) : Epoch :=
  (pre.logical.fields (.subjectKeyEpoch subject)).getD (show Epoch from 0)

def isRevoked {M : Materializer} (pre : Cell M) (key : RevocationKey) : Bool :=
  (pre.logical.fields (.revoked key)).getD false

def isNullified {M : Materializer} (pre : Cell M) (id : Nat) : Bool :=
  (pre.logical.fields (.nullifier id)).getD false

/-! ## Proof-relevant validity of stored lineage -/

/-- Every stored parent is the actual next capability and every edge is strict
attenuation.  The terminal record is a genuine root. -/
inductive LineageValid {kind : ResourceKind} : StoredCapability kind → Prop
  | root (cap : Capability kind)
      (parentNone : cap.parent = none)
      (rootSelf : cap.root = cap.id)
      (ancestorsEmpty : cap.ancestors = ∅) :
      LineageValid ⟨cap, []⟩
  | attenuate (child parent : Capability kind)
      (tail : List (Capability kind))
      (parentValid : LineageValid ⟨parent, tail⟩)
      (edge : child.StrictAttenuates parent) :
      LineageValid ⟨child, parent :: tail⟩

theorem LineageValid.root_admissible {kind : ResourceKind}
    {stored : StoredCapability kind} {state : AuthState}
    {request : Request kind} (valid : LineageValid stored)
    (admitted : stored.head.Admissible state request) :
    ∃ root : Capability kind,
      root.parent = none ∧ root.root = root.id ∧
      root.Admissible state request := by
  induction valid with
  | root cap parentNone rootSelf ancestorsEmpty =>
      exact ⟨cap, parentNone, rootSelf, admitted⟩
  | attenuate child parent tail parentValid edge ih =>
      exact ih (Capability.strict_attenuation_admits_subset edge admitted)

/-! ## Exact projection into the common authorization judgment -/

/-- A deployment declares the finite revocation keys whose sparse cells are
part of this authority domain.  Issuer/policy/subject epoch reads remain total
typed addresses and require no enumerable universe. -/
structure ProjectionUniverse where
  revocationKeys : Finset RevocationKey

/-- The sole `AuthState` projection.  Capability and revocation witnesses use
the SAME canonical cell root; revoked membership and every epoch are read from
that exact cell. -/
def authState {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) : AuthState where
  capabilityRoot := pre.root
  revocationRoot := pre.root
  revoked := domain.revocationKeys.filter fun key => isRevoked pre key
  issuerEpoch := issuerEpochAt pre
  policyEpoch := policyEpochAt pre
  subjectKeyEpoch := subjectKeyEpochAt pre

@[simp] theorem authState_capabilityRoot {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) :
    (authState domain pre).capabilityRoot = pre.root := rfl

@[simp] theorem authState_revocationRoot {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) :
    (authState domain pre).revocationRoot = pre.root := rfl

@[simp] theorem authState_issuerEpoch {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (issuer : IssuerId) :
    (authState domain pre).issuerEpoch issuer = issuerEpochAt pre issuer := rfl

@[simp] theorem authState_policyEpoch {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (policy : PolicyId) :
    (authState domain pre).policyEpoch policy = policyEpochAt pre policy := rfl

@[simp] theorem authState_subjectKeyEpoch {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (subject : SubjectId) :
    (authState domain pre).subjectKeyEpoch subject = subjectKeyEpochAt pre subject := rfl

theorem mem_authState_revoked_iff {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (key : RevocationKey) :
    key ∈ (authState domain pre).revoked ↔
      key ∈ domain.revocationKeys ∧ isRevoked pre key = true := by
  simp [authState]

/-- Outside the declared sparse revocation universe there is no projected
revocation member, even if some unrelated host data mentions the key. -/
theorem not_mem_authState_revoked_of_outside {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (key : RevocationKey)
    (outside : key ∉ domain.revocationKeys) :
    key ∉ (authState domain pre).revoked := by
  simpa [mem_authState_revoked_iff, outside]

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LineageValid.root_admissible
/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_authState_revoked_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_authState_revoked_iff

end Minidregg.Theory.CredentialAuthorityState
