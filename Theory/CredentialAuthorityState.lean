/-
# Theory.CredentialAuthorityState -- canonical sparse authority state

The authorization projection is not an independently supplied cache.  This
module places capability records, issuer/policy/subject epochs, revocations,
and single-use operation nullifiers in one typed `CellState`.  A finite
deployment universe turns the sparse revocation plane into the exact `Finset`
required by `TypedAuthorization.AuthState`; both authenticated-set roots are
the root of the same canonical materialization.

Capability lineage is retained as first-order capability and edge-origin data.
Its validity predicate checks every adjacent strict attenuation or explicit
subject delegation against its own relation, including the terminal root.
The accepted mutation family establishes authority to create a delegated edge;
the stored origin alone is not a cryptographic certificate.

`CellState.LogicalState` stores a finite dependent map.  Absent epoch and
membership entries are read through explicit zero/false defaults below;
capability absence remains the primitive optional lookup result.  Thus the
word "sparse" here is representation, not merely vocabulary.
-/
import Theory.AcceptedCellEffect
import Theory.CredentialAuthorityFamily
import Theory.CredentialSigningKey

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
  | policyRevision (policy : PolicyId)
  /-- Content address of the exact versioned policy source. -/
  | policyAddress (policy : PolicyId) (revision : PolicyRevision)
  | subjectKeyEpoch (subject : SubjectId)
  /-- Exact signing-key payload at one subject epoch. The current epoch and
  this record are installed atomically by the source-owned physical entry. -/
  | subjectKey (subject : SubjectId) (epoch : Epoch)
  | revoked (key : RevocationKey)
  | nullifier (id : Nat)
  deriving DecidableEq, Repr

/-- A stored lineage is data: the head capability followed by its parent,
grandparent, and so on.  Validity is a separate Lean proposition below. -/
structure StoredCapability (kind : ResourceKind) where
  head : Capability kind
  ancestry : List (ParentLink kind)
  deriving DecidableEq

def strictAncestry {kind : ResourceKind} : List (ParentLink kind) → Prop
  | [] => True
  | link :: tail => link.origin = .strict ∧ strictAncestry tail

def StoredCapability.IsStrict {kind : ResourceKind} (stored : StoredCapability kind) : Prop :=
  strictAncestry stored.ancestry

/-- Dependent values prevent a capability for one resource kind from being
written into another kind's slot. -/
def AuthorityField.Value : AuthorityField → Type
  | .capability kind _ => StoredCapability kind
  | .issuerEpoch _ => Epoch
  | .policyEpoch _ => Epoch
  | .policyRevision _ => PolicyRevision
  | .policyAddress _ _ => Digest
  | .subjectKeyEpoch _ => Epoch
  | .subjectKey _ _ => CredentialSigningKey.KeyRecord
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

def policyRevisionAt {M : Materializer} (pre : Cell M) (policy : PolicyId) : PolicyRevision :=
  (pre.logical.fields (.policyRevision policy)).getD (show PolicyRevision from 0)

/-- Missing sparse policy records resolve to the distinguished zero address;
production policy admission still requires membership under `pre.root`, so an
absent record is not silently authorized. -/
def policyAddressAt {M : Materializer} (pre : Cell M)
    (policy : PolicyId) (epoch : Epoch) : Digest :=
  (pre.logical.fields (.policyAddress policy epoch)).getD ⟨0⟩

def subjectKeyEpochAt {M : Materializer} (pre : Cell M)
    (subject : SubjectId) : Epoch :=
  (pre.logical.fields (.subjectKeyEpoch subject)).getD (show Epoch from 0)

/-- Keyless epochs remain keyless. In particular a missing record is never
resolved by an external key directory or by the epoch reader's zero default.
Subject/epoch equality is checked even for arbitrary canonical sparse states;
the complete page representation additionally forces both from the record. -/
def currentSigningKey (logical : CellState.LogicalState schema.{0, 0})
    (subject : SubjectId) : Option CredentialSigningKey.KeyRecord := do
  let epoch ← logical.fields (.subjectKeyEpoch subject)
  let key ← logical.fields (.subjectKey subject epoch)
  if key.subject = subject.value ∧ key.keyEpoch = epoch then some key else none

theorem currentSigningKey_no_epoch (logical : CellState.LogicalState schema.{0, 0})
    (subject : SubjectId) (absent : logical.fields (.subjectKeyEpoch subject) = none) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, absent, bind, Option.bind]

theorem currentSigningKey_no_record (logical : CellState.LogicalState schema.{0, 0})
    (subject : SubjectId) (epoch : Epoch)
    (current : logical.fields (.subjectKeyEpoch subject) = some epoch)
    (absent : logical.fields (.subjectKey subject epoch) = none) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, current, absent, bind, Option.bind]

theorem currentSigningKey_exact (logical : CellState.LogicalState schema.{0, 0})
    (key : CredentialSigningKey.KeyRecord)
    (current : logical.fields (.subjectKeyEpoch ⟨key.subject⟩) = some key.keyEpoch)
    (record : logical.fields (.subjectKey ⟨key.subject⟩ key.keyEpoch) = some key) :
    currentSigningKey logical ⟨key.subject⟩ = some key := by
  simp [currentSigningKey, current, record, bind, Option.bind]

theorem currentSigningKey_rejects_mismatch
    (logical : CellState.LogicalState schema.{0, 0}) (subject : SubjectId)
    (epoch : Epoch) (key : CredentialSigningKey.KeyRecord)
    (current : logical.fields (.subjectKeyEpoch subject) = some epoch)
    (record : logical.fields (.subjectKey subject epoch) = some key)
    (mismatch : ¬ (key.subject = subject.value ∧ key.keyEpoch = epoch)) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, current, record, mismatch, bind, Option.bind]

def isRevoked {M : Materializer} (pre : Cell M) (key : RevocationKey) : Bool :=
  (pre.logical.fields (.revoked key)).getD false

def isNullified {M : Materializer} (pre : Cell M) (id : Nat) : Bool :=
  (pre.logical.fields (.nullifier id)).getD false

/-! ## Proof-relevant validity of stored lineage -/

/-- Every stored edge retains its explicit origin and its matching static
relation. The terminal record is a root; historical operation authorization
is supplied by the accepted state transition, not by the serialized marker. -/
inductive LineageValid {kind : ResourceKind} : StoredCapability kind → Prop
  | root (cap : Capability kind)
      (parentNone : cap.parent = none)
      (rootSelf : cap.root = cap.id)
      (ancestorsEmpty : cap.ancestors = ∅) :
      LineageValid ⟨cap, []⟩
  | attenuate (child parent : Capability kind)
      (tail : List (ParentLink kind))
      (parentValid : LineageValid ⟨parent, tail⟩)
      (edge : child.StrictAttenuates parent) :
      LineageValid ⟨child, ⟨parent, .strict⟩ :: tail⟩
  | delegate (child parent : Capability kind)
      (tail : List (ParentLink kind)) (request : Request kind)
      (parentValid : LineageValid ⟨parent, tail⟩)
      (shape : DelegationShape request child parent) :
      LineageValid ⟨child, ⟨parent, .delegated request⟩ :: tail⟩

theorem LineageValid.root_admissible_of_strict {kind : ResourceKind}
    {stored : StoredCapability kind} {state : AuthState}
    {request : Request kind} (valid : LineageValid stored)
    (strict : stored.IsStrict)
    (admitted : stored.head.Admissible state request) :
    ∃ root : Capability kind,
      root.parent = none ∧ root.root = root.id ∧
      root.Admissible state request := by
  induction valid with
  | root cap parentNone rootSelf ancestorsEmpty =>
      exact ⟨cap, parentNone, rootSelf, admitted⟩
  | attenuate child parent tail parentValid edge ih =>
      exact ih strict.2 (Capability.strict_attenuation_admits_subset edge admitted)
  | delegate child parent tail request parentValid shape ih =>
      cases strict.1

theorem LineageValid.root_bounds {kind : ResourceKind}
    {stored : StoredCapability kind} (valid : LineageValid stored) :
    ∃ root : Capability kind, root.parent = none ∧ root.root = root.id ∧
      Capability.LineageBounds stored.head root := by
  induction valid with
  | root cap parentNone rootSelf ancestorsEmpty =>
      exact ⟨cap, parentNone, rootSelf, Capability.LineageBounds.refl cap⟩
  | attenuate child parent tail parentValid edge ih =>
      obtain ⟨root, parentNone, rootSelf, bound⟩ := ih
      exact ⟨root, parentNone, rootSelf, edge.payload.lineageBounds.trans bound⟩
  | delegate child parent tail request parentValid shape ih =>
      obtain ⟨root, parentNone, rootSelf, bound⟩ := ih
      exact ⟨root, parentNone, rootSelf, shape.payload.lineageBounds.trans bound⟩

theorem LineageValid.nonempty_lineage {kind : ResourceKind}
    {stored : StoredCapability kind} (valid : LineageValid stored) :
    Nonempty stored.head.Lineage := by
  induction valid with
  | root cap parentNone rootSelf ancestorsEmpty =>
      exact ⟨.root cap parentNone rootSelf ancestorsEmpty⟩
  | attenuate child parent tail parentValid edge ih =>
      obtain ⟨lineage⟩ := ih
      exact ⟨.attenuate child parent lineage edge⟩
  | delegate child parent tail request parentValid shape ih =>
      obtain ⟨lineage⟩ := ih
      exact ⟨.delegate child parent request lineage shape⟩

/-! ## Exact projection into the common authorization judgment -/

/-- A deployment declares the finite revocation keys whose sparse cells are
part of this authority domain.  Issuer/policy/subject epoch reads remain total
typed addresses and require no enumerable universe. -/
structure ProjectionUniverse where
  revocationKeys : Finset RevocationKey

/-- A schema-owned view of canonical authority fields. A concrete deployment
fixes this projection with its schema; it is not supplied by a request or a
host authority cache. This lets a bounded physical page retain its own exact
materialization while sharing the same authorization judgment. -/
structure StateProjection (S : CellState.Schema) where
  toCanonicalState : CellState.LogicalState S → CellState.LogicalState schema.{0, 0}
  revocationKeys : CellState.LogicalState S → Finset RevocationKey

/-- Read the common authorization state from the projected logical fields
and the actual materialized cell root. No second materializer or synthetic
encoding of the projected state participates. -/
def StateProjection.authState {S : CellState.Schema}
    {M : CellState.Materializer S Digest} (projection : StateProjection S)
    (pre : CellState.Materialized M) : AuthState :=
  let logical := projection.toCanonicalState pre.logical
  { capabilityRoot := pre.root
    revocationRoot := pre.root
    policyRoot := pre.root
    policyAddress := fun policy epoch =>
      (show Option Digest from logical.fields (.policyAddress policy epoch)).getD ⟨0⟩
    revoked := (projection.revocationKeys pre.logical).filter fun key =>
      (show Option Bool from logical.fields (.revoked key)).getD false
    issuerEpoch := fun issuer =>
      (logical.fields (.issuerEpoch issuer)).getD (show Epoch from 0)
    policyEpoch := fun policy =>
      (logical.fields (.policyEpoch policy)).getD (show Epoch from 0)
    policyRevision := fun policy =>
      (logical.fields (.policyRevision policy)).getD (show PolicyRevision from 0)
    subjectKeyEpoch := fun subject =>
      (logical.fields (.subjectKeyEpoch subject)).getD (show Epoch from 0) }

/-- The unbounded canonical authority schema is the identity instance of the
same state-derived view. Existing clients keep this exact interpretation. -/
def ProjectionUniverse.stateProjection (domain : ProjectionUniverse) :
    StateProjection schema.{0, 0} where
  toCanonicalState := fun logical => logical
  revocationKeys := fun _ => domain.revocationKeys

@[simp] theorem StateProjection.authState_policyRoot {S : CellState.Schema}
    {M : CellState.Materializer S Digest} (projection : StateProjection S)
    (pre : CellState.Materialized M) :
    (projection.authState pre).policyRoot = pre.root := rfl

/-- The sole `AuthState` projection.  Capability and revocation witnesses use
the SAME canonical cell root; revoked membership and every epoch are read from
that exact cell. -/
def authState {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) : AuthState where
  capabilityRoot := pre.root
  revocationRoot := pre.root
  policyRoot := pre.root
  policyAddress := policyAddressAt pre
  revoked := domain.revocationKeys.filter fun key => isRevoked pre key
  issuerEpoch := issuerEpochAt pre
  policyEpoch := policyEpochAt pre
  policyRevision := policyRevisionAt pre
  subjectKeyEpoch := subjectKeyEpochAt pre

@[simp] theorem authState_identity_projection
    {M : CellState.Materializer schema.{0, 0} Digest}
    (domain : ProjectionUniverse) (pre : Cell M) :
    domain.stateProjection.authState pre = authState domain pre := rfl

@[simp] theorem authState_capabilityRoot {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) :
    (authState domain pre).capabilityRoot = pre.root := rfl

@[simp] theorem authState_revocationRoot {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) :
    (authState domain pre).revocationRoot = pre.root := rfl

@[simp] theorem authState_policyRoot {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) :
    (authState domain pre).policyRoot = pre.root := rfl

@[simp] theorem authState_policyAddress {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M)
    (policy : PolicyId) (epoch : Epoch) :
    (authState domain pre).policyAddress policy epoch =
      policyAddressAt pre policy epoch := rfl

@[simp] theorem authState_issuerEpoch {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (issuer : IssuerId) :
    (authState domain pre).issuerEpoch issuer = issuerEpochAt pre issuer := rfl

@[simp] theorem authState_policyEpoch {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (policy : PolicyId) :
    (authState domain pre).policyEpoch policy = policyEpochAt pre policy := rfl

@[simp] theorem authState_policyRevision {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (policy : PolicyId) :
    (authState domain pre).policyRevision policy = policyRevisionAt pre policy := rfl

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

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LineageValid.root_admissible_of_strict
/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_authState_revoked_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_authState_revoked_iff

end Minidregg.Theory.CredentialAuthorityState
