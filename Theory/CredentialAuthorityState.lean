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

The state is one `Store layout`: one typed namespace ("plane") per kind of
authority record, keyed by that record's identifiers.  Absent epoch and
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
open Minidregg.Theory.Store

/-! ## Canonical typed sparse addresses -/

/-- One namespace per authorization-relevant state plane.  A capability plane
is indexed by its resource kind, so a capability for one kind cannot be written
into another kind's slot. -/
inductive AuthorityPlane where
  | capability (kind : ResourceKind)
  | issuerEpoch
  | policyEpoch
  | policyRevision
  /-- Content address of the exact versioned policy source. -/
  | policyAddress
  | subjectKeyEpoch
  /-- Exact signing-key payload at one subject epoch. The current epoch and
  this record are installed atomically by the source-owned physical entry. -/
  | subjectKey
  | revoked
  | nullifier
  deriving DecidableEq, Repr

/-- The key of each plane: the identifiers that name one record in it. -/
def AuthorityPlane.Key : AuthorityPlane → Type
  | .capability _ => CapabilityId
  | .issuerEpoch => IssuerId
  | .policyEpoch => PolicyId
  | .policyRevision => PolicyId
  | .policyAddress => PolicyId × PolicyRevision
  | .subjectKeyEpoch => SubjectId
  | .subjectKey => SubjectId × Epoch
  | .revoked => RevocationKey
  | .nullifier => Nat

instance AuthorityPlane.keyDecEq : (plane : AuthorityPlane) → DecidableEq plane.Key
  | .capability _ => inferInstanceAs (DecidableEq CapabilityId)
  | .issuerEpoch => inferInstanceAs (DecidableEq IssuerId)
  | .policyEpoch => inferInstanceAs (DecidableEq PolicyId)
  | .policyRevision => inferInstanceAs (DecidableEq PolicyId)
  | .policyAddress => inferInstanceAs (DecidableEq (PolicyId × PolicyRevision))
  | .subjectKeyEpoch => inferInstanceAs (DecidableEq SubjectId)
  | .subjectKey => inferInstanceAs (DecidableEq (SubjectId × Epoch))
  | .revoked => inferInstanceAs (DecidableEq RevocationKey)
  | .nullifier => inferInstanceAs (DecidableEq Nat)

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

/-- The value stored in each plane. -/
def AuthorityPlane.Value : AuthorityPlane → Type
  | .capability kind => StoredCapability kind
  | .issuerEpoch => Epoch
  | .policyEpoch => Epoch
  | .policyRevision => PolicyRevision
  | .policyAddress => Digest
  | .subjectKeyEpoch => Epoch
  | .subjectKey => CredentialSigningKey.KeyRecord
  | .revoked => Bool
  | .nullifier => Bool

instance AuthorityPlane.valueDecEq : (plane : AuthorityPlane) → DecidableEq plane.Value
  | .capability kind => inferInstanceAs (DecidableEq (StoredCapability kind))
  | .issuerEpoch => inferInstanceAs (DecidableEq Epoch)
  | .policyEpoch => inferInstanceAs (DecidableEq Epoch)
  | .policyRevision => inferInstanceAs (DecidableEq PolicyRevision)
  | .policyAddress => inferInstanceAs (DecidableEq Digest)
  | .subjectKeyEpoch => inferInstanceAs (DecidableEq Epoch)
  | .subjectKey => inferInstanceAs (DecidableEq CredentialSigningKey.KeyRecord)
  | .revoked => inferInstanceAs (DecidableEq Bool)
  | .nullifier => inferInstanceAs (DecidableEq Bool)

/-- The authority layout.  Every plane is RAM in this model: the effect family
(`CredentialAuthorityEffects`) guards each write by its exact prior value. -/
abbrev layout : Layout.{0, 0, 0} where
  Namespace := AuthorityPlane
  Key := AuthorityPlane.Key
  Value := AuthorityPlane.Value
  discipline := fun _ => .ram

abbrev Materializer := CellState.Materializer layout Digest
abbrev Cell (M : Materializer) := CellState.Materialized M

def readCapability {M : Materializer} (pre : Cell M)
    (kind : ResourceKind) (id : CapabilityId) : Option (StoredCapability kind) :=
  pre.logical ⟨.capability kind, id⟩

def issuerEpochAt {M : Materializer} (pre : Cell M) (issuer : IssuerId) : Epoch :=
  (pre.logical ⟨.issuerEpoch, issuer⟩).getD (show Epoch from 0)

def policyEpochAt {M : Materializer} (pre : Cell M) (policy : PolicyId) : Epoch :=
  (pre.logical ⟨.policyEpoch, policy⟩).getD (show Epoch from 0)

def policyRevisionAt {M : Materializer} (pre : Cell M) (policy : PolicyId) : PolicyRevision :=
  (pre.logical ⟨.policyRevision, policy⟩).getD (show PolicyRevision from 0)

/-- Missing sparse policy records resolve to the distinguished zero address;
production policy admission still requires membership under `pre.root`, so an
absent record is not silently authorized. -/
def policyAddressAt {M : Materializer} (pre : Cell M)
    (policy : PolicyId) (epoch : Epoch) : Digest :=
  (pre.logical ⟨.policyAddress, (policy, epoch)⟩).getD ⟨0⟩

def subjectKeyEpochAt {M : Materializer} (pre : Cell M)
    (subject : SubjectId) : Epoch :=
  (pre.logical ⟨.subjectKeyEpoch, subject⟩).getD (show Epoch from 0)

/-- Keyless epochs remain keyless. In particular a missing record is never
resolved by an external key directory or by the epoch reader's zero default.
Subject/epoch equality is checked even for arbitrary canonical sparse states;
the complete page representation additionally forces both from the record. -/
def currentSigningKey (logical : Store layout)
    (subject : SubjectId) : Option CredentialSigningKey.KeyRecord := do
  let epoch ← logical ⟨.subjectKeyEpoch, subject⟩
  let key ← logical ⟨.subjectKey, (subject, epoch)⟩
  if key.subject = subject.value ∧ key.keyEpoch = epoch then some key else none

theorem currentSigningKey_no_epoch (logical : Store layout)
    (subject : SubjectId) (absent : logical ⟨.subjectKeyEpoch, subject⟩ = none) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, absent, bind, Option.bind]

theorem currentSigningKey_no_record (logical : Store layout)
    (subject : SubjectId) (epoch : Epoch)
    (current : logical ⟨.subjectKeyEpoch, subject⟩ = some epoch)
    (absent : logical ⟨.subjectKey, (subject, epoch)⟩ = none) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, current, absent, bind, Option.bind]

theorem currentSigningKey_exact (logical : Store layout)
    (key : CredentialSigningKey.KeyRecord)
    (current : logical ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ = some key.keyEpoch)
    (record : logical ⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩ = some key) :
    currentSigningKey logical ⟨key.subject⟩ = some key := by
  simp [currentSigningKey, current, record, bind, Option.bind]

theorem currentSigningKey_rejects_mismatch
    (logical : Store layout) (subject : SubjectId)
    (epoch : Epoch) (key : CredentialSigningKey.KeyRecord)
    (current : logical ⟨.subjectKeyEpoch, subject⟩ = some epoch)
    (record : logical ⟨.subjectKey, (subject, epoch)⟩ = some key)
    (mismatch : ¬ (key.subject = subject.value ∧ key.keyEpoch = epoch)) :
    currentSigningKey logical subject = none := by
  simp [currentSigningKey, current, record, mismatch, bind, Option.bind]

def isRevoked {M : Materializer} (pre : Cell M) (key : RevocationKey) : Bool :=
  (pre.logical ⟨.revoked, key⟩).getD false

def isNullified {M : Materializer} (pre : Cell M) (id : Nat) : Bool :=
  (pre.logical ⟨.nullifier, id⟩).getD false

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

/-- A layout-owned view of canonical authority addresses. A concrete deployment
fixes this projection with its layout; it is not supplied by a request or a
host authority cache. This lets a bounded physical page retain its own exact
materialization while sharing the same authorization judgment. -/
structure StateProjection (L : Layout.{0, 0, 0}) where
  toCanonicalState : Store L → Store layout
  revocationKeys : Store L → Finset RevocationKey

/-- Read the common authorization state from the projected logical fields
and the actual materialized cell root. No second materializer or synthetic
encoding of the projected state participates. -/
def StateProjection.authState {L : Layout.{0, 0, 0}}
    {M : CellState.Materializer L Digest} (projection : StateProjection L)
    (pre : CellState.Materialized M) : AuthState :=
  let logical := projection.toCanonicalState pre.logical
  { capabilityRoot := pre.root
    revocationRoot := pre.root
    policyRoot := pre.root
    policyAddress := fun policy epoch =>
      (show Option Digest from logical ⟨.policyAddress, (policy, epoch)⟩).getD ⟨0⟩
    revoked := (projection.revocationKeys pre.logical).filter fun key =>
      (show Option Bool from logical ⟨.revoked, key⟩).getD false
    issuerEpoch := fun issuer =>
      (logical ⟨.issuerEpoch, issuer⟩).getD (show Epoch from 0)
    policyEpoch := fun policy =>
      (logical ⟨.policyEpoch, policy⟩).getD (show Epoch from 0)
    policyRevision := fun policy =>
      (logical ⟨.policyRevision, policy⟩).getD (show PolicyRevision from 0)
    subjectKeyEpoch := fun subject =>
      (logical ⟨.subjectKeyEpoch, subject⟩).getD (show Epoch from 0) }

/-- The unbounded canonical authority layout is the identity instance of the
same state-derived view. Existing clients keep this exact interpretation. -/
def ProjectionUniverse.stateProjection (domain : ProjectionUniverse) :
    StateProjection layout where
  toCanonicalState := fun logical => logical
  revocationKeys := fun _ => domain.revocationKeys

@[simp] theorem StateProjection.authState_policyRoot {L : Layout.{0, 0, 0}}
    {M : CellState.Materializer L Digest} (projection : StateProjection L)
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
    {M : CellState.Materializer layout Digest}
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
  simp [mem_authState_revoked_iff, outside]

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LineageValid.root_admissible_of_strict
/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_authState_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_authState_revoked_iff

end Minidregg.Theory.CredentialAuthorityState
