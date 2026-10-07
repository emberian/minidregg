/-
# Theory.CredentialAuthorityState -- canonical sparse authority state

The authorization projection is not an independently supplied cache.  This
module places capability records, issuer/policy/subject epochs, revocations,
and registrations in one typed `CellState`.  Single-use operation nullifiers
are not authority state: they live in the durable protocol's append-only
consumed set (`DurableCommitProtocol.Snapshot.consumed`), keyed by
`CredentialAuthorityReplay.nullifier`, so this cell does not grow per
operation.  The exact `Finset` revoked set required by
`TypedAuthorization.AuthState` is the revoked plane's own finite support, not
a deployment key list; both authenticated-set roots are
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
  /-- Presence-only and append-only: a present key IS a revocation, and no
  accepted patch removes or overwrites it. -/
  | revoked
  /-- Presence-only and append-only: a revocation key the domain has
  registered (and may later revoke).  This replaces the former "stored
  `false` in the revocation plane" encoding of "registered, not revoked". -/
  | registered
  /-- Append-only room parentage: `cell ↦ room` records the room a cell was
  born in. Written once, by the birth that creates `cell`, and never rewritten
  or removed, so `under R` coverage only grows. -/
  | parent
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
  | .registered => RevocationKey
  | .parent => Nat

instance AuthorityPlane.keyDecEq : (plane : AuthorityPlane) → DecidableEq plane.Key
  | .capability _ => inferInstanceAs (DecidableEq CapabilityId)
  | .issuerEpoch => inferInstanceAs (DecidableEq IssuerId)
  | .policyEpoch => inferInstanceAs (DecidableEq PolicyId)
  | .policyRevision => inferInstanceAs (DecidableEq PolicyId)
  | .policyAddress => inferInstanceAs (DecidableEq (PolicyId × PolicyRevision))
  | .subjectKeyEpoch => inferInstanceAs (DecidableEq SubjectId)
  | .subjectKey => inferInstanceAs (DecidableEq (SubjectId × Epoch))
  | .revoked => inferInstanceAs (DecidableEq RevocationKey)
  | .registered => inferInstanceAs (DecidableEq RevocationKey)
  | .parent => inferInstanceAs (DecidableEq Nat)

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
  | .revoked => Unit
  | .registered => Unit
  | .parent => Nat

instance AuthorityPlane.valueDecEq : (plane : AuthorityPlane) → DecidableEq plane.Value
  | .capability kind => inferInstanceAs (DecidableEq (StoredCapability kind))
  | .issuerEpoch => inferInstanceAs (DecidableEq Epoch)
  | .policyEpoch => inferInstanceAs (DecidableEq Epoch)
  | .policyRevision => inferInstanceAs (DecidableEq PolicyRevision)
  | .policyAddress => inferInstanceAs (DecidableEq Digest)
  | .subjectKeyEpoch => inferInstanceAs (DecidableEq Epoch)
  | .subjectKey => inferInstanceAs (DecidableEq CredentialSigningKey.KeyRecord)
  | .revoked => inferInstanceAs (DecidableEq Unit)
  | .registered => inferInstanceAs (DecidableEq Unit)
  | .parent => inferInstanceAs (DecidableEq Nat)

/-- The mutation discipline of each plane.  The revocation and registration
planes are presence-only and append-only: once present, a key stays present
with the same value under every accepted patch (`revocation_permanent`,
`registration_permanent`), so revocation is monotone by
the namespace's discipline rather than by a theorem each writer must recall.
Every other plane is RAM, guarded by its exact prior value. -/
def AuthorityPlane.discipline : AuthorityPlane → Discipline
  | .revoked => .appendOnly
  | .registered => .appendOnly
  | .parent => .appendOnly
  | _ => .ram

/-- The authority layout. -/
abbrev layout : Layout.{0, 0, 0} where
  Namespace := AuthorityPlane
  Key := AuthorityPlane.Key
  Value := AuthorityPlane.Value
  discipline := AuthorityPlane.discipline

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
  (pre.logical ⟨.revoked, key⟩).isSome

def isRegistered {M : Materializer} (pre : Cell M) (key : RevocationKey) : Bool :=
  (pre.logical ⟨.registered, key⟩).isSome

/-! ## Key standing: one source

A revocation key's standing is read from the two append-only presence planes
of the one cell and from nothing else.  For signing keys this replaces the
retired `KeyRecord.revoked` flag, which sat inside an overwritable RAM value. -/

/-- The revocation key of one signing-key version. -/
def signingKeyRevocation (key : CredentialSigningKey.KeyRecord) : RevocationKey :=
  .signingKey ⟨key.subject⟩ key.keyEpoch

inductive KeyStanding where
  | live
  | unregistered
  | revoked
  deriving DecidableEq, Repr

/-- The standing of a key in one cell.  This is THE signer check: the settlement
model (`AuthenticatedSettlementFinality.CurrentSigner`) and the host's signature
admission (`CredentialSignatureAdmission.select`) both call it. -/
def keyStanding {M : Materializer} (pre : Cell M) (key : RevocationKey) : KeyStanding :=
  if isRevoked pre key then .revoked
  else if isRegistered pre key then .live
  else .unregistered

theorem keyStanding_live_iff {M : Materializer} (pre : Cell M) (key : RevocationKey) :
    keyStanding pre key = .live ↔
      isRegistered pre key = true ∧ isRevoked pre key = false := by
  unfold keyStanding
  cases isRevoked pre key <;> cases isRegistered pre key <;> simp

theorem keyStanding_unregistered {M : Materializer} (pre : Cell M) (key : RevocationKey)
    (unregistered : isRegistered pre key = false) :
    keyStanding pre key ≠ .live := by
  rw [ne_eq, keyStanding_live_iff, unregistered]
  simp

theorem keyStanding_revoked {M : Materializer} (pre : Cell M) (key : RevocationKey)
    (revoked : isRevoked pre key = true) :
    keyStanding pre key = .revoked := by
  simp [keyStanding, revoked]

/-- **One source.**  Two cells that agree on a key's `registered` and `revoked`
entries give it the same standing, whatever else they hold -- in particular
whatever signing-key records, epochs or capabilities. -/
theorem keyStanding_eq_of_planes {M N : Materializer} (left : Cell M) (right : Cell N)
    (key : RevocationKey)
    (registered : left.logical ⟨.registered, key⟩ = right.logical ⟨.registered, key⟩)
    (revoked : left.logical ⟨.revoked, key⟩ = right.logical ⟨.revoked, key⟩) :
    keyStanding left key = keyStanding right key := by
  unfold keyStanding isRevoked isRegistered
  rw [registered, revoked]

/-- A signing-key record carries no standing: overwriting or freeing any record
of the `subjectKey` plane leaves every key's standing unchanged. -/
theorem keyStanding_subjectKey_frame {M N : Materializer} (pre : Cell M) (post : Cell N)
    (slot : SubjectId × Epoch) (record : Option CredentialSigningKey.KeyRecord)
    (written : post.logical = pre.logical.set ⟨.subjectKey, slot⟩ record)
    (key : RevocationKey) :
    keyStanding post key = keyStanding pre key :=
  keyStanding_eq_of_planes post pre key
    (by rw [written]; exact Store.set_ne _ _ _ _ (by intro same; cases same))
    (by rw [written]; exact Store.set_ne _ _ _ _ (by intro same; cases same))

/-! ## Proof-relevant validity of stored lineage -/

/-- Every stored edge retains its explicit origin and its matching static
relation. The terminal record is a root; historical operation authorization
is supplied by the accepted state transition, not by the serialized marker.

A root's `ancestors` are its revocation dependencies: empty for a grant issued
under nothing, and the creator's room-grant lineage for a grant born under a
room (`ResourceBirthPolicyController.Concrete.BornLineage`). They only ever add
refusals (`Admissible.ancestorNotRevoked`), never authority. -/
inductive LineageValid {kind : ResourceKind} (parentage : Parentage) :
    StoredCapability kind → Prop
  | root (cap : Capability kind)
      (parentNone : cap.parent = none)
      (rootSelf : cap.root = cap.id) :
      LineageValid parentage ⟨cap, []⟩
  | attenuate (child parent : Capability kind)
      (tail : List (ParentLink kind))
      (parentValid : LineageValid parentage ⟨parent, tail⟩)
      (edge : child.StrictAttenuates parent parentage) :
      LineageValid parentage ⟨child, ⟨parent, .strict⟩ :: tail⟩
  | delegate (child parent : Capability kind)
      (tail : List (ParentLink kind)) (request : Request kind)
      (parentValid : LineageValid parentage ⟨parent, tail⟩)
      (shape : DelegationShape request child parent parentage) :
      LineageValid parentage ⟨child, ⟨parent, .delegated request⟩ :: tail⟩

theorem LineageValid.root_admissible_of_strict {kind : ResourceKind}
    {stored : StoredCapability kind} {state : AuthState}
    {request : Request kind} (valid : LineageValid state.parent stored)
    (strict : stored.IsStrict)
    (admitted : stored.head.Admissible state request) :
    ∃ root : Capability kind,
      root.parent = none ∧ root.root = root.id ∧
      root.Admissible state request := by
  induction valid with
  | root cap parentNone rootSelf =>
      exact ⟨cap, parentNone, rootSelf, admitted⟩
  | attenuate child parent tail parentValid edge ih =>
      exact ih strict.2 (Capability.strict_attenuation_admits_subset edge admitted)
  | delegate child parent tail request parentValid shape ih =>
      cases strict.1

theorem LineageValid.root_bounds {kind : ResourceKind}
    {parentage : Parentage} {stored : StoredCapability kind}
    (valid : LineageValid parentage stored) :
    ∃ root : Capability kind, root.parent = none ∧ root.root = root.id ∧
      Capability.LineageBounds stored.head root parentage := by
  induction valid with
  | root cap parentNone rootSelf =>
      exact ⟨cap, parentNone, rootSelf, Capability.LineageBounds.refl cap parentage⟩
  | attenuate child parent tail parentValid edge ih =>
      obtain ⟨root, parentNone, rootSelf, bound⟩ := ih
      exact ⟨root, parentNone, rootSelf, edge.payload.lineageBounds.trans bound⟩
  | delegate child parent tail request parentValid shape ih =>
      obtain ⟨root, parentNone, rootSelf, bound⟩ := ih
      exact ⟨root, parentNone, rootSelf, shape.payload.lineageBounds.trans bound⟩

theorem LineageValid.nonempty_lineage {kind : ResourceKind}
    {parentage : Parentage} {stored : StoredCapability kind}
    (valid : LineageValid parentage stored) :
    Nonempty (stored.head.Lineage parentage) := by
  induction valid with
  | root cap parentNone rootSelf =>
      exact ⟨.root cap parentNone rootSelf⟩
  | attenuate child parent tail parentValid edge ih =>
      obtain ⟨lineage⟩ := ih
      exact ⟨.attenuate child parent lineage edge⟩
  | delegate child parent tail request parentValid shape ih =>
      obtain ⟨lineage⟩ := ih
      exact ⟨.delegate child parent request lineage shape⟩

/-! ## Exact projection into the common authorization judgment

The revoked set is the `revoked` plane's own finite support: the store is a
dependent finitely-supported map, so no deployment universe, key list or
caller-selected filter participates.  A key the plane holds is in the set, and
nothing else is. -/

/-- No recorded parents: every `under R` covers only `R` itself. -/
def noParents : Parentage := Parentage.empty

/-- The cell an address contributes to the parent plane's support. -/
def parentKeyAt : Address layout → Finset Nat
  | ⟨.parent, cell⟩ => {cell}
  | _ => ∅

/-- The cells with a recorded parent: exactly the `parent` plane's support. -/
def parentKeys (logical : Store layout) : Finset Nat :=
  logical.support.biUnion parentKeyAt

theorem mem_parentKeys_iff (logical : Store layout) (cell : Nat) :
    cell ∈ parentKeys logical ↔ (logical ⟨.parent, cell⟩).isSome = true := by
  constructor
  · intro member
    obtain ⟨⟨plane, stored⟩, supported, contributes⟩ := Finset.mem_biUnion.mp member
    cases plane <;> simp [parentKeyAt] at contributes
    have same : cell = stored := Finset.mem_singleton.mp contributes
    subst same
    exact Option.isSome_iff_ne_none.mpr (DFinsupp.mem_support_iff.mp supported)
  · intro present
    exact Finset.mem_biUnion.mpr ⟨⟨.parent, cell⟩,
      DFinsupp.mem_support_iff.mpr (Option.isSome_iff_ne_none.mp present),
      Finset.mem_singleton_self cell⟩

/-- The parent projection of one authority store: its `parent` plane, with
the plane's own finite support. -/
def parentageOf (logical : Store layout) : Parentage where
  parentOf cell := logical ⟨.parent, cell⟩
  support := parentKeys logical
  supported cell recorded :=
    (mem_parentKeys_iff logical cell).mpr (Option.isSome_iff_ne_none.mpr recorded)

/-- The parent projection reads the `parent` plane and nothing else. -/
theorem parentageOf_congr {left right : Store layout}
    (same : ∀ cell, left ⟨.parent, cell⟩ = right ⟨.parent, cell⟩) :
    parentageOf left = parentageOf right := by
  unfold parentageOf
  congr 1
  · funext cell
    exact same cell
  · ext cell
    rw [mem_parentKeys_iff, mem_parentKeys_iff, same]

/-- The key an address contributes to the revoked set: its own key on the
`revoked` plane, nothing on any other plane. -/
def revokedKeyAt : Address layout → Finset RevocationKey
  | ⟨.revoked, key⟩ => {key}
  | _ => ∅

/-- The revoked keys of one authority store: exactly the `revoked` plane's
finite support. -/
def revokedKeys (logical : Store layout) : Finset RevocationKey :=
  logical.support.biUnion revokedKeyAt

theorem mem_revokedKeys_iff (logical : Store layout) (key : RevocationKey) :
    key ∈ revokedKeys logical ↔ (logical ⟨.revoked, key⟩).isSome = true := by
  constructor
  · intro member
    obtain ⟨⟨plane, stored⟩, supported, contributes⟩ := Finset.mem_biUnion.mp member
    cases plane <;> simp [revokedKeyAt] at contributes
    have same : key = stored := Finset.mem_singleton.mp contributes
    subst same
    exact Option.isSome_iff_ne_none.mpr (DFinsupp.mem_support_iff.mp supported)
  · intro present
    exact Finset.mem_biUnion.mpr ⟨⟨.revoked, key⟩,
      DFinsupp.mem_support_iff.mpr (Option.isSome_iff_ne_none.mp present),
      Finset.mem_singleton_self key⟩

/-- The sole `AuthState` projection.  Capability and revocation witnesses use
the SAME canonical cell root; revoked membership and every epoch are read from
that exact cell. -/
def authState {M : Materializer} (pre : Cell M) : AuthState where
  capabilityRoot := pre.root
  revocationRoot := pre.root
  policyRoot := pre.root
  policyAddress := policyAddressAt pre
  revoked := revokedKeys pre.logical
  issuerEpoch := issuerEpochAt pre
  policyEpoch := policyEpochAt pre
  policyRevision := policyRevisionAt pre
  subjectKeyEpoch := subjectKeyEpochAt pre
  parent := parentageOf pre.logical

@[simp] theorem authState_capabilityRoot {M : Materializer} (pre : Cell M) :
    (authState pre).capabilityRoot = pre.root := rfl

@[simp] theorem authState_revocationRoot {M : Materializer} (pre : Cell M) :
    (authState pre).revocationRoot = pre.root := rfl

@[simp] theorem authState_policyRoot {M : Materializer} (pre : Cell M) :
    (authState pre).policyRoot = pre.root := rfl

@[simp] theorem authState_policyAddress {M : Materializer} (pre : Cell M)
    (policy : PolicyId) (epoch : Epoch) :
    (authState pre).policyAddress policy epoch = policyAddressAt pre policy epoch := rfl

@[simp] theorem authState_issuerEpoch {M : Materializer} (pre : Cell M) (issuer : IssuerId) :
    (authState pre).issuerEpoch issuer = issuerEpochAt pre issuer := rfl

@[simp] theorem authState_policyEpoch {M : Materializer} (pre : Cell M) (policy : PolicyId) :
    (authState pre).policyEpoch policy = policyEpochAt pre policy := rfl

@[simp] theorem authState_policyRevision {M : Materializer} (pre : Cell M) (policy : PolicyId) :
    (authState pre).policyRevision policy = policyRevisionAt pre policy := rfl

@[simp] theorem authState_subjectKeyEpoch {M : Materializer} (pre : Cell M) (subject : SubjectId) :
    (authState pre).subjectKeyEpoch subject = subjectKeyEpochAt pre subject := rfl

/-- Projected revocation membership is exactly the cell's `revoked` plane read:
no key outside the plane is revoked, and no key in it can be filtered away. -/
@[simp] theorem mem_authState_revoked_iff {M : Materializer} (pre : Cell M)
    (key : RevocationKey) :
    key ∈ (authState pre).revoked ↔ isRevoked pre key = true :=
  mem_revokedKeys_iff pre.logical key

/-! ## Append-only presence planes: revocation is monotone -/

/-- A present revocation survives every valid patch. -/
theorem revocation_permanent (store : Store layout) (patch : Patch layout)
    (key : RevocationKey) (valid : Patch.ValidFrom store patch)
    (revoked : store ⟨.revoked, key⟩ = some ()) :
    Patch.run store patch ⟨.revoked, key⟩ = some () :=
  Patch.appendOnly_present_preserved store patch ⟨.revoked, key⟩ () valid rfl revoked

/-- Satisfiable pole: revoking a key not yet revoked is enabled. -/
theorem revoke_enabled_iff (store : Store layout) (key : RevocationKey) :
    (Op.allocate (L := layout) .revoked key ()).Enabled store ↔
      store ⟨.revoked, key⟩ = none := by
  change layout.discipline .revoked ≠ .rom ∧ store ⟨.revoked, key⟩ = none ↔ _
  simp [AuthorityPlane.discipline]

/-- Refuting pole: no operation removes a revocation. -/
theorem unrevoke_refused (store : Store layout) (key : RevocationKey) :
    ¬ (Op.free (L := layout) .revoked key ()).Enabled store := by
  change ¬ (layout.discipline .revoked = .ram ∧ store ⟨.revoked, key⟩ = some ())
  simp [AuthorityPlane.discipline]

/-- Refuting pole: no operation overwrites a revocation. -/
theorem revocation_overwrite_refused (store : Store layout) (key : RevocationKey) :
    ¬ (Op.write (L := layout) .revoked key () ()).Enabled store := by
  change ¬ (layout.discipline .revoked = .ram ∧ store ⟨.revoked, key⟩ = some ())
  simp [AuthorityPlane.discipline]

/-! ## Registration is append-only: deregistration is impossible

A revocation key's lifecycle is read from two presence planes and nothing
else: registered-and-live is `registered` present with `revoked` absent; a
revoked key is `registered` present AND `revoked` present.  Neither plane can
lose an entry, so the only transition is live → revoked, and it is permanent. -/

/-- A registration survives every valid patch. -/
theorem registration_permanent (store : Store layout) (patch : Patch layout)
    (key : RevocationKey) (valid : Patch.ValidFrom store patch)
    (registered : store ⟨.registered, key⟩ = some ()) :
    Patch.run store patch ⟨.registered, key⟩ = some () :=
  Patch.appendOnly_present_preserved store patch ⟨.registered, key⟩ () valid rfl registered

/-- Satisfiable pole: registering a key not yet registered is enabled. -/
theorem register_enabled_iff (store : Store layout) (key : RevocationKey) :
    (Op.allocate (L := layout) .registered key ()).Enabled store ↔
      store ⟨.registered, key⟩ = none := by
  change layout.discipline .registered ≠ .rom ∧ store ⟨.registered, key⟩ = none ↔ _
  simp [AuthorityPlane.discipline]

/-- Refuting pole: no operation removes a registration. -/
theorem deregister_refused (store : Store layout) (key : RevocationKey) :
    ¬ (Op.free (L := layout) .registered key ()).Enabled store := by
  change ¬ (layout.discipline .registered = .ram ∧ store ⟨.registered, key⟩ = some ())
  simp [AuthorityPlane.discipline]

/-- Refuting pole: no operation overwrites a registration. -/
theorem registration_overwrite_refused (store : Store layout) (key : RevocationKey) :
    ¬ (Op.write (L := layout) .registered key () ()).Enabled store := by
  change ¬ (layout.discipline .registered = .ram ∧ store ⟨.registered, key⟩ = some ())
  simp [AuthorityPlane.discipline]

/-! ### Monotonicity over every accepted history

`Patch.Executes` composes by list append (`Patch.Executes.append`), so a
history of accepted patches is one executed patch and the statements below
cover every finite history, not only one step. -/

/-- On an append-only plane a present entry is present, with the same value,
after every executed patch. -/
theorem presence_monotone (plane : AuthorityPlane)
    (appendOnly : AuthorityPlane.discipline plane = .appendOnly) (key : plane.Key)
    (value : plane.Value) {pre post : Store layout} {patch : Patch layout}
    (executes : Patch.Executes pre patch post)
    (present : pre ⟨plane, key⟩ = some value) :
    post ⟨plane, key⟩ = some value := by
  obtain ⟨valid, ran⟩ := executes
  rw [← ran]
  exact Patch.appendOnly_present_preserved pre patch ⟨plane, key⟩ value valid appendOnly present

/-- **Revocation is monotone:** once revoked, revoked after every accepted history. -/
theorem revocation_monotone {pre post : Store layout} {patch : Patch layout}
    (executes : Patch.Executes pre patch post) (key : RevocationKey)
    (revoked : pre ⟨.revoked, key⟩ = some ()) :
    post ⟨.revoked, key⟩ = some () :=
  presence_monotone .revoked rfl key () executes revoked

/-- **Registration is monotone:** once registered, registered after every
accepted history.  Deregistration is not an operation of this domain. -/
theorem registration_monotone {pre post : Store layout} {patch : Patch layout}
    (executes : Patch.Executes pre patch post) (key : RevocationKey)
    (registered : pre ⟨.registered, key⟩ = some ()) :
    post ⟨.registered, key⟩ = some () :=
  presence_monotone .registered rfl key () executes registered

/-- A revoked key (registered present AND revoked present) stays exactly that:
no accepted history returns it to registered-and-live, or to unregistered. -/
theorem revoked_registration_permanent {pre post : Store layout} {patch : Patch layout}
    (executes : Patch.Executes pre patch post) (key : RevocationKey)
    (registered : pre ⟨.registered, key⟩ = some ())
    (revoked : pre ⟨.revoked, key⟩ = some ()) :
    post ⟨.registered, key⟩ = some () ∧ post ⟨.revoked, key⟩ = some () :=
  ⟨registration_monotone executes key registered, revocation_monotone executes key revoked⟩

/-! ### Refusal at the cell, both poles, for every presence plane -/

/-- Validation of a one-operation patch that frees an entry of an append-only
plane is rejected at its first operation, whatever the materializer and
whether or not the entry is present. -/
theorem presence_free_rejected (M : Materializer) (pre : Cell M) (plane : AuthorityPlane)
    (appendOnly : AuthorityPlane.discipline plane = .appendOnly)
    (key : plane.Key) (value : plane.Value) :
    CellState.validate M pre pre.root [Op.free (L := layout) plane key value] =
      .rejected (.disabledOperation 0) := by
  have notEnabled : ¬ (Op.free (L := layout) plane key value).Enabled pre.logical := by
    rintro ⟨ram, _⟩
    change AuthorityPlane.discipline plane = .ram at ram
    rw [appendOnly] at ram
    cases ram
  have disabled :
      Patch.firstDisabled? pre.logical [Op.free (L := layout) plane key value] = some 0 := by
    simp [Patch.firstDisabled?, notEnabled]
  unfold CellState.validate
  rw [dif_pos rfl]
  split
  · rename_i reported
    rw [disabled] at reported
    cases reported
  · rename_i index reported
    rw [disabled] at reported
    cases reported
    rfl

/-- Allocating an absent entry of an append-only plane validates, and the post
holds it. -/
theorem presence_allocate_accepted (M : Materializer) (pre : Cell M) (plane : AuthorityPlane)
    (appendOnly : AuthorityPlane.discipline plane = .appendOnly)
    (key : plane.Key) (value : plane.Value)
    (fresh : pre.logical ⟨plane, key⟩ = none) :
    ∃ validated : CellState.ValidatedPatch M pre pre.root
        [Op.allocate (L := layout) plane key value],
      CellState.validate M pre pre.root [Op.allocate (L := layout) plane key value] =
          .accepted validated ∧
        validated.apply.logical ⟨plane, key⟩ = some value := by
  have enabled : (Op.allocate (L := layout) plane key value).Enabled pre.logical := by
    refine ⟨?_, fresh⟩
    change AuthorityPlane.discipline plane ≠ .rom
    rw [appendOnly]
    nofun
  obtain ⟨validated, accepted⟩ := CellState.validate_accepts M pre pre.root
    [Op.allocate (L := layout) plane key value] rfl ⟨enabled, trivial⟩
  exact ⟨validated, accepted, by simp [Op.apply]⟩

/-- **At the cell.**  Validation of a patch that would un-revoke a key is
rejected at its first operation, whatever the materializer. -/
theorem unrevoke_rejected (M : Materializer) (pre : Cell M) (key : RevocationKey) :
    CellState.validate M pre pre.root [Op.free (L := layout) .revoked key ()] =
      .rejected (.disabledOperation 0) :=
  presence_free_rejected M pre .revoked rfl key ()

/-- **At the cell.**  Revoking an unrevoked key validates, and the post has it
revoked. -/
theorem revoke_accepted (M : Materializer) (pre : Cell M) (key : RevocationKey)
    (fresh : pre.logical ⟨.revoked, key⟩ = none) :
    ∃ validated : CellState.ValidatedPatch M pre pre.root
        [Op.allocate (L := layout) .revoked key ()],
      CellState.validate M pre pre.root [Op.allocate (L := layout) .revoked key ()] =
          .accepted validated ∧
        validated.apply.logical ⟨.revoked, key⟩ = some () :=
  presence_allocate_accepted M pre .revoked rfl key () fresh

/-- **At the cell, refuting pole.**  Deregistration is rejected at operation 0,
whatever the materializer: a registered key cannot be erased. -/
theorem deregister_rejected (M : Materializer) (pre : Cell M) (key : RevocationKey) :
    CellState.validate M pre pre.root [Op.free (L := layout) .registered key ()] =
      .rejected (.disabledOperation 0) :=
  presence_free_rejected M pre .registered rfl key ()

/-- **At the cell, satisfiable pole.**  Registering a fresh key validates, and
the post has it registered. -/
theorem register_accepted (M : Materializer) (pre : Cell M) (key : RevocationKey)
    (fresh : pre.logical ⟨.registered, key⟩ = none) :
    ∃ validated : CellState.ValidatedPatch M pre pre.root
        [Op.allocate (L := layout) .registered key ()],
      CellState.validate M pre pre.root [Op.allocate (L := layout) .registered key ()] =
          .accepted validated ∧
        validated.apply.logical ⟨.registered, key⟩ = some () :=
  presence_allocate_accepted M pre .registered rfl key () fresh

/-- Once revoked, a key stays revoked under every accepted history: its standing
can never return to `live`.  (`revocation_monotone` on the append-only plane.) -/
theorem keyStanding_revoked_permanent {M N : Materializer} (pre : Cell M) (post : Cell N)
    {patch : Patch layout} (executes : Patch.Executes pre.logical patch post.logical)
    (key : RevocationKey) (revoked : keyStanding pre key = .revoked) :
    keyStanding post key = .revoked := by
  have present : pre.logical ⟨.revoked, key⟩ = some () := by
    unfold keyStanding at revoked
    cases hr : isRevoked pre key
    · cases hg : isRegistered pre key <;> simp [hr, hg] at revoked
    · simp only [isRevoked, Option.isSome_iff_exists] at hr
      obtain ⟨value, present⟩ := hr
      exact present.trans (congrArg some (Subsingleton.elim (α := Unit) value ()))
  apply keyStanding_revoked
  have kept := revocation_monotone executes key present
  show (post.logical ⟨.revoked, key⟩).isSome = true
  rw [kept]
  rfl

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LineageValid.root_admissible_of_strict
/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_authState_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_authState_revoked_iff
/-- info: 'Minidregg.Theory.CredentialAuthorityState.revocation_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revocation_permanent
/-- info: 'Minidregg.Theory.CredentialAuthorityState.unrevoke_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevoke_rejected
/-- info: 'Minidregg.Theory.CredentialAuthorityState.revoke_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_accepted
/-- info: 'Minidregg.Theory.CredentialAuthorityState.registration_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registration_permanent
/-- info: 'Minidregg.Theory.CredentialAuthorityState.revocation_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revocation_monotone
/-- info: 'Minidregg.Theory.CredentialAuthorityState.registration_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registration_monotone
/-- info: 'Minidregg.Theory.CredentialAuthorityState.revoked_registration_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_registration_permanent
/-- info: 'Minidregg.Theory.CredentialAuthorityState.deregister_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deregister_refused
/-- info: 'Minidregg.Theory.CredentialAuthorityState.deregister_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deregister_rejected
/-- info: 'Minidregg.Theory.CredentialAuthorityState.register_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms register_accepted

/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_revokedKeys_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_revokedKeys_iff
/-- info: 'Minidregg.Theory.CredentialAuthorityState.keyStanding_live_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyStanding_live_iff
/-- info: 'Minidregg.Theory.CredentialAuthorityState.keyStanding_eq_of_planes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyStanding_eq_of_planes
/-- info: 'Minidregg.Theory.CredentialAuthorityState.keyStanding_subjectKey_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyStanding_subjectKey_frame
/-- info: 'Minidregg.Theory.CredentialAuthorityState.keyStanding_revoked_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyStanding_revoked_permanent
/-- info: 'Minidregg.Theory.CredentialAuthorityState.parentageOf_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityState.parentageOf_congr
/-- info: 'Minidregg.Theory.CredentialAuthorityState.mem_parentKeys_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityState.mem_parentKeys_iff
end Minidregg.Theory.CredentialAuthorityState
