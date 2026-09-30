/-
# Compiler.CredentialAuthorityDomain -- the authority domain is one cell

The authority domain of a deployment is ONE store cell
(`CredentialAuthorityCell`): a `Store` over `CredentialAuthorityState.layout`
at the declared `StoreCodec` wire.  There is no catalogue, no shard, no
routing of entry groups to pages and no second view of the same store.

A `Snapshot` is the deployment's domain digest together with that one cell.
Everything a consumer reads is read from the cell:

* the revocation universe is derived from the cell's finite support: the
  keys of the `revoked` and `registered` planes and every key a stored
  capability names (`mem_revocationUniverse_iff`), so no caller-authored list
  can omit a live revocation (`mem_revoked_iff`), and a registered or issued,
  unrevoked key is in the universe, which is how families read registration;
* the authority clock (`Snapshot.revision`) and the spent-marker query
  (`Snapshot.spent`) are NOT cell state.  Both are read from the durable
  system state the snapshot is loaded from: the clock is the durable height
  and `spent` is the durable consumed-nullifier set at the authority replay
  key (`CredentialAuthorityDomainReceiver.Loaded.revisionExact/spentExact`).
  The cell therefore does not grow per operation;
* policy heads and current signing keys are the typed planes' reads.

Preparation is the guarded patch on that one cell, validated by the kernel
validator at the cell's own root.  A policy update retires the superseded
revision's address in the same patch; a signing-key rotation retires the
superseded record.  Nothing here authorizes: the surrounding semantic family
supplies authorization.

Retired: `LOOM/AUTH/DOMAIN` catalogue cells, `LOOM/AUTH/POLICYPAGE` shards and
`LOOM/AUTH/STATE` whole-state cells refuse to decode at the authority cell
(`CredentialAuthorityCell.retired_page_frame_refused`,
`retired_state_frame_refused`, and `retired_catalogue_frame_refused` below).
-/
import Compiler.CredentialAuthorityCell
import Theory.CanonicalAuthorityProjection
import Theory.CredentialAuthorityEffects
import Theory.PolicyInstall

namespace Minidregg.Compiler.CredentialAuthorityDomain

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
  (Entry assignAll setAll run_assignAll)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Cell := CredentialAuthorityCell.Cell

namespace Snapshot

/-- The revocation keys a stored capability names: its own, its ancestors'
and its channels'. -/
def capabilityKeys {kind : ResourceKind} (stored : StoredCapability kind) :
    Finset RevocationKey :=
  insert (.capability stored.head.id)
    ((stored.head.ancestors.image RevocationKey.capability) ∪
      (stored.head.channels.image RevocationKey.channel))

/-- The revocation keys one address of a store contributes: a revoked or
registered key, or every key a stored capability names. -/
def keysAt (store : Store layout) : Address layout → Finset RevocationKey
  | ⟨.revoked, key⟩ => {key}
  | ⟨.registered, key⟩ => {key}
  | ⟨.capability kind, identifier⟩ =>
      match store ⟨.capability kind, identifier⟩ with
      | some stored => capabilityKeys (kind := kind) stored
      | none => ∅
  | _ => ∅

def revocationKeysOf (store : Store layout) : Finset RevocationKey :=
  store.support.biUnion (keysAt store)

end Snapshot

/-- The authorization projection of an authority cell: its revocation universe
is derived from the cell's own support (`Snapshot.revocationUniverse`). -/
def authStateOf (cell : Cell) : AuthState :=
  CredentialAuthorityState.authState ⟨Snapshot.revocationKeysOf cell.logical⟩ cell

/-- The deployment's authority domain: its domain digest, its one cell, and the
cell's authorization projection, computed once when the snapshot is built
(`authStateExact` pins it to `authStateOf`).  `revision` (the authority clock)
and `spent` (which operation markers are consumed) are the durable system
state's, carried here so every consumer of the snapshot reads the same
values; the receiver's `Loaded` pins both to the physical snapshot. -/
structure Snapshot where
  domain : Digest
  revision : Nat
  spent : Nat → Bool
  cell : Cell
  authState : AuthState
  authStateExact : authState = authStateOf cell

/-- The only constructor callers use. -/
def Snapshot.ofCell (domain : Digest) (revision : Nat) (spent : Nat → Bool) (cell : Cell) :
    Snapshot :=
  ⟨domain, revision, spent, cell, authStateOf cell, rfl⟩

/-! The projection's coordinates read the cell, whatever the snapshot's
provenance; these are what the definitional unfolding used to give. -/

@[simp] theorem Snapshot.authState_policyEpoch (snapshot : Snapshot) (policy : PolicyId) :
    snapshot.authState.policyEpoch policy = policyEpochAt snapshot.cell policy := by
  rw [snapshot.authStateExact]; rfl

@[simp] theorem Snapshot.authState_policyRevision (snapshot : Snapshot) (policy : PolicyId) :
    snapshot.authState.policyRevision policy = policyRevisionAt snapshot.cell policy := by
  rw [snapshot.authStateExact]; rfl

@[simp] theorem Snapshot.authState_issuerEpoch (snapshot : Snapshot) (issuer : IssuerId) :
    snapshot.authState.issuerEpoch issuer = issuerEpochAt snapshot.cell issuer := by
  rw [snapshot.authStateExact]; rfl

@[simp] theorem Snapshot.authState_subjectKeyEpoch (snapshot : Snapshot) (subject : SubjectId) :
    snapshot.authState.subjectKeyEpoch subject = subjectKeyEpochAt snapshot.cell subject := by
  rw [snapshot.authStateExact]; rfl

@[simp] theorem Snapshot.authState_policyAddress (snapshot : Snapshot) :
    snapshot.authState.policyAddress = policyAddressAt snapshot.cell := by
  rw [snapshot.authStateExact]; rfl

@[simp] theorem Snapshot.authState_roots (snapshot : Snapshot) :
    snapshot.authState.capabilityRoot = snapshot.cell.root ∧
      snapshot.authState.revocationRoot = snapshot.cell.root ∧
      snapshot.authState.policyRoot = snapshot.cell.root := by
  rw [snapshot.authStateExact]; exact ⟨rfl, rfl, rfl⟩

/-- A snapshot is its domain, clock, spent set and cell; the projection is
determined. -/
theorem Snapshot.ext_cell {left right : Snapshot} (domains : left.domain = right.domain)
    (revisions : left.revision = right.revision) (spents : left.spent = right.spent)
    (cells : left.cell = right.cell) : left = right := by
  cases left with
  | mk leftDomain leftRevision leftSpent leftCell leftState leftExact =>
      cases right with
      | mk rightDomain rightRevision rightSpent rightCell rightState rightExact =>
          simp only at domains revisions spents cells
          subst domains revisions spents cells
          have states : leftState = rightState := leftExact.trans rightExact.symm
          subst states
          rfl

namespace Snapshot

def logical (snapshot : Snapshot) : Store layout := snapshot.cell.logical

/-- The revocation universe is derived from the cell's own support: every
revoked key, every registered key, and every key a stored capability names
(the retired shard universe held exactly these). -/
def revocationUniverse (snapshot : Snapshot) : ProjectionUniverse :=
  ⟨revocationKeysOf snapshot.logical⟩

theorem mem_revocationKeysOf {store : Store layout} {address : Address layout}
    (present : store address ≠ none) {key : RevocationKey}
    (member : key ∈ keysAt store address) : key ∈ revocationKeysOf store :=
  Finset.mem_biUnion.mpr ⟨address, DFinsupp.mem_support_iff.mpr present, member⟩

/-- The universe is exactly: revoked, registered, or named by a stored
capability. -/
theorem mem_revocationUniverse_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ snapshot.revocationUniverse.revocationKeys ↔
      isRevoked snapshot.cell key = true ∨ isRegistered snapshot.cell key = true ∨
        ∃ (kind : ResourceKind) (identifier : CapabilityId) (stored : StoredCapability kind),
          readCapability snapshot.cell kind identifier = some stored ∧
            key ∈ capabilityKeys stored := by
  constructor
  · intro member
    obtain ⟨⟨plane, stored⟩, supported, contributes⟩ := Finset.mem_biUnion.mp member
    have present := DFinsupp.mem_support_iff.mp supported
    cases plane with
    | revoked =>
        have same : key = stored := Finset.mem_singleton.mp contributes
        subst same
        exact Or.inl (by simpa [isRevoked, Option.isSome_iff_ne_none] using present)
    | registered =>
        have same : key = stored := Finset.mem_singleton.mp contributes
        subst same
        exact Or.inr (Or.inl (by simpa [isRegistered, Option.isSome_iff_ne_none] using present))
    | capability kind =>
        right; right
        simp only [keysAt] at contributes
        cases read : snapshot.logical ⟨.capability kind, stored⟩ with
        | none => rw [read] at contributes; cases contributes
        | some capability =>
            rw [read] at contributes
            exact ⟨kind, stored, capability, read, contributes⟩
    | _ => cases contributes
  · rintro (revoked | registered | ⟨kind, identifier, stored, read, named⟩)
    · apply mem_revocationKeysOf (address := ⟨.revoked, key⟩)
        (by simpa [isRevoked, Option.isSome_iff_ne_none] using revoked)
      exact Finset.mem_singleton_self key
    · apply mem_revocationKeysOf (address := ⟨.registered, key⟩)
        (by simpa [isRegistered, Option.isSome_iff_ne_none] using registered)
      exact Finset.mem_singleton_self key
    · have present : snapshot.logical ⟨.capability kind, identifier⟩ = some stored := read
      apply mem_revocationKeysOf (address := ⟨.capability kind, identifier⟩)
        (by rw [present]; simp)
      simp only [keysAt, present]
      exact named

/-- Every key a stored capability names is in the universe: issuance makes a
capability's own key (and its ancestors' and channels') revocable. -/
theorem mem_revocationUniverse_of_stored (snapshot : Snapshot) {kind : ResourceKind}
    {identifier : CapabilityId} {stored : StoredCapability kind}
    (read : readCapability snapshot.cell kind identifier = some stored)
    {key : RevocationKey} (named : key ∈ capabilityKeys stored) :
    key ∈ snapshot.revocationUniverse.revocationKeys :=
  (snapshot.mem_revocationUniverse_iff key).mpr (Or.inr (Or.inr ⟨kind, identifier, stored, read, named⟩))

/-- Projected revocation membership is exactly the cell's read. -/
theorem mem_revoked_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ snapshot.authState.revoked ↔ isRevoked snapshot.cell key = true := by
  rw [snapshot.authStateExact, authStateOf, CredentialAuthorityState.mem_authState_revoked_iff]
  constructor
  · exact And.right
  · intro revoked
    exact ⟨(snapshot.mem_revocationUniverse_iff key).mpr (Or.inl revoked), revoked⟩

end Snapshot

/-! ## Loading the one cell -/

/-- Decode the deployment's authority cell.  The codec is canonical, so an
accepted cell re-encodes to exactly the loaded bytes (`load_bytes`). -/
def load (domain : Digest) (revision : Nat) (spent : Nat → Bool) (bytes : List UInt8) :
    Option Snapshot :=
  (CredentialAuthorityCell.materializer.codec.decode bytes).map fun store =>
    Snapshot.ofCell domain revision spent (materialize CredentialAuthorityCell.materializer store)

theorem load_bytes {domain : Digest} {revision : Nat} {spent : Nat → Bool}
    {bytes : List UInt8} {snapshot : Snapshot}
    (loaded : load domain revision spent bytes = some snapshot) :
    snapshot.cell.bytes = bytes ∧ snapshot.domain = domain := by
  unfold load at loaded
  cases decoded : CredentialAuthorityCell.materializer.codec.decode bytes with
  | none => simp [decoded] at loaded
  | some store =>
      simp only [decoded, Option.map_some, Option.some.injEq] at loaded
      subst loaded
      exact ⟨CredentialAuthorityCell.decode_canonical decoded, rfl⟩

theorem load_cell (domain : Digest) (revision : Nat) (spent : Nat → Bool) (cell : Cell) :
    load domain revision spent cell.bytes = some (Snapshot.ofCell domain revision spent cell) := by
  unfold load
  rw [CredentialAuthorityCell.cell_decode cell]
  rfl

/-- The retired catalogue frame (`LOOM/AUTH/DOMAIN` v2) refuses to load. -/
def retiredCatalogueFrame : List UInt8 := "LOOM/AUTH/DOMAIN".toUTF8.toList ++ [2]

theorem retired_catalogue_frame_refused (domain : Digest) (revision : Nat)
    (spent : Nat → Bool) (payload : List UInt8) :
    load domain revision spent (retiredCatalogueFrame ++ payload) = none := by
  have head : retiredCatalogueFrame = 76 :: retiredCatalogueFrame.drop 1 := by decide +kernel
  have refused : CredentialAuthorityCell.materializer.codec.decode
      (retiredCatalogueFrame ++ payload) = none := by
    rw [head, List.cons_append]
    exact StoreCodec.decode_other_first_byte CredentialAuthorityCell.wire 76
      (retiredCatalogueFrame.drop 1 ++ payload) (by decide)
  simp [load, refused]

/-! ## Policy heads and signing keys -/

/-- The current head of a policy: its generation must be present, and its
revision and that revision's address are read from the same store. -/
def headAt (logical : Store layout) (policy : PolicyId) : Option PolicyInstall.Head := do
  let _generation ← logical ⟨.policyEpoch, policy⟩
  let revision ← logical ⟨.policyRevision, policy⟩
  let address ← logical ⟨.policyAddress, (policy, revision)⟩
  some ⟨revision, address⟩

theorem headAt_missing_generation (logical : Store layout) (policy : PolicyId)
    (missing : logical ⟨.policyEpoch, policy⟩ = none) :
    headAt logical policy = none := by
  simp [headAt, missing]

theorem headAt_missing_revision (logical : Store layout) (policy : PolicyId)
    (missing : logical ⟨.policyRevision, policy⟩ = none) :
    headAt logical policy = none := by
  unfold headAt
  cases logical ⟨.policyEpoch, policy⟩ <;> simp [missing]

theorem headAt_exact (logical : Store layout) (policy : PolicyId) (head : PolicyInstall.Head)
    (current : headAt logical policy = some head) :
    (logical ⟨.policyEpoch, policy⟩).isSome ∧
      logical ⟨.policyRevision, policy⟩ = some head.version ∧
      logical ⟨.policyAddress, (policy, head.version)⟩ = some head.address := by
  unfold headAt at current
  cases generation : logical ⟨.policyEpoch, policy⟩ <;> simp [generation] at current
  cases revision : logical ⟨.policyRevision, policy⟩ <;> simp [revision] at current
  rename_i revisionValue
  cases address : logical ⟨.policyAddress, (policy, revisionValue)⟩ <;>
    simp [address] at current
  subst current
  exact ⟨rfl, rfl, address⟩

theorem headAt_of_fields (logical : Store layout) (policy : PolicyId)
    (generation : (logical ⟨.policyEpoch, policy⟩).isSome)
    (revision : PolicyRevision) (address : Digest)
    (revisionExact : logical ⟨.policyRevision, policy⟩ = some revision)
    (addressExact : logical ⟨.policyAddress, (policy, revision)⟩ = some address) :
    headAt logical policy = some ⟨revision, address⟩ := by
  obtain ⟨epoch, present⟩ := Option.isSome_iff_exists.mp generation
  unfold headAt
  simp only [bind, Option.bind, present, revisionExact]
  rw [addressExact]

def Snapshot.currentHead (snapshot : Snapshot) (policy : PolicyId) :
    Option PolicyInstall.Head := headAt snapshot.logical policy

def Snapshot.currentSigningKey (snapshot : Snapshot) (subject : SubjectId) :
    Option CredentialSigningKey.KeyRecord :=
  CredentialAuthorityState.currentSigningKey snapshot.logical subject

/-- The committed policy group: generation, revision and that revision's
address, all present in the one cell. -/
def Snapshot.policyContains (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest) : Prop :=
  (show Option Epoch from snapshot.logical ⟨.policyEpoch, policy⟩) = some generation ∧
    (show Option PolicyRevision from snapshot.logical ⟨.policyRevision, policy⟩) = some revision ∧
    (show Option Digest from snapshot.logical ⟨.policyAddress, (policy, revision)⟩) = some address

instance snapshotPolicyContainsDecidable (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest) :
    Decidable (snapshot.policyContains policy generation revision address) := by
  unfold Snapshot.policyContains
  infer_instance

theorem Snapshot.policy_exact (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest)
    (member : snapshot.policyContains policy generation revision address) :
    snapshot.currentHead policy = some ⟨revision, address⟩ :=
  headAt_of_fields _ _
    (by rw [show snapshot.logical ⟨.policyEpoch, policy⟩ = some generation from member.1]; rfl)
    revision address member.2.1 member.2.2

/-! ## Preparation: the guarded patch on the one cell -/

/-- A prepared authority update is the kernel's validated patch at the cell's
own root.  The post is derived from the patch; no caller supplies it. -/
structure Prepared (snapshot : Snapshot) (patch : Patch layout) : Type where
  validated : ValidatedPatch CredentialAuthorityCell.materializer snapshot.cell
    snapshot.cell.root patch

def prepare (snapshot : Snapshot) (patch : Patch layout) : Option (Prepared snapshot patch) :=
  match validate CredentialAuthorityCell.materializer snapshot.cell snapshot.cell.root patch with
  | .accepted validated => some ⟨validated⟩
  | .rejected _ => none

theorem prepare_valid_iff (snapshot : Snapshot) (patch : Patch layout) :
    (prepare snapshot patch).isSome ↔ Patch.ValidFrom snapshot.logical patch := by
  constructor
  · intro prepared
    unfold prepare at prepared
    split at prepared
    · rename_i validated _
      exact validated.valid
    · simp at prepared
  · intro valid
    obtain ⟨validated, accepted⟩ := validate_accepts CredentialAuthorityCell.materializer
      snapshot.cell snapshot.cell.root patch rfl valid
    simp [prepare, accepted]

theorem Prepared.frame {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) (address : Address layout)
    (outside : address ∉ Patch.writeFootprint patch) :
    prepared.validated.apply.logical address = snapshot.logical address := by
  rw [ValidatedPatch.apply_logical]
  exact Patch.run_frame _ patch address outside

/-! ### Policy installation -/

/-- Free the superseded revision's address when the revision changes. -/
def retirePolicy (logical : Store layout) (policy : PolicyId) (revision : PolicyRevision) :
    Patch layout :=
  match headAt logical policy with
  | some old =>
      if old.version = revision then []
      else [.free .policyAddress (policy, old.version) old.address]
  | none => []

def policyEntries (policy : PolicyId) (revision : PolicyRevision) (address : Digest) :
    List Entry :=
  [⟨⟨.policyRevision, policy⟩, revision⟩, ⟨⟨.policyAddress, (policy, revision)⟩, address⟩]

/-- Install `(revision, address)` as the policy's head.  The generation is
not written: it is framed. -/
def policyPatch (logical : Store layout) (policy : PolicyId) (revision : PolicyRevision)
    (address : Digest) : Patch layout :=
  let retire := retirePolicy logical policy revision
  retire ++ assignAll (Patch.run logical retire) (policyEntries policy revision address)

private theorem sigma_ne {a b : AuthorityPlane} {ka : a.Key} {kb : b.Key}
    (planes : a ≠ b) : (⟨a, ka⟩ : Address layout) ≠ ⟨b, kb⟩ := by
  intro same
  exact planes (congrArg Sigma.fst same)

theorem retirePolicy_valid (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) : Patch.ValidFrom logical (retirePolicy logical policy revision) := by
  unfold retirePolicy
  cases current : headAt logical policy with
  | none => trivial
  | some old =>
      simp only
      split
      · trivial
      · exact ⟨⟨rfl, (headAt_exact logical policy old current).2.2⟩, trivial⟩

theorem retirePolicy_run (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Address layout)
    (notRetired : ∀ old : PolicyInstall.Head, headAt logical policy = some old →
      old.version ≠ revision → address ≠ ⟨.policyAddress, (policy, old.version)⟩) :
    Patch.run logical (retirePolicy logical policy revision) address = logical address := by
  unfold retirePolicy
  cases current : headAt logical policy with
  | none => rfl
  | some old =>
      simp only
      split
      · rfl
      · rename_i different
        simp only [Patch.run_cons, Patch.run_nil, Op.apply]
        exact Store.set_ne _ _ _ _ (notRetired old current different)

theorem policyPatch_valid (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) :
    Patch.ValidFrom logical (policyPatch logical policy revision address) := by
  unfold policyPatch
  rw [Patch.validFrom_append]
  refine ⟨retirePolicy_valid logical policy revision, ?_⟩
  apply CredentialAuthorityEffects.assignAll_valid
  exact ⟨Or.inl rfl, Or.inl rfl, trivial⟩

theorem policyPatch_run (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) :
    Patch.run logical (policyPatch logical policy revision address) =
      setAll (Patch.run logical (retirePolicy logical policy revision))
        (policyEntries policy revision address) := by
  simp [policyPatch]

/-- The head after installation. -/
theorem policyPatch_head (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest)
    (generation : (logical ⟨.policyEpoch, policy⟩).isSome) :
    headAt (Patch.run logical (policyPatch logical policy revision address)) policy =
      some ⟨revision, address⟩ := by
  rw [policyPatch_run]
  apply headAt_of_fields
  · simp only [policyEntries, setAll]
    rw [Store.set_ne _ _ _ _ (sigma_ne (by decide)), Store.set_ne _ _ _ _ (sigma_ne (by decide)),
      retirePolicy_run logical policy revision _ (fun _ _ _ => sigma_ne (by decide))]
    exact generation
  · simp only [policyEntries, setAll]
    rw [Store.set_ne _ _ _ _ (sigma_ne (by decide)), Store.set_eq]; rfl
  · simp only [policyEntries, setAll]
    rw [Store.set_eq]; rfl

/-- The generation is framed. -/
theorem policyPatch_generation (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) :
    Patch.run logical (policyPatch logical policy revision address) ⟨.policyEpoch, policy⟩ =
      logical ⟨.policyEpoch, policy⟩ := by
  rw [policyPatch_run]
  simp only [policyEntries, setAll]
  rw [Store.set_ne _ _ _ _ (sigma_ne (by decide)), Store.set_ne _ _ _ _ (sigma_ne (by decide))]
  exact retirePolicy_run logical policy revision _ (fun _ _ _ => sigma_ne (by decide))

/-- The superseded revision's address is retired. -/
theorem policyPatch_retired_absent (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (old : PolicyInstall.Head)
    (current : headAt logical policy = some old) (different : old.version ≠ revision) :
    Patch.run logical (policyPatch logical policy revision address)
      ⟨.policyAddress, (policy, old.version)⟩ = none := by
  have distinct : (⟨.policyAddress, (policy, old.version)⟩ : Address layout) ≠
      ⟨.policyAddress, (policy, revision)⟩ := by
    intro same
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at same
    exact different (congrArg Prod.snd same)
  rw [policyPatch_run]
  simp only [policyEntries, setAll]
  rw [Store.set_ne _ _ _ _ distinct, Store.set_ne _ _ _ _ (sigma_ne (by decide))]
  simp [retirePolicy, current, different, Op.apply]

/-- A policy update prepared on the one cell.  The generation must already be
present and the policy must have a head: this path updates an existing policy;
initial policies are born with the domain.  The operation's single use is the
durable consumed set's (the receiver's intent nullifier), not a cell write. -/
structure PreparedPolicy (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) : Type where
  prepared : Prepared snapshot (policyPatch snapshot.logical policy revision address)
  headPresent : (snapshot.currentHead policy).isSome

def preparePolicy (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) :
    Option (PreparedPolicy snapshot policy revision address) :=
  if present : (snapshot.currentHead policy).isSome then
    (prepare snapshot (policyPatch snapshot.logical policy revision address)).map
      fun prepared => ⟨prepared, present⟩
  else none

/-- Satisfiable pole: an existing policy prepares. -/
theorem preparePolicy_isSome (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest)
    (present : (snapshot.currentHead policy).isSome) :
    (preparePolicy snapshot policy revision address).isSome := by
  have prepared := (prepare_valid_iff snapshot _).mpr
    (policyPatch_valid snapshot.logical policy revision address)
  simp only [preparePolicy, present, dite_true]
  simpa using prepared

/-- Refuting pole: a policy with no head is refused. -/
theorem preparePolicy_headless_refused (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest)
    (headless : snapshot.currentHead policy = none) :
    preparePolicy snapshot policy revision address = none := by
  simp [preparePolicy, headless]

namespace PreparedPolicy

variable {snapshot : Snapshot} {policy : PolicyId} {revision : PolicyRevision}
  {address : Digest}

def post (update : PreparedPolicy snapshot policy revision address) : Store layout :=
  update.prepared.validated.apply.logical

private theorem post_eq (update : PreparedPolicy snapshot policy revision address) :
    update.post = Patch.run snapshot.logical (policyPatch snapshot.logical policy revision address) := by
  simp only [post, ValidatedPatch.apply_logical]
  rfl

theorem head_exact (update : PreparedPolicy snapshot policy revision address) :
    headAt update.post policy = some ⟨revision, address⟩ := by
  obtain ⟨head, current⟩ := Option.isSome_iff_exists.mp update.headPresent
  have generation := (headAt_exact _ _ head current).1
  rw [post_eq]
  exact policyPatch_head snapshot.logical policy revision address generation

theorem generation_preserved (update : PreparedPolicy snapshot policy revision address) :
    update.post ⟨.policyEpoch, policy⟩ = snapshot.logical ⟨.policyEpoch, policy⟩ := by
  rw [post_eq]
  exact policyPatch_generation _ _ _ _

theorem retired_address_absent (update : PreparedPolicy snapshot policy revision address)
    (old : PolicyInstall.Head) (current : snapshot.currentHead policy = some old)
    (different : old.version ≠ revision) :
    update.post ⟨.policyAddress, (policy, old.version)⟩ = none := by
  rw [post_eq]
  exact policyPatch_retired_absent _ _ _ _ old current different

end PreparedPolicy

/-! ### Signing-key installation -/

/-- Free the superseded key record when the epoch changes. -/
def retireSigningKey (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    Patch layout :=
  match currentSigningKey logical ⟨key.subject⟩ with
  | some old =>
      if old.keyEpoch = key.keyEpoch then []
      else [.free .subjectKey (⟨key.subject⟩, old.keyEpoch) old]
  | none => []

def signingKeyEntries (key : CredentialSigningKey.KeyRecord) : List Entry :=
  [⟨⟨.subjectKeyEpoch, ⟨key.subject⟩⟩, key.keyEpoch⟩,
   ⟨⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩, key⟩]

def signingKeyPatch (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    Patch layout :=
  let retire := retireSigningKey logical key
  retire ++ assignAll (Patch.run logical retire) (signingKeyEntries key)

theorem retireSigningKey_valid (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    Patch.ValidFrom logical (retireSigningKey logical key) := by
  unfold retireSigningKey
  cases current : currentSigningKey logical ⟨key.subject⟩ with
  | none => trivial
  | some old =>
      simp only
      split
      · trivial
      · refine ⟨⟨rfl, ?_⟩, trivial⟩
        unfold currentSigningKey at current
        cases epoch : logical ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ <;>
          simp [epoch, bind, Option.bind] at current
        rename_i epochValue
        cases record : logical ⟨.subjectKey, (⟨key.subject⟩, epochValue)⟩ <;>
          simp [record] at current
        rename_i stored
        obtain ⟨⟨_, sameEpoch⟩, rfl⟩ := current
        rw [sameEpoch]
        exact record

theorem signingKeyPatch_valid (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    Patch.ValidFrom logical (signingKeyPatch logical key) := by
  unfold signingKeyPatch
  rw [Patch.validFrom_append]
  refine ⟨retireSigningKey_valid logical key, ?_⟩
  apply CredentialAuthorityEffects.assignAll_valid
  exact ⟨Or.inl rfl, Or.inl rfl, trivial⟩

/-- After installation the record is the subject's current signing key. -/
theorem signingKeyPatch_current (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    currentSigningKey (Patch.run logical (signingKeyPatch logical key)) ⟨key.subject⟩ =
      some key := by
  apply currentSigningKey_exact
  · simp only [signingKeyPatch, Patch.run_append, run_assignAll, signingKeyEntries, setAll]
    rw [Store.set_ne _ _ _ _ (sigma_ne (by decide)), Store.set_eq]; rfl
  · simp only [signingKeyPatch, Patch.run_append, run_assignAll, signingKeyEntries, setAll]
    rw [Store.set_eq]; rfl

def prepareSigningKey (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord) :
    Option (Prepared snapshot (signingKeyPatch snapshot.logical key)) :=
  prepare snapshot (signingKeyPatch snapshot.logical key)

/-- Satisfiable pole: every signing-key installation prepares. -/
theorem prepareSigningKey_isSome (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord) :
    (prepareSigningKey snapshot key).isSome :=
  (prepare_valid_iff snapshot _).mpr (signingKeyPatch_valid snapshot.logical key)

/-! ## Registration extends the universe without changing authorization -/

/-- Registering extra keys (not revoked) leaves the projected authorization
state unchanged: every live revocation is already in the derived universe. -/
theorem Snapshot.authState_extension_exact (snapshot : Snapshot)
    (additional : Finset RevocationKey) :
    CredentialAuthorityState.authState
        ⟨snapshot.revocationUniverse.revocationKeys ∪ additional⟩ snapshot.cell =
      snapshot.authState := by
  have revokedExact :
      (snapshot.revocationUniverse.revocationKeys ∪ additional).filter
          (fun key => isRevoked snapshot.cell key) =
        snapshot.revocationUniverse.revocationKeys.filter
          (fun key => isRevoked snapshot.cell key) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨_, live⟩
      exact ⟨(snapshot.mem_revocationUniverse_iff key).mpr (Or.inl live), live⟩
    · rintro ⟨registered, live⟩
      exact ⟨Or.inl registered, live⟩
  rw [snapshot.authStateExact]
  unfold CredentialAuthorityState.authState authStateOf
  dsimp only
  rw [revokedExact]
  rfl

/-! ## Worked instance (both poles) -/

namespace Witness

def policy : PolicyId := ⟨17⟩

/-- A domain with policy 17 at generation 1, revision 3. -/
def store : Store layout :=
  StoreCodec.fromEntries
    ([⟨⟨.policyEpoch, policy⟩, (1 : Nat)⟩,
      ⟨⟨.policyRevision, policy⟩, (3 : Nat)⟩,
      ⟨⟨.policyAddress, (policy, 3)⟩, (⟨3300⟩ : Digest)⟩] : List (StoreCodec.Entry layout))

def snapshot : Snapshot :=
  Snapshot.ofCell ⟨91⟩ 0 (fun _ => false) (materialize CredentialAuthorityCell.materializer store)

theorem head : snapshot.currentHead policy = some ⟨3, ⟨3300⟩⟩ := by decide

/-- Satisfiable pole: revision 4 of the present policy prepares. -/
theorem update_prepares : (preparePolicy snapshot policy 4 ⟨4400⟩).isSome :=
  preparePolicy_isSome snapshot policy 4 ⟨4400⟩ (by decide)

/-- Refuting pole: a policy the domain has no head for is refused. -/
theorem headless_refused : preparePolicy snapshot ⟨18⟩ 0 ⟨4400⟩ = none :=
  preparePolicy_headless_refused snapshot ⟨18⟩ 0 ⟨4400⟩ (by decide)

end Witness

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.load_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_bytes
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.retired_catalogue_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_catalogue_frame_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicy.head_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicy.head_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicy.retired_address_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicy.retired_address_absent
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.preparePolicy_headless_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparePolicy_headless_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.signingKeyPatch_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signingKeyPatch_current
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_revocationUniverse_of_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_revocationUniverse_of_stored
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_revocationUniverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_revocationUniverse_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_revoked_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.authState_extension_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.authState_extension_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Witness.update_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.update_prepares
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Witness.headless_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.headless_refused

end Minidregg.Compiler.CredentialAuthorityDomain
