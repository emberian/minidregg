/-
# Compiler.CredentialAuthorityDomain -- the authority domain is one cell

The authority domain of a deployment is ONE store cell
(`CredentialAuthorityCell`): a `Store` over `CredentialAuthorityState.layout`
at the declared `StoreCodec` wire.  There is no catalogue, no shard, no
routing of entry groups to pages and no second view of the same store.

A `Snapshot` is the deployment's domain digest together with that one cell.
Everything a consumer reads is read from the cell:

* the revocation universe is the keys of the `revoked` and `registered`
  planes in the cell's finite support, so no caller-authored list can omit a
  live revocation (`mem_revoked_iff`), and a registered, unrevoked key is in
  the universe (`mem_revocationUniverse_iff`), which is how families read
  registration;
* the authority clock (`Snapshot.revision`) is the number of spent operation
  nullifiers.  The nullifier plane is append-only, so the clock never runs
  backwards under any valid patch (`revision_monotone`) and every accepted
  operation that spends a fresh nullifier advances it (`revision_advances`).
  It replaces the retired catalogue's revision counter;
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
  (Entry assignAll setAll run_assignAll nullifierEntry)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Cell := CredentialAuthorityCell.Cell

/-- The deployment's authority domain: its domain digest and its one cell. -/
structure Snapshot where
  domain : Digest
  cell : Cell

namespace Snapshot

def logical (snapshot : Snapshot) : Store layout := snapshot.cell.logical

/-- Every supported registration address contributes its key. -/
def registeredAt : Address layout → Finset RevocationKey
  | ⟨.registered, key⟩ => {key}
  | _ => ∅

/-- The keys the cell registers. -/
def registeredKeys (snapshot : Snapshot) : Finset RevocationKey :=
  snapshot.cell.logical.support.biUnion registeredAt

/-- The revocation universe is derived from the cell's own support: every
revoked key and every registered key. -/
def revocationUniverse (snapshot : Snapshot) : ProjectionUniverse :=
  ⟨CanonicalAuthorityProjection.revocationKeys snapshot.cell ∪ registeredKeys snapshot⟩

theorem mem_registeredKeys_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ registeredKeys snapshot ↔ isRegistered snapshot.cell key = true := by
  constructor
  · rw [registeredKeys, Finset.mem_biUnion]
    rintro ⟨⟨plane, stored⟩, supported, contributes⟩
    cases plane <;> simp [registeredAt] at contributes
    have same : key = stored := Finset.mem_singleton.mp contributes
    subst same
    have present := DFinsupp.mem_support_iff.mp supported
    simp only [isRegistered, Option.isSome_iff_ne_none]
    exact present
  · intro registered
    rw [registeredKeys, Finset.mem_biUnion]
    refine ⟨⟨.registered, key⟩, ?_, Finset.mem_singleton_self key⟩
    rw [DFinsupp.mem_support_iff]
    simpa [isRegistered, Option.isSome_iff_ne_none] using registered

theorem mem_revocationUniverse_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ snapshot.revocationUniverse.revocationKeys ↔
      isRevoked snapshot.cell key = true ∨ isRegistered snapshot.cell key = true := by
  change key ∈ CanonicalAuthorityProjection.revocationKeys snapshot.cell ∪
    registeredKeys snapshot ↔ _
  rw [Finset.mem_union, mem_registeredKeys_iff, CanonicalAuthorityProjection.mem_revocationKeys_iff]
  constructor
  · rintro (supported | registered)
    · left
      have present := DFinsupp.mem_support_iff.mp supported
      simpa [isRevoked, Option.isSome_iff_ne_none] using present
    · exact Or.inr registered
  · rintro (revoked | registered)
    · exact Or.inl (CanonicalAuthorityProjection.supported_of_isRevoked snapshot.cell key revoked)
    · exact Or.inr registered

def authState (snapshot : Snapshot) : AuthState :=
  CredentialAuthorityState.authState snapshot.revocationUniverse snapshot.cell

/-- Projected revocation membership is exactly the cell's read. -/
theorem mem_revoked_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ snapshot.authState.revoked ↔ isRevoked snapshot.cell key = true := by
  rw [authState, CredentialAuthorityState.mem_authState_revoked_iff, mem_revocationUniverse_iff]
  constructor
  · exact And.right
  · intro revoked
    exact ⟨Or.inl revoked, revoked⟩

end Snapshot

/-! ## Loading the one cell -/

/-- Decode the deployment's authority cell.  The codec is canonical, so an
accepted cell re-encodes to exactly the loaded bytes (`load_bytes`). -/
def load (domain : Digest) (bytes : List UInt8) : Option Snapshot :=
  (CredentialAuthorityCell.materializer.codec.decode bytes).map fun store =>
    ⟨domain, materialize CredentialAuthorityCell.materializer store⟩

theorem load_bytes {domain : Digest} {bytes : List UInt8} {snapshot : Snapshot}
    (loaded : load domain bytes = some snapshot) :
    snapshot.cell.bytes = bytes ∧ snapshot.domain = domain := by
  unfold load at loaded
  cases decoded : CredentialAuthorityCell.materializer.codec.decode bytes with
  | none => simp [decoded] at loaded
  | some store =>
      simp only [decoded, Option.map_some, Option.some.injEq] at loaded
      subst loaded
      exact ⟨CredentialAuthorityCell.decode_canonical decoded, rfl⟩

theorem load_cell (domain : Digest) (cell : Cell) :
    load domain cell.bytes = some ⟨domain, cell⟩ := by
  unfold load
  rw [CredentialAuthorityCell.cell_decode cell]
  rfl

/-- The retired catalogue frame (`LOOM/AUTH/DOMAIN` v2) refuses to load. -/
def retiredCatalogueFrame : List UInt8 := "LOOM/AUTH/DOMAIN".toUTF8.toList ++ [2]

theorem retired_catalogue_frame_refused (domain : Digest) (payload : List UInt8) :
    load domain (retiredCatalogueFrame ++ payload) = none := by
  have head : retiredCatalogueFrame = 76 :: retiredCatalogueFrame.drop 1 := by decide +kernel
  have refused : CredentialAuthorityCell.materializer.codec.decode
      (retiredCatalogueFrame ++ payload) = none := by
    rw [head, List.cons_append]
    exact StoreCodec.decode_other_first_byte CredentialAuthorityCell.wire 76
      (retiredCatalogueFrame.drop 1 ++ payload) (by decide)
  simp [load, refused]

/-! ## The authority clock -/

/-- The spent operation nullifiers of a store. -/
def spent (store : Store layout) : Finset (Address layout) :=
  store.support.filter fun address => address.1 = .nullifier

/-- The authority clock: how many single-use operations this domain has
spent.  It is committed state (the append-only nullifier plane), never a
counter a caller supplies. -/
def revisionOf (store : Store layout) : Nat := (spent store).card

def Snapshot.revision (snapshot : Snapshot) : Nat := revisionOf snapshot.logical

theorem mem_spent_iff (store : Store layout) (address : Address layout) :
    address ∈ spent store ↔ address.1 = .nullifier ∧ store address ≠ none := by
  simp only [spent, Finset.mem_filter, DFinsupp.mem_support_iff]
  exact and_comm

theorem spent_subset (store : Store layout) (patch : Patch layout)
    (valid : Patch.ValidFrom store patch) : spent store ⊆ spent (Patch.run store patch) := by
  intro address member
  rw [mem_spent_iff] at member ⊢
  obtain ⟨⟨plane, id⟩, rfl⟩ : ∃ a : Address layout, a = address := ⟨address, rfl⟩
  obtain ⟨plane, present⟩ := member
  cases plane
  refine ⟨rfl, ?_⟩
  obtain ⟨value, isSome⟩ := Option.ne_none_iff_exists'.mp present
  rw [Patch.appendOnly_present_preserved store patch ⟨.nullifier, id⟩ value valid rfl isSome]
  simp

/-- The clock never runs backwards under a valid patch. -/
theorem revision_monotone (store : Store layout) (patch : Patch layout)
    (valid : Patch.ValidFrom store patch) :
    revisionOf store ≤ revisionOf (Patch.run store patch) :=
  Finset.card_le_card (spent_subset store patch valid)

/-- A valid patch whose post spends a nullifier the pre had not spent
advances the clock. -/
theorem revision_advances (store : Store layout) (patch : Patch layout)
    (valid : Patch.ValidFrom store patch) (id : Nat)
    (fresh : store ⟨.nullifier, id⟩ = none)
    (spentAfter : Patch.run store patch ⟨.nullifier, id⟩ = some ()) :
    revisionOf store < revisionOf (Patch.run store patch) := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨spent_subset store patch valid, fun same => ?_⟩
  have inPost : (⟨.nullifier, id⟩ : Address layout) ∈ spent (Patch.run store patch) :=
    (mem_spent_iff _ _).mpr ⟨rfl, by rw [spentAfter]; simp⟩
  rw [← same, mem_spent_iff] at inPost
  exact inPost.2 fresh

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

/-- The prepared post as a snapshot of the same domain. -/
def Prepared.post {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) : Snapshot :=
  ⟨snapshot.domain, prepared.validated.apply⟩

theorem Prepared.revision_monotone {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) : snapshot.revision ≤ prepared.post.revision :=
  CredentialAuthorityDomain.revision_monotone _ patch prepared.validated.valid

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

/-- Policy installation plus the operation's single-use nullifier. -/
def policyAndNullifierPatch (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) : Patch layout :=
  policyPatch logical policy revision address ++ [.allocate .nullifier nullifierId ()]

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

theorem policyAndNullifierPatch_valid_iff (logical : Store layout) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) :
    Patch.ValidFrom logical (policyAndNullifierPatch logical policy revision address nullifierId) ↔
      logical ⟨.nullifier, nullifierId⟩ = none := by
  unfold policyAndNullifierPatch
  rw [Patch.validFrom_append]
  have untouched : Patch.run logical (policyPatch logical policy revision address)
      ⟨.nullifier, nullifierId⟩ = logical ⟨.nullifier, nullifierId⟩ := by
    rw [policyPatch_run]
    simp only [policyEntries, setAll]
    rw [Store.set_ne _ _ _ _ (sigma_ne (by decide)), Store.set_ne _ _ _ _ (sigma_ne (by decide))]
    exact retirePolicy_run logical policy revision _ (fun _ _ _ => sigma_ne (by decide))
  constructor
  · rintro ⟨_, enabled, _⟩
    exact untouched ▸ enabled.2
  · intro fresh
    refine ⟨policyPatch_valid logical policy revision address, ⟨by decide, ?_⟩, trivial⟩
    exact untouched.trans fresh

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

/-- A policy update with its operation nullifier, prepared on the one cell.
The generation must already be present and the policy must have a head: this
path updates an existing policy; initial policies are born with the domain. -/
structure PreparedPolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) : Type where
  prepared : Prepared snapshot
    (policyAndNullifierPatch snapshot.logical policy revision address nullifierId)
  nullifierFresh : isNullified snapshot.cell nullifierId = false
  headPresent : (snapshot.currentHead policy).isSome

def preparePolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) :
    Option (PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :=
  if fresh : isNullified snapshot.cell nullifierId = false then
    if present : (snapshot.currentHead policy).isSome then
      (prepare snapshot (policyAndNullifierPatch snapshot.logical policy revision address
        nullifierId)).map fun prepared => ⟨prepared, fresh, present⟩
    else none
  else none

/-- Satisfiable pole: an existing policy with an unspent nullifier prepares. -/
theorem preparePolicyAndNullifier_isSome (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat)
    (fresh : isNullified snapshot.cell nullifierId = false)
    (present : (snapshot.currentHead policy).isSome) :
    (preparePolicyAndNullifier snapshot policy revision address nullifierId).isSome := by
  have valid := (policyAndNullifierPatch_valid_iff snapshot.logical policy revision address
    nullifierId).mpr (by simpa [isNullified] using fresh)
  have prepared := (prepare_valid_iff snapshot _).mpr valid
  simp only [preparePolicyAndNullifier, fresh, present, dite_true]
  simpa using prepared

/-- Refuting pole: a spent nullifier is refused. -/
theorem preparePolicyAndNullifier_used_refused (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat)
    (used : isNullified snapshot.cell nullifierId = true) :
    preparePolicyAndNullifier snapshot policy revision address nullifierId = none := by
  simp [preparePolicyAndNullifier, used]

namespace PreparedPolicyAndNullifier

variable {snapshot : Snapshot} {policy : PolicyId} {revision : PolicyRevision}
  {address : Digest} {nullifierId : Nat}

def post (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    Store layout :=
  update.prepared.validated.apply.logical

private theorem post_eq
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.post = Patch.run
      (Patch.run snapshot.logical (policyPatch snapshot.logical policy revision address))
      [.allocate .nullifier nullifierId ()] := by
  simp only [post, ValidatedPatch.apply_logical, policyAndNullifierPatch, Patch.run_append]
  rfl

private theorem post_other
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId)
    (target : Address layout) (plane : target.1 ≠ .nullifier) :
    update.post target =
      Patch.run snapshot.logical (policyPatch snapshot.logical policy revision address) target := by
  rw [post_eq]
  simp only [Patch.run_cons, Patch.run_nil, Op.apply]
  exact Store.set_ne _ _ _ _ (fun same => plane (congrArg Sigma.fst same))

theorem head_exact
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    headAt update.post policy = some ⟨revision, address⟩ := by
  obtain ⟨head, current⟩ := Option.isSome_iff_exists.mp update.headPresent
  have generation := (headAt_exact _ _ head current).1
  have installed := policyPatch_head snapshot.logical policy revision address generation
  obtain ⟨epochPresent, revisionExact, addressExact⟩ := headAt_exact _ _ _ installed
  apply headAt_of_fields
  · rw [post_other update _ (by simp)]; exact epochPresent
  · rw [post_other update _ (by simp)]; exact revisionExact
  · rw [post_other update _ (by simp)]; exact addressExact

theorem generation_preserved
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.post ⟨.policyEpoch, policy⟩ = snapshot.logical ⟨.policyEpoch, policy⟩ := by
  rw [post_other update _ (by simp)]
  exact policyPatch_generation _ _ _ _

theorem nullifier_consumed
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.post ⟨.nullifier, nullifierId⟩ = some () := by
  rw [post_eq]
  simp only [Patch.run_cons, Patch.run_nil, Op.apply, Store.set_eq]
  rfl

theorem retired_address_absent
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId)
    (old : PolicyInstall.Head) (current : snapshot.currentHead policy = some old)
    (different : old.version ≠ revision) :
    update.post ⟨.policyAddress, (policy, old.version)⟩ = none := by
  rw [post_other update _ (by simp)]
  exact policyPatch_retired_absent _ _ _ _ old current different

/-- The operation advances the authority clock. -/
theorem revision_advances
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    snapshot.revision < update.prepared.post.revision := by
  apply CredentialAuthorityDomain.revision_advances _ _ update.prepared.validated.valid nullifierId
  · simpa [isNullified] using update.nullifierFresh
  · exact update.nullifier_consumed

end PreparedPolicyAndNullifier

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
  unfold CredentialAuthorityState.authState Snapshot.authState
  dsimp only
  rw [revokedExact]
  rfl

/-! ## Worked instance (both poles) -/

namespace Witness

def policy : PolicyId := ⟨17⟩

/-- A domain with policy 17 at generation 1, revision 3, one spent operation. -/
def store : Store layout :=
  StoreCodec.fromEntries
    ([⟨⟨.policyEpoch, policy⟩, (1 : Nat)⟩,
      ⟨⟨.policyRevision, policy⟩, (3 : Nat)⟩,
      ⟨⟨.policyAddress, (policy, 3)⟩, (⟨3300⟩ : Digest)⟩,
      ⟨⟨.nullifier, (5 : Nat)⟩, ()⟩] : List (StoreCodec.Entry layout))

def snapshot : Snapshot := ⟨⟨91⟩, materialize CredentialAuthorityCell.materializer store⟩

theorem head : snapshot.currentHead policy = some ⟨3, ⟨3300⟩⟩ := by decide

theorem revision_one : snapshot.revision = 1 := by decide +kernel

/-- Satisfiable pole: revision 4 with a fresh nullifier prepares. -/
theorem update_prepares :
    (preparePolicyAndNullifier snapshot policy 4 ⟨4400⟩ 6).isSome :=
  preparePolicyAndNullifier_isSome snapshot policy 4 ⟨4400⟩ 6 (by decide) (by decide)

/-- Refuting pole: replaying the spent nullifier is refused. -/
theorem replay_refused :
    preparePolicyAndNullifier snapshot policy 4 ⟨4400⟩ 5 = none :=
  preparePolicyAndNullifier_used_refused snapshot policy 4 ⟨4400⟩ 5 (by decide)

end Witness

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.load_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_bytes
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.retired_catalogue_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_catalogue_frame_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.revision_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revision_monotone
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.revision_advances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revision_advances
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.policyAndNullifierPatch_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms policyAndNullifierPatch_valid_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicyAndNullifier.head_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicyAndNullifier.head_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicyAndNullifier.retired_address_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicyAndNullifier.retired_address_absent
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.preparePolicyAndNullifier_used_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparePolicyAndNullifier_used_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.signingKeyPatch_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signingKeyPatch_current
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_revocationUniverse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_revocationUniverse_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_revoked_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.authState_extension_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.authState_extension_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Witness.update_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.update_prepares
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Witness.replay_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.replay_refused

end Minidregg.Compiler.CredentialAuthorityDomain
