/-
# Compiler.CredentialAuthorityDomain -- the authority domain as one cell

The authority domain is one store cell (`CredentialAuthorityCell`) at the
deployment's pinned `authorityCellId`, read in the deployment's domain.  There
is no catalogue, no shard, no routing and no placement: every authority record
is an address of `CredentialAuthorityState.layout`, and an update is one
guarded `Store.Patch` validated at the cell's own root.

A `Snapshot` pairs that cell with the domain that the receiving deployment
fixes (`CredentialAuthorityDomainReceiver.load`); nothing in a request chooses
either.  The revocation universe that `authState` projects over is derived
from the cell itself: every key present in the revocation or registration
planes, and every key a stored capability names.

The update builders below produce the patches that the policy-install and
key-enrollment controllers validate; the semantic authority families of
`Theory.CredentialAuthorityEffects` produce their own patches over the same
cell, so there is one post and nothing to join.
-/
import Compiler.CredentialAuthorityCell
import Theory.CredentialAuthorityEffects
import Theory.PolicyInstall

namespace Minidregg.Compiler.CredentialAuthorityDomain

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects (Entry assignOp assignOp_apply)
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev materializer : CredentialAuthorityState.Materializer := CredentialAuthorityCell.materializer
abbrev Cell := CredentialAuthorityCell.Cell

/-- The authority domain: the one cell, and the domain the receiving deployment
reads it in. -/
structure Snapshot where
  domain : Digest
  cell : Cell

def Snapshot.logical (snapshot : Snapshot) : Store layout := snapshot.cell.logical

@[simp] theorem Snapshot.cell_logical (snapshot : Snapshot) :
    snapshot.cell.logical = snapshot.logical := rfl

/-! ## The revocation universe, derived from the cell -/

def capabilityKeys {kind : ResourceKind} (stored : StoredCapability kind) : Finset RevocationKey :=
  insert (.capability stored.head.id)
    ((stored.head.ancestors.image RevocationKey.capability) ∪
      (stored.head.channels.image RevocationKey.channel))

/-- The revocation keys one present address contributes. -/
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

theorem mem_revocationKeysOf {store : Store layout} {address : Address layout}
    (present : store address ≠ none) {key : RevocationKey} (member : key ∈ keysAt store address) :
    key ∈ revocationKeysOf store :=
  Finset.mem_biUnion.mpr ⟨address, DFinsupp.mem_support_toFun _ _ |>.mpr present, member⟩

theorem revoked_mem_revocationKeysOf {store : Store layout} {key : RevocationKey}
    (present : store ⟨.revoked, key⟩ ≠ none) : key ∈ revocationKeysOf store :=
  mem_revocationKeysOf (address := ⟨.revoked, key⟩) present (Finset.mem_singleton_self key)

theorem registered_mem_revocationKeysOf {store : Store layout} {key : RevocationKey}
    (present : store ⟨.registered, key⟩ ≠ none) : key ∈ revocationKeysOf store :=
  mem_revocationKeysOf (address := ⟨.registered, key⟩) present (Finset.mem_singleton_self key)

def Snapshot.revocationUniverse (snapshot : Snapshot) : ProjectionUniverse :=
  ⟨revocationKeysOf snapshot.logical⟩

def Snapshot.authState (snapshot : Snapshot) : AuthState :=
  CredentialAuthorityState.authState snapshot.revocationUniverse snapshot.cell

/-- Every revoked key is in the derived universe: the projection cannot forget
a revocation. -/
theorem Snapshot.revocation_absent_of_outside (snapshot : Snapshot) (key : RevocationKey)
    (outside : key ∉ snapshot.revocationUniverse.revocationKeys) :
    snapshot.logical ⟨.revoked, key⟩ = none := by
  by_contra present
  exact outside (revoked_mem_revocationKeysOf present)

theorem Snapshot.revocation_false_of_outside (snapshot : Snapshot) (key : RevocationKey)
    (outside : key ∉ snapshot.revocationUniverse.revocationKeys) :
    isRevoked snapshot.cell key = false := by
  change (snapshot.logical ⟨.revoked, key⟩).isSome = false
  rw [snapshot.revocation_absent_of_outside key outside]
  rfl

/-- Every revoked key of the cell is projected as revoked. -/
theorem Snapshot.mem_authState_revoked_iff (snapshot : Snapshot) (key : RevocationKey) :
    key ∈ snapshot.authState.revoked ↔ isRevoked snapshot.cell key = true := by
  unfold Snapshot.authState
  rw [CredentialAuthorityState.mem_authState_revoked_iff]
  constructor
  · exact fun both => both.2
  · intro revoked
    refine ⟨?_, revoked⟩
    apply revoked_mem_revocationKeysOf
    intro absent
    change (snapshot.logical ⟨.revoked, key⟩).isSome = true at revoked
    rw [absent] at revoked
    cases revoked

def Snapshot.extendedUniverse (snapshot : Snapshot) (additional : Finset RevocationKey) :
    ProjectionUniverse :=
  ⟨snapshot.revocationUniverse.revocationKeys ∪ additional⟩

/-- Extending the universe with fresh self keys changes no authorization field:
the derived universe already holds every revoked key. -/
theorem Snapshot.authState_extension_exact (snapshot : Snapshot)
    (additional : Finset RevocationKey) :
    CredentialAuthorityState.authState (snapshot.extendedUniverse additional) snapshot.cell =
      snapshot.authState := by
  have revokedExact :
      (snapshot.revocationUniverse.revocationKeys ∪ additional).filter
          (fun key => isRevoked snapshot.cell key) =
        snapshot.revocationUniverse.revocationKeys.filter
          (fun key => isRevoked snapshot.cell key) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨registered | added, live⟩
      · exact ⟨registered, live⟩
      · by_cases registered : key ∈ snapshot.revocationUniverse.revocationKeys
        · exact ⟨registered, live⟩
        · rw [snapshot.revocation_false_of_outside key registered] at live
          contradiction
    · rintro ⟨registered, live⟩
      exact ⟨Or.inl registered, live⟩
  unfold CredentialAuthorityState.authState Snapshot.authState Snapshot.extendedUniverse
  dsimp only
  rw [revokedExact]
  rfl

/-! ## Policy heads and signing keys -/

def headAt (logical : Store layout) (policy : PolicyId) : Option PolicyInstall.Head := do
  let _generation ← logical ⟨.policyEpoch, policy⟩
  let revision ← logical ⟨.policyRevision, policy⟩
  let address ← logical ⟨.policyAddress, (policy, revision)⟩
  some ⟨revision, address⟩

theorem headAt_missing_generation (logical : Store layout) (policy : PolicyId)
    (missing : logical ⟨.policyEpoch, policy⟩ = none) : headAt logical policy = none := by
  simp [headAt, missing]

theorem headAt_missing_revision (logical : Store layout) (policy : PolicyId)
    (missing : logical ⟨.policyRevision, policy⟩ = none) : headAt logical policy = none := by
  unfold headAt
  cases logical ⟨.policyEpoch, policy⟩ <;> simp [missing]

theorem headAt_exact (logical : Store layout) (policy : PolicyId) (generation : Epoch)
    (revision : PolicyRevision) (address : Digest)
    (generationAt : logical ⟨.policyEpoch, policy⟩ = some generation)
    (revisionAt : logical ⟨.policyRevision, policy⟩ = some revision)
    (addressAt : logical ⟨.policyAddress, (policy, revision)⟩ = some address) :
    headAt logical policy = some ⟨revision, address⟩ := by
  unfold headAt
  rw [generationAt, revisionAt]
  show (logical ⟨.policyAddress, (policy, revision)⟩ >>= fun address =>
    some (⟨revision, address⟩ : PolicyInstall.Head)) = _
  rw [addressAt]
  rfl

theorem headAt_some {logical : Store layout} {policy : PolicyId} {head : PolicyInstall.Head}
    (current : headAt logical policy = some head) :
    (logical ⟨.policyEpoch, policy⟩).isSome ∧
      logical ⟨.policyRevision, policy⟩ = some head.version ∧
      logical ⟨.policyAddress, (policy, head.version)⟩ = some head.address := by
  unfold headAt at current
  cases generation : logical ⟨.policyEpoch, policy⟩ <;>
    cases revision : logical ⟨.policyRevision, policy⟩ <;>
    simp_all [bind, Option.bind]
  rename_i revisionValue
  cases address : logical ⟨.policyAddress, (policy, revisionValue)⟩ <;> simp_all
  cases current
  constructor <;> first | rfl | assumption

def Snapshot.currentHead (snapshot : Snapshot) (policy : PolicyId) : Option PolicyInstall.Head :=
  headAt snapshot.logical policy

def Snapshot.currentSigningKey (snapshot : Snapshot) (subject : SubjectId) :
    Option CredentialSigningKey.KeyRecord :=
  CredentialAuthorityState.currentSigningKey snapshot.logical subject

/-- The current policy record at exactly these coordinates. -/
def generationAt? (logical : Store layout) (policy : PolicyId) : Option Epoch :=
  logical ⟨.policyEpoch, policy⟩

def revisionAt? (logical : Store layout) (policy : PolicyId) : Option PolicyRevision :=
  logical ⟨.policyRevision, policy⟩

def addressAt? (logical : Store layout) (policy : PolicyId) (revision : PolicyRevision) :
    Option Digest :=
  logical ⟨.policyAddress, (policy, revision)⟩

def Snapshot.policyContains (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest) : Prop :=
  generationAt? snapshot.logical policy = some generation ∧
    revisionAt? snapshot.logical policy = some revision ∧
    addressAt? snapshot.logical policy revision = some address

instance snapshotPolicyContainsDecidable (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest) :
    Decidable (snapshot.policyContains policy generation revision address) := by
  unfold Snapshot.policyContains
  infer_instance

theorem Snapshot.policy_exact (snapshot : Snapshot) (policy : PolicyId)
    (generation : Epoch) (revision : PolicyRevision) (address : Digest)
    (member : snapshot.policyContains policy generation revision address) :
    snapshot.currentHead policy = some ⟨revision, address⟩ :=
  headAt_exact _ _ _ _ _ member.1 member.2.1 member.2.2

/-! ## Prepared updates: one patch, validated at the cell's own root -/

/-- A prepared update is the validator's token for a patch generated from this
snapshot, quoted at the cell's own root.  It carries no authorization. -/
structure Prepared (snapshot : Snapshot) (patch : Patch layout) : Type where
  private mk ::
  validated : ValidatedPatch materializer snapshot.cell snapshot.cell.root patch

def prepare (snapshot : Snapshot) (patch : Patch layout) : Option (Prepared snapshot patch) :=
  match validate materializer snapshot.cell snapshot.cell.root patch with
  | .rejected _ => none
  | .accepted validated => some ⟨validated⟩

theorem prepare_isSome_iff (snapshot : Snapshot) (patch : Patch layout) :
    (prepare snapshot patch).isSome ↔ Patch.ValidFrom snapshot.logical patch := by
  unfold prepare
  constructor
  · intro some
    split at some
    · cases some
    · rename_i validated _
      exact validated.valid
  · intro valid
    obtain ⟨validated, accepted⟩ :=
      validate_accepts materializer snapshot.cell snapshot.cell.root patch rfl valid
    rw [accepted]
    rfl

def Prepared.postCell {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) : Cell :=
  prepared.validated.apply

def Prepared.postLogical {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) : Store layout :=
  prepared.postCell.logical

@[simp] theorem Prepared.postLogical_run {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) :
    prepared.postLogical = Patch.run snapshot.logical patch := rfl

theorem Prepared.frame {snapshot : Snapshot} {patch : Patch layout}
    (prepared : Prepared snapshot patch) (address : Address layout)
    (outside : address ∉ Patch.writeFootprint patch) :
    prepared.postLogical address = snapshot.logical address :=
  Patch.run_frame _ _ _ outside

/-! ## Policy succession -/

/-- Replace the current head of `policy` by `(revision, address)`: the revision
moves under its exact prior value, the retired revision's address is freed at
its exact prior value, and the new address is assigned.  The generation is not
touched. -/
def policySuccession (logical : Store layout) (policy : PolicyId) (old : PolicyInstall.Head)
    (revision : PolicyRevision) (address : Digest) : Patch layout :=
  let retired := (logical.set ⟨.policyRevision, policy⟩ (some revision)).set
    ⟨.policyAddress, (policy, old.version)⟩ none
  [.write .policyRevision policy old.version revision,
    .free .policyAddress (policy, old.version) old.address,
    assignOp retired ⟨.policyAddress, (policy, revision)⟩ address]

def nullifierOp (operationNullifier : Nat) : Op layout :=
  .allocate .nullifier operationNullifier ()

def policyAndNullifierPatch (logical : Store layout) (policy : PolicyId) (old : PolicyInstall.Head)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) : Patch layout :=
  policySuccession logical policy old revision address ++ [nullifierOp nullifierId]

theorem run_policyAndNullifierPatch (logical : Store layout) (policy : PolicyId)
    (old : PolicyInstall.Head) (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) :
    Patch.run logical (policyAndNullifierPatch logical policy old revision address nullifierId) =
      ((((logical.set ⟨.policyRevision, policy⟩ (some revision)).set
        ⟨.policyAddress, (policy, old.version)⟩ none).set
          ⟨.policyAddress, (policy, revision)⟩ (some address)).set
            ⟨.nullifier, nullifierId⟩ (some ())) := by
  unfold policyAndNullifierPatch policySuccession nullifierOp
  change ((assignOp ((logical.set ⟨.policyRevision, policy⟩ (some revision)).set
      ⟨.policyAddress, (policy, old.version)⟩ none) ⟨.policyAddress, (policy, revision)⟩ address).apply
        ((logical.set ⟨.policyRevision, policy⟩ (some revision)).set
          ⟨.policyAddress, (policy, old.version)⟩ none)).set ⟨.nullifier, nullifierId⟩ (some ()) = _
  rw [assignOp_apply]

/-- One grouped authority update: the succession of one policy head and one
fresh operation nullifier, validated at the snapshot's own root. -/
structure PreparedPolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) where
  old : PolicyInstall.Head
  current : snapshot.currentHead policy = some old
  prepared : Prepared snapshot
    (policyAndNullifierPatch snapshot.logical policy old revision address nullifierId)
  nullifierFresh : isNullified snapshot.cell nullifierId = false

def preparePolicyAndNullifier (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat) :
    Option (PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :=
  match current : snapshot.currentHead policy with
  | none => none
  | some old =>
      if fresh : isNullified snapshot.cell nullifierId = false then
        match prepare snapshot
            (policyAndNullifierPatch snapshot.logical policy old revision address nullifierId) with
        | none => none
        | some prepared => some ⟨old, current, prepared, fresh⟩
      else none

section PolicyAndNullifier

variable {snapshot : Snapshot} {policy : PolicyId} {revision : PolicyRevision}
  {address : Digest} {nullifierId : Nat}

private theorem post_eq (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.prepared.postLogical =
      ((((snapshot.logical.set ⟨.policyRevision, policy⟩ (some revision)).set
        ⟨.policyAddress, (policy, update.old.version)⟩ none).set
          ⟨.policyAddress, (policy, revision)⟩ (some address)).set
            ⟨.nullifier, nullifierId⟩ (some ())) := by
  rw [Prepared.postLogical_run, run_policyAndNullifierPatch]

private theorem set_other {store : Store layout} {address other : Address layout}
    {value : Option (layout.Value address.1)} (different : other ≠ address) :
    store.set address value other = store other := Store.set_ne _ _ _ _ different

theorem PreparedPolicyAndNullifier.head_exact
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    headAt update.prepared.postLogical policy = some ⟨revision, address⟩ := by
  obtain ⟨generation, _, _⟩ := headAt_some update.current
  rw [post_eq]
  obtain ⟨generationValue, generationAt⟩ := Option.isSome_iff_exists.mp generation
  apply headAt_exact _ _ generationValue
  · rw [set_other (by simp), set_other (by simp), set_other (by simp), set_other (by simp)]
    exact generationAt
  · rw [set_other (by simp), set_other (by simp), set_other (by simp), Store.set_eq]
    rfl
  · rw [set_other (by simp), Store.set_eq]
    rfl

theorem PreparedPolicyAndNullifier.generation_preserved
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.prepared.postLogical ⟨.policyEpoch, policy⟩ = snapshot.logical ⟨.policyEpoch, policy⟩ := by
  rw [post_eq, set_other (by simp), set_other (by simp), set_other (by simp), set_other (by simp)]

theorem PreparedPolicyAndNullifier.nullifier_consumed
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId) :
    update.prepared.postLogical ⟨.nullifier, nullifierId⟩ = some () := by
  rw [post_eq, Store.set_eq]
  rfl

theorem PreparedPolicyAndNullifier.retired_address_absent
    (update : PreparedPolicyAndNullifier snapshot policy revision address nullifierId)
    (different : update.old.version ≠ revision) :
    update.prepared.postLogical ⟨.policyAddress, (policy, update.old.version)⟩ = none := by
  rw [post_eq, set_other (by simp), set_other, Store.set_eq]
  intro same
  exact different (Prod.ext_iff.mp (eq_of_heq (Sigma.mk.inj same).2)).2

/-- Refuting pole: a spent operation nullifier is never prepared. -/
theorem preparePolicyAndNullifier_used_refused (snapshot : Snapshot) (policy : PolicyId)
    (revision : PolicyRevision) (address : Digest) (nullifierId : Nat)
    (used : isNullified snapshot.cell nullifierId = true) :
    preparePolicyAndNullifier snapshot policy revision address nullifierId = none := by
  unfold preparePolicyAndNullifier
  split
  · rfl
  · simp [used]

end PolicyAndNullifier

/-! ## Signing-key installation -/

/-- The retired record of the subject's current epoch, freed at its exact value. -/
def signingKeyRetire (logical : Store layout) (key : CredentialSigningKey.KeyRecord) : Patch layout :=
  match logical ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ with
  | none => []
  | some epoch =>
      match logical ⟨.subjectKey, (⟨key.subject⟩, epoch)⟩ with
      | none => []
      | some old => [.free .subjectKey (⟨key.subject⟩, epoch) old]

/-- Install `key` as its subject's current key: the retired record (if any) is
freed at its exact value, the epoch moves under its exact prior value (or is
allocated), and the record is assigned. -/
def signingKeyPatch (logical : Store layout) (key : CredentialSigningKey.KeyRecord) : Patch layout :=
  let retired := Patch.run logical (signingKeyRetire logical key)
  signingKeyRetire logical key ++
    [assignOp retired ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ key.keyEpoch,
      assignOp (retired.set ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ (some key.keyEpoch))
        ⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩ key]

theorem signingKeyPatch_run (logical : Store layout) (key : CredentialSigningKey.KeyRecord) :
    Patch.run logical (signingKeyPatch logical key) =
      ((Patch.run logical (signingKeyRetire logical key)).set
        ⟨.subjectKeyEpoch, ⟨key.subject⟩⟩ (some key.keyEpoch)).set
          ⟨.subjectKey, (⟨key.subject⟩, key.keyEpoch)⟩ (some key) := by
  unfold signingKeyPatch
  simp only [Patch.run_append, Patch.run_cons, Patch.run_nil, assignOp_apply]

def prepareSigningKey (snapshot : Snapshot) (key : CredentialSigningKey.KeyRecord) :
    Option (Prepared snapshot (signingKeyPatch snapshot.logical key)) :=
  prepare snapshot (signingKeyPatch snapshot.logical key)

theorem preparedSigningKey_exact {snapshot : Snapshot} {key : CredentialSigningKey.KeyRecord}
    (prepared : Prepared snapshot (signingKeyPatch snapshot.logical key)) :
    CredentialAuthorityState.currentSigningKey prepared.postLogical ⟨key.subject⟩ = some key := by
  rw [Prepared.postLogical_run, signingKeyPatch_run]
  apply CredentialAuthorityState.currentSigningKey_exact
  · rw [Store.set_ne _ _ _ _ (by simp), Store.set_eq]
    rfl
  · rw [Store.set_eq]
    rfl

/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.authState_extension_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.authState_extension_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.Snapshot.mem_authState_revoked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.mem_authState_revoked_iff
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicyAndNullifier.head_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicyAndNullifier.head_exact
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.PreparedPolicyAndNullifier.retired_address_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedPolicyAndNullifier.retired_address_absent
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.preparePolicyAndNullifier_used_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparePolicyAndNullifier_used_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityDomain.preparedSigningKey_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedSigningKey_exact

end Minidregg.Compiler.CredentialAuthorityDomain
