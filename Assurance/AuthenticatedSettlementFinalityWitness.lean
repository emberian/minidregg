/-
# Assurance.AuthenticatedSettlementFinalityWitness -- exact key-bound quorum

This witness joins `AuthenticatedSettlementFinality` to finite sparse
`CredentialAuthorityState` cells.  Three replica identities are selected under
one exact canonical authority root, current subject-key epochs, a versioned
governance-policy address, and a registered live revocation channel.  Their
signed payloads retain exact candidate bytes and the derived log slot.

The signature bytes are supplied only through `VerifiedSignatureBoundary`.
No verifier or EUF theorem is fabricated here.  Likewise the final safety
theorem requires the kernel's explicit origin, no-EUF-break, and issuance
discipline premises.  Closed stale-key, stale-policy, replay-after-revocation,
wrong-root, wrong-epoch, wrong-slot, and wrong-candidate-byte teeth fail
structural admission before signature soundness is relevant.

The countability-selected codec and byte-length root below are inhabitation
witnesses, not production formats or cryptographic commitments.
-/
import Kernel.AuthenticatedSettlementFinality
import Theory.DeployedMaterializerWitness

namespace Minidregg.Assurance.AuthenticatedSettlementFinalityWitness

open Minidregg.Kernel.AuthenticatedSettlementFinality
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
noncomputable section

deriving instance Countable for
  Minidregg.Kernel.DurableCommitProtocol.RootWrite
deriving instance Countable for
  Minidregg.Kernel.DurableCommitProtocol.Intent
deriving instance Countable for Candidate
deriving instance Countable for VotePayload

/-! ## Three exact finite sparse authority snapshots -/

abbrev Node := Fin 3

def subject0 : SubjectId := ⟨41⟩
def subject1 : SubjectId := ⟨42⟩
def subject2 : SubjectId := ⟨43⟩
def governancePolicy : PolicyId := ⟨17⟩
def oldKeyRevocation : RevocationKey := .channel ⟨9⟩
def newKeyRevocation : RevocationKey := .channel ⟨10⟩

noncomputable abbrev AuthorityMaterializer : CredentialAuthorityState.Materializer :=
  DeployedMaterializerWitness.authorityMaterializer

/-- Epoch two, governance policy epoch five, and a live key-revocation channel. -/
def liveLogical : LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields :=
    (((((((0 : FieldStore CredentialAuthorityState.schema.{0, 0}).write
      (.subjectKeyEpoch subject0) (show Epoch from 2)).write
      (.subjectKeyEpoch subject1) (show Epoch from 2)).write
      (.subjectKeyEpoch subject2) (show Epoch from 2)).write
      (.policyEpoch governancePolicy) (show Epoch from 5)).write
      (.policyAddress governancePolicy 5) ⟨5500⟩).write
      (.revoked oldKeyRevocation) false).write
      (.revoked newKeyRevocation) false
  resources := fun resource => nomatch resource

noncomputable def liveCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer liveLogical

@[simp] theorem liveCell_logical : liveCell.logical = liveLogical := rfl

/-- The exact key-rotation snapshot advances all signer subjects to epoch three. -/
def rotatedLogical : LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := (((liveLogical.fields.write (.subjectKeyEpoch subject0)
    (show Epoch from 3)).write (.subjectKeyEpoch subject1)
    (show Epoch from 3)).write (.subjectKeyEpoch subject2)
    (show Epoch from 3)).write (.revoked oldKeyRevocation) true
  resources := fun resource => nomatch resource

noncomputable def rotatedCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer rotatedLogical

@[simp] theorem rotatedCell_logical : rotatedCell.logical = rotatedLogical := rfl

/-- A later snapshot additionally rotates policy content and revokes the old
key channel.  It is used only for rejection teeth. -/
def finalLogical : LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := (((rotatedLogical.fields.write (.policyEpoch governancePolicy)
    (show Epoch from 6)).write
    (.policyAddress governancePolicy 6) ⟨6600⟩).write
    (.revoked oldKeyRevocation) true)
  resources := fun resource => nomatch resource

noncomputable def finalCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer finalLogical

@[simp] theorem finalCell_logical : finalCell.logical = finalLogical := rfl

def projection : ProjectionUniverse where
  revocationKeys := {oldKeyRevocation, newKeyRevocation}

def signerSubject (node : Node) : SubjectId := ⟨41 + node.val⟩

def signerIdentity (node : Node) : VersionedPublicKeyIdentity Nat where
  subject := signerSubject node
  keyEpoch := 2
  publicKey := 7000 + (signerSubject node).value
  publicKeyAddress := ⟨8000 + (signerSubject node).value⟩
  governancePolicy := governancePolicy
  governanceEpoch := 5
  governanceAddress := ⟨5500⟩
  revocationKey := oldKeyRevocation

def rotatedSignerIdentity (node : Node) : VersionedPublicKeyIdentity Nat where
  subject := signerSubject node
  keyEpoch := 3
  publicKey := 9000 + (signerSubject node).value
  publicKeyAddress := ⟨10000 + (signerSubject node).value⟩
  governancePolicy := governancePolicy
  governanceEpoch := 5
  governanceAddress := ⟨5500⟩
  revocationKey := newKeyRevocation

/-- This logical directory exposes membership separately.  A physical
authenticated directory still owes `DeploymentRefinement`; the closed map is
only a semantic versioned-key-selection witness. -/
def directory : KeyDirectory Nat where
  resolve := fun subject epoch =>
    if epoch = 2 then
      some (7000 + subject.value, ⟨8000 + subject.value⟩)
    else if epoch = 3 then
      some (9000 + subject.value, ⟨10000 + subject.value⟩)
    else none
  Member := fun root identity =>
    (root = liveCell.root ∨ root = rotatedCell.root) ∧
      ((identity.keyEpoch = 2 ∧
          identity.publicKey = 7000 + identity.subject.value ∧
          identity.publicKeyAddress = ⟨8000 + identity.subject.value⟩) ∨
        (identity.keyEpoch = 3 ∧
          identity.publicKey = 9000 + identity.subject.value ∧
          identity.publicKeyAddress = ⟨10000 + identity.subject.value⟩))

noncomputable def authority :
    SignerAuthority AuthorityMaterializer Node Nat where
  projection := projection
  cell := liveCell
  directory := directory
  protocolDomain := ⟨8844⟩
  signer := signerIdentity

@[simp] theorem live_subject_epoch (node : Node) :
    subjectKeyEpochAt liveCell (signerSubject node) = 2 := by
  fin_cases node <;>
    simp [liveCell_logical, liveLogical, subjectKeyEpochAt, signerSubject,
      subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
      newKeyRevocation] <;>
    decide

@[simp] theorem live_policy_epoch :
    policyEpochAt liveCell governancePolicy = 5 := by
  simp [liveCell_logical, liveLogical, policyEpochAt, subject0, subject1, subject2,
    governancePolicy, oldKeyRevocation, newKeyRevocation]

@[simp] theorem live_policy_address :
    policyAddressAt liveCell governancePolicy 5 = ⟨5500⟩ := by
  simp [liveCell_logical, liveLogical, policyAddressAt, subject0, subject1, subject2,
    governancePolicy, oldKeyRevocation, newKeyRevocation]

@[simp] theorem live_old_key_not_revoked :
    isRevoked liveCell oldKeyRevocation = false := by
  have readExact :
      liveLogical.fields (.revoked oldKeyRevocation) = some false := by
    unfold liveLogical
    rw [FieldStore.write_other (different := by
      simp [oldKeyRevocation, newKeyRevocation])]
    rw [FieldStore.write_self]
  change (liveLogical.fields (.revoked oldKeyRevocation)).getD false = false
  rw [readExact]
  rfl

@[simp] theorem rotated_subject_epoch (node : Node) :
    subjectKeyEpochAt rotatedCell (signerSubject node) = 3 := by
  fin_cases node <;>
    simp [rotatedCell_logical, rotatedLogical, liveLogical, subjectKeyEpochAt,
      signerSubject, subject0, subject1, subject2, governancePolicy,
      oldKeyRevocation, newKeyRevocation] <;>
    decide

@[simp] theorem rotated_policy_epoch :
    policyEpochAt rotatedCell governancePolicy = 5 := by
  simp [rotatedCell_logical, rotatedLogical, liveLogical, policyEpochAt,
    subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
    newKeyRevocation]

@[simp] theorem rotated_policy_address :
    policyAddressAt rotatedCell governancePolicy 5 = ⟨5500⟩ := by
  simp [rotatedCell_logical, rotatedLogical, liveLogical, policyAddressAt,
    subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
    newKeyRevocation]

@[simp] theorem rotated_old_key_revoked :
    isRevoked rotatedCell oldKeyRevocation = true := by
  simp [rotatedCell_logical, rotatedLogical, liveLogical, isRevoked,
    subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
    newKeyRevocation]

@[simp] theorem rotated_new_key_not_revoked :
    isRevoked rotatedCell newKeyRevocation = false := by
  have readExact :
      rotatedLogical.fields (.revoked newKeyRevocation) = some false := by
    unfold rotatedLogical
    rw [FieldStore.write_other (different := by
      simp [oldKeyRevocation, newKeyRevocation])]
    rw [FieldStore.write_other (different := by simp)]
    rw [FieldStore.write_other (different := by simp)]
    rw [FieldStore.write_other (different := by simp)]
    unfold liveLogical
    rw [FieldStore.write_self]
  change (rotatedLogical.fields (.revoked newKeyRevocation)).getD false = false
  rw [readExact]
  rfl

@[simp] theorem final_policy_epoch :
    policyEpochAt finalCell governancePolicy = 6 := by
  simp [finalCell_logical, finalLogical, rotatedLogical, liveLogical, policyEpochAt,
    subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
    newKeyRevocation]

@[simp] theorem final_key_revoked :
    isRevoked finalCell oldKeyRevocation = true := by
  simp [finalCell_logical, finalLogical, rotatedLogical, liveLogical, isRevoked,
    subject0, subject1, subject2, governancePolicy, oldKeyRevocation,
    newKeyRevocation]

theorem currentSigner (node : Node) : authority.CurrentSigner node where
  directoryExact := by simp [authority, directory, signerIdentity]
  directoryMember := by simp [authority, directory, signerIdentity]
  keyEpochCurrent := by simp [authority, signerIdentity]
  governanceEpochCurrent := by simp [authority, signerIdentity]
  governanceAddressCurrent := by simp [authority, signerIdentity]
  revocationRegistered := by
    simp [authority, signerIdentity, projection, oldKeyRevocation,
      newKeyRevocation]
  notRevoked := by
    intro revoked
    rcases (mem_authState_revoked_iff projection liveCell oldKeyRevocation).mp revoked with
      ⟨_, marked⟩
    rw [live_old_key_not_revoked] at marked
    contradiction

/-! ## One exact signed durable candidate and quorum -/

noncomputable def candidate : Candidate Nat Nat Nat Nat :=
  Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance.candidate

/-- The first candidate proposed after key rotation extends the exact old log;
it does not reopen the old slot under a fresh key. -/
noncomputable def rotatedCandidate : Candidate Nat Nat Nat Nat where
  epoch := candidate.epoch + 1
  priorLog := candidate.log
  intent := candidate.intent

noncomputable def candidateCodec : LawfulCodec (Candidate Nat Nat Nat Nat) := by
  letI : Nonempty (Candidate Nat Nat Nat Nat) := ⟨candidate⟩
  exact codecOfCountable _

noncomputable def payloadCodec : LawfulCodec VotePayload := by
  letI : Nonempty VotePayload :=
    ⟨expectedPayload authority candidateCodec 0 candidate⟩
  exact codecOfCountable _

/-- The only source of positive signature verification.  A deployment may
instantiate this with a concrete signature implementation and test vector, but
this module neither chooses one nor claims it secure. -/
structure VerifiedSignatureBoundary where
  Signature : Type
  portal : SignaturePortal Nat Signature
  signature : Node -> Signature
  verified : forall node,
    portal.verify (signerIdentity node).publicKey
      (payloadCodec.encode
        (expectedPayload authority candidateCodec node candidate))
      (signature node) = true

def vote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat where
  identity := signerIdentity node
  candidate := candidate
  payload := expectedPayload authority candidateCodec node candidate
  signature := boundary.signature node

theorem voteAccepted (boundary : VerifiedSignatureBoundary) (node : Node) :
    AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (vote boundary node) where
  identityExact := rfl
  candidateExact := rfl
  payloadExact := rfl
  currentSigner := currentSigner node
  verified := boundary.verified node

def quorumCore : Finset Node := {0, 1}

def quorums : QuorumSystem Node where
  isQuorum voters := quorumCore ⊆ voters
  intersects := by
    intro left right leftQuorum rightQuorum
    refine ⟨0, leftQuorum ?_, rightQuorum ?_⟩ <;> simp [quorumCore]

def book (boundary : VerifiedSignatureBoundary) :
    AuthenticatedVoteBook Node Nat boundary.Signature Nat Nat Nat Nat :=
  fun node => [vote boundary node]

def certificate (boundary : VerifiedSignatureBoundary) :
    AuthenticatedFinalized authority candidateCodec payloadCodec boundary.portal
      quorums (book boundary) candidate where
  voters := quorumCore
  quorum := fun _ member => member
  authenticated := by
    intro node member
    exact ⟨vote boundary node, by simp [book], voteAccepted boundary node⟩

theorem erased_certificate_records_exact_candidate
    (boundary : VerifiedSignatureBoundary) :
    candidate ∈ eraseBook (book boundary) 0 := by
  simp [eraseBook, book, vote]

/-- Final no-equivocation is deliberately conditional on the external
signature-origin reduction and absence of its EUF bad event. -/
theorem no_other_authenticated_candidate_at_slot
    (boundary : VerifiedSignatureBoundary)
    (origin : SignatureOrigin payloadCodec boundary.portal)
    (discipline : IssuanceDiscipline origin)
    (noBreak : ¬ origin.EUFBreak)
    {other : Candidate Nat Nat Nat Nat}
    (otherFinal : AuthenticatedFinalized authority candidateCodec payloadCodec
      boundary.portal quorums (book boundary) other) :
    ¬ ConflictsAtSlot candidate other :=
  no_conflicting_authenticated_finalization origin discipline noBreak
    (certificate boundary) otherFinal

/-! ## Closed malformed/stale/replay teeth -/

def wrongSlotVote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat :=
  { vote boundary node with
    payload := { expectedPayload authority candidateCodec node candidate with
      slot := candidate.slot + 1 } }

theorem wrong_slot_vote_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (wrongSlotVote boundary node) := by
  apply wrong_slot_rejected
  simp [wrongSlotVote]

def wrongEpochVote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat :=
  { vote boundary node with
    payload := { expectedPayload authority candidateCodec node candidate with
      consensusEpoch := candidate.epoch + 1 } }

theorem wrong_consensus_epoch_vote_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (wrongEpochVote boundary node) := by
  apply wrong_consensus_epoch_rejected
  simp [wrongEpochVote]

def wrongBytesVote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat :=
  { vote boundary node with
    payload := { expectedPayload authority candidateCodec node candidate with
      candidateBytes := candidateCodec.encode candidate ++ [0] } }

theorem wrong_candidate_payload_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (wrongBytesVote boundary node) := by
  apply wrong_candidate_bytes_rejected
  change candidateCodec.encode candidate ++ [0] ≠ candidateCodec.encode candidate
  intro same
  have lengths := congrArg List.length same
  simp at lengths

def wrongRootVote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat :=
  { vote boundary node with
    payload := { expectedPayload authority candidateCodec node candidate with
      authorityRoot := ⟨authority.cell.root.value + 1⟩ } }

theorem wrong_authority_snapshot_replay_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (wrongRootVote boundary node) := by
  apply wrong_authority_root_rejected
  change (⟨authority.cell.root.value + 1⟩ : Digest) ≠ authority.cell.root
  intro equal
  have values := congrArg Digest.value equal
  simp at values

/-- The old epoch-two key is structurally stale at the exact rotated snapshot,
regardless of whether its old signature still verifies cryptographically. -/
noncomputable def rotatedAuthority :
    SignerAuthority AuthorityMaterializer Node Nat :=
  { authority with
    cell := rotatedCell
    signer := rotatedSignerIdentity }

theorem rotatedCurrentSigner (node : Node) :
    rotatedAuthority.CurrentSigner node where
  directoryExact := by
    simp [rotatedAuthority, authority, directory, rotatedSignerIdentity]
  directoryMember := by
    simp [rotatedAuthority, authority, directory, rotatedSignerIdentity]
  keyEpochCurrent := by simp [rotatedAuthority, authority, rotatedSignerIdentity]
  governanceEpochCurrent := by
    simp [rotatedAuthority, authority, rotatedSignerIdentity]
  governanceAddressCurrent := by
    simp [rotatedAuthority, authority, rotatedSignerIdentity]
  revocationRegistered := by
    simp [rotatedAuthority, authority, rotatedSignerIdentity, projection,
      oldKeyRevocation, newKeyRevocation]
  notRevoked := by
    intro revoked
    rcases (mem_authState_revoked_iff projection rotatedCell
      newKeyRevocation).mp revoked with ⟨_, marked⟩
    rw [rotated_new_key_not_revoked] at marked
    contradiction

def rotationHandoff : RotationHandoff
    (earlierAuthority := authority) (laterAuthority := rotatedAuthority)
    0 candidate rotatedCandidate where
  sameSubject := rfl
  keyEpochAdvanced := by decide
  oldKeyRevokedLater := by
    apply (mem_authState_revoked_iff projection rotatedCell oldKeyRevocation).2
    exact ⟨by simp [projection], rotated_old_key_revoked⟩
  candidateAdvance :=
    { laterEpoch := by simp [rotatedCandidate]
      extendsPrior := List.prefix_rfl }

theorem rotated_key_handoff_extends_exact_log :
    candidate.log.IsPrefix rotatedCandidate.log :=
  RotationHandoff.extends_finalized_log rotationHandoff

theorem stale_key_after_rotation_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote rotatedAuthority candidateCodec payloadCodec boundary.portal
      node candidate (vote boundary node) := by
  apply stale_key_epoch_rejected
  simp [vote, signerIdentity, rotatedAuthority, authority]

/-- Reusing the old key-bound vote at `finalCell` fails twice: its governance
policy epoch is stale and its dedicated revocation channel is present. -/
noncomputable def finalAuthority :
    SignerAuthority AuthorityMaterializer Node Nat :=
  { authority with cell := finalCell }

theorem old_vote_rejected_after_policy_rotation
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote finalAuthority candidateCodec payloadCodec boundary.portal
      node candidate (vote boundary node) := by
  apply stale_governance_epoch_rejected
  simp [vote, signerIdentity, finalAuthority, authority]

theorem revoked_signer_vote_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote finalAuthority candidateCodec payloadCodec boundary.portal
      node candidate (vote boundary node) := by
  apply revoked_signer_rejected
  apply (mem_authState_revoked_iff projection finalCell oldKeyRevocation).2
  exact ⟨by simp [projection], final_key_revoked⟩

/-! ## Explicit physical/cryptographic ceiling -/

/-- Nothing above proves a concrete signature scheme, authenticated directory,
key custody service, rotation transport, network liveness, or physical durable
storage.  Those claims require this external refinement plus the existing
durability refinement for the candidate's intent. -/
structure PhysicalAuthenticatedFinalityRefinement
    (boundary : VerifiedSignatureBoundary) where
  crypto : DeploymentRefinement authority payloadCodec boundary.portal
  PublicKeyDirectoryProofsVerify : Prop
  CredentialCellReadsAreSnapshotConsistent : Prop
  KeyErasureAfterRotation : Prop
  DurableWalRefinementHolds : Prop

/-! ## Axiom audit -/

#print axioms currentSigner
#print axioms voteAccepted
#print axioms no_other_authenticated_candidate_at_slot
#print axioms wrong_slot_vote_rejected
#print axioms rotatedCurrentSigner
#print axioms rotated_key_handoff_extends_exact_log
#print axioms stale_key_after_rotation_rejected
#print axioms revoked_signer_vote_rejected

end
end Minidregg.Assurance.AuthenticatedSettlementFinalityWitness
