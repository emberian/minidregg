/-
# Assurance.AuthenticatedSettlementFinalityWitness -- exact key-bound quorum

This witness joins `AuthenticatedSettlementFinality` to finite sparse
`CredentialAuthorityState` cells.  Three replica identities are selected under
one exact canonical authority root, current subject-key epochs, a versioned
governance-policy address, and a key version (`RevocationKey.signingKey`)
whose standing is live: registered (present in the append-only `registered`
plane) and not revoked (absent from `revoked`).  Their
signed payloads retain exact candidate bytes and the derived log slot.

The signature bytes are supplied only through `VerifiedSignatureBoundary`.
No verifier or EUF theorem is fabricated here.  Likewise the final safety
theorem requires the kernel's explicit origin, no-EUF-break, and issuance
discipline premises.  Closed stale-key, stale-policy, replay-after-revocation,
wrong-root, wrong-epoch, wrong-slot, and wrong-candidate-byte teeth fail
structural admission before signature soundness is relevant.

The authority snapshots are deployed `CredentialAuthorityCell` stores (the
store codec and its cSHAKE256 root).  The countability-selected codecs for
candidates and vote payloads are inhabitation witnesses, not production formats.
-/
import Kernel.AuthenticatedSettlementFinality
import Compiler.CredentialAuthorityCell
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
open Minidregg.Theory.Store
open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec

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
def signerSubject (node : Node) : SubjectId := ⟨41 + node.val⟩
/-- Each replica's epoch-two key version. -/
def oldKeyRevocation (node : Node) : RevocationKey := .signingKey (signerSubject node) 2
/-- Each replica's epoch-three key version. -/
def newKeyRevocation (node : Node) : RevocationKey := .signingKey (signerSubject node) 3

abbrev AuthorityMaterializer : CredentialAuthorityState.Materializer :=
  CredentialAuthorityCell.materializer

/-- Epoch two, governance policy epoch five, and every replica's epoch-two key
version registered, none revoked.  Registration is presence in the append-only
`registered` plane; liveness is absence from `revoked`. -/
def liveEntries : List (Entry layout) :=
  [⟨⟨.subjectKeyEpoch, subject0⟩, (2 : Epoch)⟩,
   ⟨⟨.subjectKeyEpoch, subject1⟩, (2 : Epoch)⟩,
   ⟨⟨.subjectKeyEpoch, subject2⟩, (2 : Epoch)⟩,
   ⟨⟨.policyEpoch, governancePolicy⟩, (5 : Epoch)⟩,
   ⟨⟨.policyAddress, (governancePolicy, 5)⟩, (⟨5500⟩ : Digest)⟩,
   ⟨⟨.registered, oldKeyRevocation 0⟩, ()⟩,
   ⟨⟨.registered, oldKeyRevocation 1⟩, ()⟩,
   ⟨⟨.registered, oldKeyRevocation 2⟩, ()⟩]

def liveLogical : Store layout := fromEntries liveEntries

def liveCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer liveLogical

@[simp] theorem liveCell_logical : liveCell.logical = liveLogical := rfl

/-- The key rotation as one guarded patch: every signer subject advances from
epoch two to three, its epoch-three key version is registered, and its
epoch-two version is revoked.  No registration is removed. -/
def rotationPatch : Patch layout :=
  [.write .subjectKeyEpoch subject0 (2 : Epoch) (3 : Epoch),
   .write .subjectKeyEpoch subject1 (2 : Epoch) (3 : Epoch),
   .write .subjectKeyEpoch subject2 (2 : Epoch) (3 : Epoch),
   .allocate .registered (newKeyRevocation 0) (),
   .allocate .registered (newKeyRevocation 1) (),
   .allocate .registered (newKeyRevocation 2) (),
   .allocate .revoked (oldKeyRevocation 0) (),
   .allocate .revoked (oldKeyRevocation 1) (),
   .allocate .revoked (oldKeyRevocation 2) ()]

/-- The exact key-rotation snapshot: all signer subjects at epoch three, their
epoch-three versions registered and their epoch-two versions revoked
(registered present AND revoked present).  It is not
supplied beside the live snapshot: it is the store the rotation patch runs to. -/
def rotatedLogical : Store layout := Patch.run liveLogical rotationPatch

def rotatedCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer rotatedLogical

@[simp] theorem rotatedCell_logical : rotatedCell.logical = rotatedLogical := rfl

/-- Every guard of the rotation patch holds at its prefix: the rotation is an
accepted transition of the live store. -/
theorem rotation_executes : Patch.Executes liveLogical rotationPatch rotatedLogical :=
  ⟨by decide, rfl⟩

/-- A later policy-content rotation.  It is used only for rejection teeth. -/
def policyRotationPatch : Patch layout :=
  [.write .policyEpoch governancePolicy (5 : Epoch) (6 : Epoch),
   .allocate .policyAddress (governancePolicy, 6) (⟨6600⟩ : Digest)]

def finalLogical : Store layout := Patch.run rotatedLogical policyRotationPatch

theorem policy_rotation_executes :
    Patch.Executes rotatedLogical policyRotationPatch finalLogical :=
  ⟨by decide, rfl⟩

def finalCell : CredentialAuthorityState.Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer finalLogical

@[simp] theorem finalCell_logical : finalCell.logical = finalLogical := rfl

def signerIdentity (node : Node) : VersionedPublicKeyIdentity Nat where
  subject := signerSubject node
  keyEpoch := 2
  publicKey := 7000 + (signerSubject node).value
  publicKeyAddress := ⟨8000 + (signerSubject node).value⟩
  governancePolicy := governancePolicy
  governanceEpoch := 5
  governanceAddress := ⟨5500⟩

def rotatedSignerIdentity (node : Node) : VersionedPublicKeyIdentity Nat where
  subject := signerSubject node
  keyEpoch := 3
  publicKey := 9000 + (signerSubject node).value
  publicKeyAddress := ⟨10000 + (signerSubject node).value⟩
  governancePolicy := governancePolicy
  governanceEpoch := 5
  governanceAddress := ⟨5500⟩

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

def authority :
    SignerAuthority AuthorityMaterializer Node Nat where
  cell := liveCell
  directory := directory
  protocolDomain := ⟨8844⟩
  signer := signerIdentity

@[simp] theorem live_subject_epoch (node : Node) :
    subjectKeyEpochAt liveCell (signerSubject node) = 2 := by
  fin_cases node <;> decide

@[simp] theorem live_policy_epoch :
    policyEpochAt liveCell governancePolicy = 5 := by
  decide

@[simp] theorem live_policy_address :
    policyAddressAt liveCell governancePolicy 5 = ⟨5500⟩ := by
  decide

@[simp] theorem live_old_key_standing (node : Node) :
    keyStanding liveCell (oldKeyRevocation node) = .live := by
  fin_cases node <;> decide

@[simp] theorem rotated_subject_epoch (node : Node) :
    subjectKeyEpochAt rotatedCell (signerSubject node) = 3 := by
  fin_cases node <;> decide

@[simp] theorem rotated_policy_epoch :
    policyEpochAt rotatedCell governancePolicy = 5 := by
  decide

@[simp] theorem rotated_policy_address :
    policyAddressAt rotatedCell governancePolicy 5 = ⟨5500⟩ := by
  decide

@[simp] theorem rotated_old_key_revoked (node : Node) :
    isRevoked rotatedCell (oldKeyRevocation node) = true := by
  fin_cases node <;> decide

/-- Each old key version after rotation is registered present AND revoked
present: its registration survived the rotation (`registration_monotone`). -/
theorem rotated_old_key_registered_and_revoked (node : Node) :
    rotatedLogical ⟨.registered, oldKeyRevocation node⟩ = some () ∧
      rotatedLogical ⟨.revoked, oldKeyRevocation node⟩ = some () :=
  ⟨registration_monotone rotation_executes (oldKeyRevocation node)
      (by fin_cases node <;> rfl),
    by fin_cases node <;> rfl⟩

/-- ...and it stays so through the later policy rotation: the permanence
theorem, applied to the actual next transition. -/
theorem final_old_key_registered_and_revoked (node : Node) :
    finalLogical ⟨.registered, oldKeyRevocation node⟩ = some () ∧
      finalLogical ⟨.revoked, oldKeyRevocation node⟩ = some () :=
  revoked_registration_permanent policy_rotation_executes (oldKeyRevocation node)
    (rotated_old_key_registered_and_revoked node).1
    (rotated_old_key_registered_and_revoked node).2

@[simp] theorem rotated_new_key_standing (node : Node) :
    keyStanding rotatedCell (newKeyRevocation node) = .live := by
  fin_cases node <;> decide

@[simp] theorem final_policy_epoch :
    policyEpochAt finalCell governancePolicy = 6 := by
  decide

@[simp] theorem final_key_revoked (node : Node) :
    isRevoked finalCell (oldKeyRevocation node) = true := by
  fin_cases node <;> decide

theorem currentSigner (node : Node) : authority.CurrentSigner node where
  directoryExact := by simp [authority, directory, signerIdentity]
  directoryMember := by simp [authority, directory, signerIdentity]
  keyEpochCurrent := by simp [authority, signerIdentity]
  governanceEpochCurrent := by simp [authority, signerIdentity]
  governanceAddressCurrent := by simp [authority, signerIdentity]
  standing := live_old_key_standing node

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
  standing := rotated_new_key_standing node

def rotationHandoff : RotationHandoff
    (earlierAuthority := authority) (laterAuthority := rotatedAuthority)
    0 candidate rotatedCandidate where
  sameSubject := rfl
  keyEpochAdvanced := by decide
  oldKeyRevokedLater := rotated_old_key_revoked 0
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
  exact revoked_signer_rejected (final_key_revoked node)

/-- The same signed vote, relabelled with a key version (epoch seven) the cell
never registered. -/
def strangerVote (boundary : VerifiedSignatureBoundary) (node : Node) :
    SignedVote Nat boundary.Signature Nat Nat Nat Nat :=
  { vote boundary node with
    identity := { signerIdentity node with keyEpoch := 7 } }

/-- Refuting pole of registration: a key the exact cell has not registered is
refused before signature soundness is relevant. -/
theorem unregistered_key_vote_rejected
    (boundary : VerifiedSignatureBoundary) (node : Node) :
    ¬ AcceptedVote authority candidateCodec payloadCodec boundary.portal
      node candidate (strangerVote boundary node) :=
  unregistered_signer_rejected (by
    show isRegistered liveCell (.signingKey (signerSubject node) 7) = false
    fin_cases node <;> decide)

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

/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.currentSigner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms currentSigner
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.voteAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms voteAccepted
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.no_other_authenticated_candidate_at_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_other_authenticated_candidate_at_slot
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.wrong_slot_vote_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_slot_vote_rejected
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.rotatedCurrentSigner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotatedCurrentSigner
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.rotated_key_handoff_extends_exact_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotated_key_handoff_extends_exact_log
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.stale_key_after_rotation_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_key_after_rotation_rejected
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.revoked_signer_vote_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_signer_vote_rejected
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.unregistered_key_vote_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unregistered_key_vote_rejected
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.rotation_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotation_executes
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.rotated_old_key_registered_and_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotated_old_key_registered_and_revoked
/-- info: 'Minidregg.Assurance.AuthenticatedSettlementFinalityWitness.final_old_key_registered_and_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms final_old_key_registered_and_revoked

end
end Minidregg.Assurance.AuthenticatedSettlementFinalityWitness
