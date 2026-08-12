/-
# Kernel.AuthenticatedSettlementFinality -- versioned-key quorum certificates

`ReplicatedSettlementFinality` proves safety once a `VoteBook` and its voting
discipline are trusted.  This module makes the cryptographic/control seam of
that book explicit.  A signed vote binds all of the following data:

* the canonical credential-authority root consulted for admission;
* a versioned public-key identity selected for one replica;
* the current subject-key and governance-policy epochs;
* a registered, live revocation key for that key identity;
* the protocol domain, consensus epoch, derived log slot, and injectively
  encoded candidate bytes.

Boolean signature verification is deliberately not called sound.  A
`SignatureOrigin` says that an accepted verification either came from the
explicit issuance relation or constitutes an EUF break.  Under `¬ EUFBreak`,
and an issuance discipline that does not sign two candidate byte strings for
one protocol/subject/slot, intersecting authenticated quorums cannot finalize
different candidates at that slot.  This is a conditional cryptographic
reduction, not a concrete signature theorem.

**Trust ceiling.**  `KeyDirectory.Member`, signature verification origin,
EUF security, key custody, and issuance discipline are deployment premises.
The module proves no concrete scheme secure and no network live.  Dedicated
credential revocation channels are used as key-version revocation identifiers;
a deployment must refine that assignment to its physical key registry.
-/
import Kernel.ReplicatedSettlementFinality
import Theory.CredentialAuthorityState

namespace Minidregg.Kernel.AuthenticatedSettlementFinality

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Kernel.ReplicatedSettlementFinality

set_option autoImplicit false

universe u v w x n k s

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w}
  {Event : Type x} {Node : Type n} {PublicKey : Type k} {Signature : Type s}

/-! ## Versioned public-key identities and the canonical authority view -/

/-- One public key together with every stable name needed to select and revoke
it.  `revocationKey` should be a dedicated credential-authority channel for
this key version (or a deployment-refined equivalent), never a host-local flag.
The governance policy address pins the exact versioned policy content under
which this signer is admitted. -/
structure VersionedPublicKeyIdentity (PublicKey : Type k) where
  subject : SubjectId
  keyEpoch : Epoch
  publicKey : PublicKey
  publicKeyAddress : Digest
  governancePolicy : PolicyId
  governanceEpoch : Epoch
  governanceAddress : Digest
  revocationKey : RevocationKey

/-- The public-key lookup is an explicit authenticated-directory boundary.
`Member root identity` is the semantic membership relation a physical Merkle
or database proof must refine; it is not manufactured from the lookup map. -/
structure KeyDirectory (PublicKey : Type k) where
  resolve : SubjectId -> Epoch -> Option (PublicKey × Digest)
  Member : Digest -> VersionedPublicKeyIdentity PublicKey -> Prop

/-- One replica configuration, tied to an exact materialized credential cell.
Changing `cell` changes the authority root included in every expected vote. -/
structure SignerAuthority
    (M : CredentialAuthorityState.Materializer)
    (Node : Type n) (PublicKey : Type k) where
  projection : ProjectionUniverse
  cell : CredentialAuthorityState.Cell M
  directory : KeyDirectory PublicKey
  protocolDomain : Digest
  signer : Node -> VersionedPublicKeyIdentity PublicKey

namespace SignerAuthority

variable {M : CredentialAuthorityState.Materializer}
  (authority : SignerAuthority M Node PublicKey)

def authState : TypedAuthorization.AuthState :=
  CredentialAuthorityState.authState authority.projection authority.cell

/-- Exact currentness of one signer at the canonical authority snapshot.  The
directory entry, key epoch, policy epoch/address, and revocation membership all
refer to the same versioned identity and exact `cell.root`. -/
structure CurrentSigner (node : Node) : Prop where
  directoryExact :
    authority.directory.resolve (authority.signer node).subject
        (authority.signer node).keyEpoch =
      some ((authority.signer node).publicKey,
        (authority.signer node).publicKeyAddress)
  directoryMember :
    authority.directory.Member authority.cell.root (authority.signer node)
  keyEpochCurrent :
    (authority.signer node).keyEpoch =
      CredentialAuthorityState.subjectKeyEpochAt authority.cell
        (authority.signer node).subject
  governanceEpochCurrent :
    (authority.signer node).governanceEpoch =
      CredentialAuthorityState.policyEpochAt authority.cell
        (authority.signer node).governancePolicy
  governanceAddressCurrent :
    CredentialAuthorityState.policyAddressAt authority.cell
        (authority.signer node).governancePolicy
        (authority.signer node).governanceEpoch =
      (authority.signer node).governanceAddress
  revocationRegistered :
    (authority.signer node).revocationKey ∈ authority.projection.revocationKeys
  notRevoked :
    (authority.signer node).revocationKey ∉ authority.authState.revoked

end SignerAuthority

/-! ## Exact signed vote payload -/

/-- The lossless semantic message signed by a replica.  A lawful codec below
turns this value into exact bytes.  The candidate slot is redundant only on
purpose: admission checks it against `Candidate.slot`, giving malformed-wire
and replay rejection a direct tooth. -/
structure VotePayload where
  protocolDomain : Digest
  authorityRoot : Digest
  signerSubject : SubjectId
  signerKeyEpoch : Epoch
  publicKeyAddress : Digest
  governancePolicy : PolicyId
  governanceEpoch : Epoch
  governanceAddress : Digest
  consensusEpoch : Nat
  slot : Nat
  candidateBytes : List UInt8
  deriving DecidableEq, Repr

/-- An executable signature portal only.  No soundness proposition is hidden
inside this data interface. -/
structure SignaturePortal (PublicKey : Type k) (Signature : Type s) where
  verify : PublicKey -> List UInt8 -> Signature -> Bool

variable {M : CredentialAuthorityState.Materializer}

def expectedPayload
    (authority : SignerAuthority M Node PublicKey)
    (candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event))
    (node : Node) (candidate : Candidate TxId CellId Nullifier Event) :
    VotePayload :=
  { protocolDomain := authority.protocolDomain
    authorityRoot := authority.cell.root
    signerSubject := (authority.signer node).subject
    signerKeyEpoch := (authority.signer node).keyEpoch
    publicKeyAddress := (authority.signer node).publicKeyAddress
    governancePolicy := (authority.signer node).governancePolicy
    governanceEpoch := (authority.signer node).governanceEpoch
    governanceAddress := (authority.signer node).governanceAddress
    consensusEpoch := candidate.epoch
    slot := candidate.slot
    candidateBytes := candidateCodec.encode candidate }

/-- A wire vote retains both the typed candidate and the exact payload sent to
the signature verifier.  Neither can silently be reconstructed from a digest. -/
structure SignedVote
    (PublicKey : Type k) (Signature : Type s)
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  identity : VersionedPublicKeyIdentity PublicKey
  candidate : Candidate TxId CellId Nullifier Event
  payload : VotePayload
  signature : Signature

/-- Admission of one signed vote for one exact authority snapshot, replica,
and candidate.  The equality fields are intentional proof obligations: a host
parser cannot independently choose identity, slot, or payload bytes. -/
structure AcceptedVote
    (authority : SignerAuthority M Node PublicKey)
    (candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event))
    (payloadCodec : LawfulCodec VotePayload)
    (portal : SignaturePortal PublicKey Signature)
    (node : Node) (candidate : Candidate TxId CellId Nullifier Event)
    (vote : SignedVote PublicKey Signature TxId CellId Nullifier Event) : Prop where
  identityExact : vote.identity = authority.signer node
  candidateExact : vote.candidate = candidate
  payloadExact : vote.payload = expectedPayload authority candidateCodec node candidate
  currentSigner : authority.CurrentSigner node
  verified : portal.verify vote.identity.publicKey
    (payloadCodec.encode vote.payload) vote.signature = true

/-! ## Structural rejection teeth -/

theorem stale_key_epoch_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (stale : vote.identity.keyEpoch ≠
      subjectKeyEpochAt authority.cell vote.identity.subject) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply stale
  rw [accepted.identityExact]
  exact accepted.currentSigner.keyEpochCurrent

theorem stale_governance_epoch_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (stale : vote.identity.governanceEpoch ≠
      policyEpochAt authority.cell vote.identity.governancePolicy) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply stale
  rw [accepted.identityExact]
  exact accepted.currentSigner.governanceEpochCurrent

theorem wrong_governance_address_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : CredentialAuthorityState.policyAddressAt authority.cell
        vote.identity.governancePolicy vote.identity.governanceEpoch ≠
      vote.identity.governanceAddress) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply wrong
  rw [accepted.identityExact]
  exact accepted.currentSigner.governanceAddressCurrent

theorem revoked_signer_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (revoked : vote.identity.revocationKey ∈ authority.authState.revoked) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply accepted.currentSigner.notRevoked
  simpa [accepted.identityExact] using revoked

theorem wrong_authority_root_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : vote.payload.authorityRoot ≠ authority.cell.root) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply wrong
  rw [accepted.payloadExact]
  rfl

theorem wrong_consensus_epoch_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : vote.payload.consensusEpoch ≠ candidate.epoch) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply wrong
  rw [accepted.payloadExact]
  rfl

theorem wrong_slot_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : vote.payload.slot ≠ candidate.slot) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply wrong
  rw [accepted.payloadExact]
  rfl

theorem wrong_candidate_bytes_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : vote.payload.candidateBytes ≠ candidateCodec.encode candidate) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  apply wrong
  rw [accepted.payloadExact]
  rfl

theorem wrong_typed_candidate_rejected
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (wrong : vote.candidate ≠ candidate) :
    ¬ AcceptedVote authority candidateCodec payloadCodec portal node candidate vote := by
  intro accepted
  exact wrong accepted.candidateExact

/-! ## Explicit signature-origin/EUF boundary -/

/-- A verification accepted by `portal` either corresponds to a signature in
the deployment issuance relation or witnesses an EUF break.  In a concrete
game this implication normally carries a probability bound; this logical
interface exposes only the exact bad event and never claims it impossible. -/
structure SignatureOrigin
    (payloadCodec : LawfulCodec VotePayload)
    (portal : SignaturePortal PublicKey Signature) where
  Issued : VersionedPublicKeyIdentity PublicKey -> VotePayload -> Signature -> Prop
  EUFBreak : Prop
  verify_origin : forall identity payload signature,
    portal.verify identity.publicKey (payloadCodec.encode payload) signature = true ->
      Issued identity payload signature ∨ EUFBreak

/-- Key-custody/consensus discipline at the issuance boundary.  Across key
rotation, the same subject may use different public keys, but it must not issue
different candidate bytes for one protocol domain and one log slot. -/
structure IssuanceDiscipline
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    (origin : SignatureOrigin payloadCodec portal) : Prop where
  noEquivocation : forall
      {leftIdentity rightIdentity : VersionedPublicKeyIdentity PublicKey}
      {leftPayload rightPayload : VotePayload}
      {leftSignature rightSignature : Signature},
    origin.Issued leftIdentity leftPayload leftSignature ->
    origin.Issued rightIdentity rightPayload rightSignature ->
    leftIdentity.subject = rightIdentity.subject ->
    leftPayload.protocolDomain = rightPayload.protocolDomain ->
    leftPayload.slot = rightPayload.slot ->
      leftPayload.candidateBytes = rightPayload.candidateBytes

theorem issued_of_accepted
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    (origin : SignatureOrigin payloadCodec portal)
    (noBreak : ¬ origin.EUFBreak)
    {node : Node} {candidate : Candidate TxId CellId Nullifier Event}
    {vote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (accepted : AcceptedVote authority candidateCodec payloadCodec portal
      node candidate vote) :
    origin.Issued vote.identity vote.payload vote.signature := by
  rcases origin.verify_origin vote.identity vote.payload vote.signature
      accepted.verified with issued | broken
  · exact issued
  · exact False.elim (noBreak broken)

private theorem lawfulCodec_encode_injective {alpha : Type u}
    (codec : LawfulCodec alpha) : Function.Injective codec.encode := by
  intro left right equal
  have decoded := congrArg codec.decode equal
  simpa only [codec.decode_encode, Option.some.injEq] using decoded

/-- Accepted votes under two authority snapshots (and therefore potentially
two rotated public keys) cannot name different exact candidates at one slot
when the snapshots retain the same protocol domain and signer subject. -/
theorem accepted_candidate_unique_across_authorities_at_slot
    {leftAuthority rightAuthority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    (origin : SignatureOrigin payloadCodec portal)
    (discipline : IssuanceDiscipline origin)
    (noBreak : ¬ origin.EUFBreak)
    {leftNode rightNode : Node}
    {left right : Candidate TxId CellId Nullifier Event}
    {leftVote rightVote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (leftAccepted : AcceptedVote leftAuthority candidateCodec payloadCodec portal
      leftNode left leftVote)
    (rightAccepted : AcceptedVote rightAuthority candidateCodec payloadCodec portal
      rightNode right rightVote)
    (sameSubject : (leftAuthority.signer leftNode).subject =
      (rightAuthority.signer rightNode).subject)
    (sameDomain : leftAuthority.protocolDomain = rightAuthority.protocolDomain)
    (sameSlot : left.slot = right.slot) :
    left = right := by
  have leftIssued := issued_of_accepted origin noBreak leftAccepted
  have rightIssued := issued_of_accepted origin noBreak rightAccepted
  have voteSameSubject : leftVote.identity.subject = rightVote.identity.subject := by
    rw [leftAccepted.identityExact, rightAccepted.identityExact]
    exact sameSubject
  have voteSameDomain : leftVote.payload.protocolDomain =
      rightVote.payload.protocolDomain := by
    rw [leftAccepted.payloadExact, rightAccepted.payloadExact]
    exact sameDomain
  have payloadSameSlot : leftVote.payload.slot = rightVote.payload.slot := by
    rw [leftAccepted.payloadExact, rightAccepted.payloadExact]
    exact sameSlot
  have sameBytes := discipline.noEquivocation leftIssued rightIssued
    voteSameSubject voteSameDomain payloadSameSlot
  rw [leftAccepted.payloadExact, rightAccepted.payloadExact] at sameBytes
  exact lawfulCodec_encode_injective candidateCodec sameBytes

/-- Same-snapshot specialization used by an authenticated quorum's intersecting
replica. -/
theorem accepted_candidate_unique_at_slot
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    (origin : SignatureOrigin payloadCodec portal)
    (discipline : IssuanceDiscipline origin)
    (noBreak : ¬ origin.EUFBreak)
    {node : Node}
    {left right : Candidate TxId CellId Nullifier Event}
    {leftVote rightVote : SignedVote PublicKey Signature TxId CellId Nullifier Event}
    (leftAccepted : AcceptedVote authority candidateCodec payloadCodec portal
      node left leftVote)
    (rightAccepted : AcceptedVote authority candidateCodec payloadCodec portal
      node right rightVote)
    (sameSlot : left.slot = right.slot) :
    left = right :=
  accepted_candidate_unique_across_authorities_at_slot
    origin discipline noBreak leftAccepted rightAccepted rfl rfl sameSlot

/-! ## Authenticated quorum certificates -/

abbrev AuthenticatedVoteBook
    (Node : Type n) (PublicKey : Type k) (Signature : Type s)
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) :=
  Node -> List (SignedVote PublicKey Signature TxId CellId Nullifier Event)

def eraseBook
    (book : AuthenticatedVoteBook Node PublicKey Signature
      TxId CellId Nullifier Event) :
    VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event) :=
  fun node => (book node).map SignedVote.candidate

/-- A quorum certificate carries an actual admitted signed vote for every
voter.  Erasure to `Finalized` below is lossless with respect to the candidate,
but cryptographic evidence stays available in this richer certificate. -/
structure AuthenticatedFinalized
    [DecidableEq Node]
    (authority : SignerAuthority M Node PublicKey)
    (candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event))
    (payloadCodec : LawfulCodec VotePayload)
    (portal : SignaturePortal PublicKey Signature)
    (quorums : QuorumSystem Node)
    (book : AuthenticatedVoteBook Node PublicKey Signature
      TxId CellId Nullifier Event)
    (candidate : Candidate TxId CellId Nullifier Event) :
    Type (max u v w x n k s) where
  voters : Finset Node
  quorum : quorums.isQuorum voters
  authenticated : forall node, node ∈ voters ->
    exists vote, vote ∈ book node ∧
      AcceptedVote authority candidateCodec payloadCodec portal node candidate vote

namespace AuthenticatedFinalized

variable [DecidableEq Node]
  {authority : SignerAuthority M Node PublicKey}
  {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
  {payloadCodec : LawfulCodec VotePayload}
  {portal : SignaturePortal PublicKey Signature}
  {quorums : QuorumSystem Node}
  {book : AuthenticatedVoteBook Node PublicKey Signature
    TxId CellId Nullifier Event}
  {candidate : Candidate TxId CellId Nullifier Event}

def erase
    (certificate : AuthenticatedFinalized authority candidateCodec payloadCodec
      portal quorums book candidate) :
    Finalized quorums (eraseBook book) candidate where
  voters := certificate.voters
  quorum := certificate.quorum
  voted := by
    intro node member
    rcases certificate.authenticated node member with ⟨vote, inBook, accepted⟩
    apply List.mem_map.mpr
    exact ⟨vote, inBook, accepted.candidateExact⟩

end AuthenticatedFinalized

/-- Intersecting authenticated quorums inherit a common replica.  The
signature-origin reduction and cross-key issuance discipline at that replica
give exact candidate equality at one slot, without postulating a trusted
`VoteBook` prefix discipline. -/
theorem authenticated_finalized_candidate_unique_at_slot
    [DecidableEq Node]
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {quorums : QuorumSystem Node}
    {book : AuthenticatedVoteBook Node PublicKey Signature
      TxId CellId Nullifier Event}
    (origin : SignatureOrigin payloadCodec portal)
    (discipline : IssuanceDiscipline origin)
    (noBreak : ¬ origin.EUFBreak)
    {left right : Candidate TxId CellId Nullifier Event}
    (leftFinal : AuthenticatedFinalized authority candidateCodec payloadCodec
      portal quorums book left)
    (rightFinal : AuthenticatedFinalized authority candidateCodec payloadCodec
      portal quorums book right)
    (sameSlot : left.slot = right.slot) :
    left = right := by
  rcases quorums.intersects leftFinal.voters rightFinal.voters
      leftFinal.quorum rightFinal.quorum with ⟨node, inLeft, inRight⟩
  rcases leftFinal.authenticated node inLeft with
    ⟨leftVote, leftMember, leftAccepted⟩
  rcases rightFinal.authenticated node inRight with
    ⟨rightVote, rightMember, rightAccepted⟩
  exact accepted_candidate_unique_at_slot origin discipline noBreak
    leftAccepted rightAccepted sameSlot

theorem no_conflicting_authenticated_finalization
    [DecidableEq Node]
    {authority : SignerAuthority M Node PublicKey}
    {candidateCodec : LawfulCodec (Candidate TxId CellId Nullifier Event)}
    {payloadCodec : LawfulCodec VotePayload}
    {portal : SignaturePortal PublicKey Signature}
    {quorums : QuorumSystem Node}
    {book : AuthenticatedVoteBook Node PublicKey Signature
      TxId CellId Nullifier Event}
    (origin : SignatureOrigin payloadCodec portal)
    (discipline : IssuanceDiscipline origin)
    (noBreak : ¬ origin.EUFBreak)
    {left right : Candidate TxId CellId Nullifier Event}
    (leftFinal : AuthenticatedFinalized authority candidateCodec payloadCodec
      portal quorums book left)
    (rightFinal : AuthenticatedFinalized authority candidateCodec payloadCodec
      portal quorums book right) :
    ¬ ConflictsAtSlot left right := by
  rintro ⟨sameSlot, differs⟩
  have candidateExact := authenticated_finalized_candidate_unique_at_slot
    origin discipline noBreak leftFinal rightFinal sameSlot
  exact differs (congrArg Candidate.intent candidateExact)

/-! ## Rotation and deployment ceilings -/

/-- A safe key rotation changes the versioned key identity only after the old
key's candidate log is handed off as a prefix of the new candidate.  Revoking
the old identity in the later canonical authority state is explicit. -/
structure RotationHandoff
    {earlierAuthority laterAuthority : SignerAuthority M Node PublicKey}
    (node : Node)
    (earlier later : Candidate TxId CellId Nullifier Event) : Prop where
  sameSubject : (earlierAuthority.signer node).subject =
    (laterAuthority.signer node).subject
  keyEpochAdvanced : (earlierAuthority.signer node).keyEpoch <
    (laterAuthority.signer node).keyEpoch
  oldKeyRevokedLater : (earlierAuthority.signer node).revocationKey ∈
    laterAuthority.authState.revoked
  candidateAdvance : EpochAdvance earlier later

theorem RotationHandoff.extends_finalized_log
    {earlierAuthority laterAuthority : SignerAuthority M Node PublicKey}
    {node : Node}
    {earlier later : Candidate TxId CellId Nullifier Event}
    (handoff : RotationHandoff
      (earlierAuthority := earlierAuthority)
      (laterAuthority := laterAuthority) node earlier later) :
    earlier.log.IsPrefix later.log :=
  epochAdvance_extends_log handoff.candidateAdvance

/-- Physical directory proofs, signatures, key custody, and network progress
remain outside the logical carrier.  Supplying this record is the exact point
where a deployment may claim those refinements. -/
structure DeploymentRefinement
    (authority : SignerAuthority M Node PublicKey)
    (payloadCodec : LawfulCodec VotePayload)
    (portal : SignaturePortal PublicKey Signature) where
  DirectoryProof : Type
  directoryMemberSound : forall node,
    DirectoryProof -> authority.directory.Member authority.cell.root
      (authority.signer node)
  origin : SignatureOrigin payloadCodec portal
  issuanceDiscipline : IssuanceDiscipline origin
  noEufBreak : ¬ origin.EUFBreak
  PhysicalKeyCustody : Prop
  RotationProtocolRefinesHandoff : Prop
  AuthenticatedTransport : Prop
  OnlineQuorumExists : Prop
  EventualNetworkDelivery : Prop
  ResponsiveReplicas : Prop

/-! ## Axiom audit -/

/-- info: 'Minidregg.Kernel.AuthenticatedSettlementFinality.stale_key_epoch_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_key_epoch_rejected
/-- info: 'Minidregg.Kernel.AuthenticatedSettlementFinality.revoked_signer_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_signer_rejected
/-- info: 'Minidregg.Kernel.AuthenticatedSettlementFinality.accepted_candidate_unique_across_authorities_at_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_candidate_unique_across_authorities_at_slot
/-- info: 'Minidregg.Kernel.AuthenticatedSettlementFinality.accepted_candidate_unique_at_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_candidate_unique_at_slot
/-- info: 'Minidregg.Kernel.AuthenticatedSettlementFinality.no_conflicting_authenticated_finalization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_conflicting_authenticated_finalization

end Minidregg.Kernel.AuthenticatedSettlementFinality
