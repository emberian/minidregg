/-
# Compiler.CredentialAuthorityPolicyRegistry -- complete authority selects policy

The receiving registry consumes the complete canonical authority domain. Its
policy source is the executable canonical v2 record, addressed by cSHAKE. The
current source revision, selected address, membership, and all authority epochs come
from that same snapshot. The physical receiver supplies complete catalogue
and shard provenance; semantic source bytes alone cannot reconstruct it.

The explicit Example namespace retains the earlier bounded-page model only
as an instance of the generic selection and stale-guard theorems. It is not a
receiving configuration or decoder fallback. Signature verification remains
the deployment portal's responsibility.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Compiler.CredentialAuthorityDomain
import Compiler.PolicyRecordCodec
import Compiler.CredentialSignatureAdmission
import Theory.CredentialLineageAdmission
import Kernel.CanonicalPolicyRegistry

namespace Minidregg.Compiler.CredentialAuthorityPolicyRegistry

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Pred
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Stable policy-source content address -/

/-- The single policy-source codec is the executable canonical v2 codec.
The former noncomputable enumeration is not a decoder fallback. -/
def policyRecordCodec : LawfulCodec PolicyRecord := PolicyRecordCodec.codec

def policyRecordCustomization : List UInt8 :=
  PolicyRecordCodec.customization

def policyHashBytes (bytes : List UInt8) : Digest :=
  PolicyRecordCodec.hashBytes bytes

def policyRecordDigest (record : PolicyRecord) : Digest :=
  policyHashBytes (policyRecordCodec.encode record)

theorem policyRecordCodec_canonical {bytes : List UInt8} {record : PolicyRecord}
    (decoded : policyRecordCodec.decode bytes = some record) :
    policyRecordCodec.encode record = bytes :=
  PolicyRecordCodec.decode_canonical decoded

/-- Pair-scoped collision boundary for policy substitution.  Ordinary exact
selection below needs only the digest equality; semantic substitution claims
must additionally supply this premise for the particular pair in question. -/
structure PolicyRecordPairBinding (left right : PolicyRecord) : Prop where
  noCollision :
    policyHashBytes (policyRecordCodec.encode left) =
        policyHashBytes (policyRecordCodec.encode right) ->
      left = right

/-! ## Complete canonical authority snapshots and source resolution -/

abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-- Every authority coordinate is read from the full canonical schema. The
revocation universe is derived from every checked shard, never requester
selected. A physical receiver must provide this snapshot's provenance. -/
def projection (snapshot : Snapshot) :
    CredentialAuthorityState.StateProjection CredentialAuthorityState.schema.{0, 0} :=
  snapshot.revocationUniverse.stateProjection

@[simp] theorem projection_authState (snapshot : Snapshot) :
    (projection snapshot).authState snapshot.cell = snapshot.authState :=
  CredentialAuthorityState.authState_identity_projection _ _

/-- Data returned by the actual resolver retains every checked source fact. -/
structure LoadedPolicy (snapshot : Snapshot) (store : PayloadStore)
    (policyId : PolicyId) (revision : PolicyRevision) where
  committed : CommittedPolicy
  current : snapshot.authState.policyRevision policyId = revision
  member : snapshot.policyContains policyId (snapshot.authState.policyEpoch policyId) revision committed.address
  policyIdExact : committed.record.policyId = policyId
  revisionExact : committed.record.version = revision
  domainExact : committed.record.domain = snapshot.domain
  addressExact : policyRecordDigest committed.record = committed.address
  fetched : store.fetch committed.address = some (policyRecordCodec.encode committed.record)

/-- A successful source load names the current head of the exact complete
canonical snapshot, with no absent-to-zero shortcut in policy selection. -/
theorem LoadedPolicy.current_head {snapshot : Snapshot} {store : PayloadStore}
    {policyId : PolicyId} {revision : PolicyRevision}
    (loaded : LoadedPolicy snapshot store policyId revision) :
    snapshot.currentHead policyId = some ⟨revision, loaded.committed.address⟩ :=
  snapshot.policy_exact policyId (snapshot.authState.policyEpoch policyId) revision loaded.committed.address loaded.member

/-- Resolve from current canonical authority state, then fetch and decode the
selected source. A store response cannot choose another address or record. -/
def loadPolicy (snapshot : Snapshot) (store : PayloadStore)
    (policyId : PolicyId) (revision : PolicyRevision) : Option (LoadedPolicy snapshot store policyId revision) :=
  let address := snapshot.authState.policyAddress policyId revision
  if current : snapshot.authState.policyRevision policyId = revision then
    if member : snapshot.policyContains policyId (snapshot.authState.policyEpoch policyId) revision address then
      match fetched : store.fetch address with
      | none => none
      | some bytes =>
          match decoded : policyRecordCodec.decode bytes with
          | none => none
          | some record =>
              if policyIdExact : record.policyId = policyId then
                if revisionExact : record.version = revision then
                  if domainExact : record.domain = snapshot.domain then
                    if addressExact : policyRecordDigest record = address then
                      some
                        { committed := ⟨address, record⟩
                          current := current
                          member := member
                          policyIdExact := policyIdExact
                          revisionExact := revisionExact
                          domainExact := domainExact
                          addressExact := addressExact
                          fetched := by
                            have canonical := policyRecordCodec_canonical decoded
                            simpa only [canonical] using fetched }
                    else none
                  else none
                else none
              else none
    else none
  else none

def policyRegistry (snapshot : Snapshot) (store : PayloadStore) : PolicyRegistry where
  resolve := fun policyId revision =>
    (loadPolicy snapshot store policyId revision).map LoadedPolicy.committed

/-- Membership claims name their source role and exact canonical coordinate.
Both roles share the semantic authority root, so the claim is data checked
against that root rather than an independently authoritative host opening. -/
inductive MembershipClaim where
  | policy (identifier : PolicyId) (revision : PolicyRevision)
  | capability (kind : ResourceKind) (identifier : CapabilityId)
  deriving DecidableEq, Repr

def capabilityKindTag : ResourceKind → UInt8
  | .object => 0
  | .account => 1
  | .program => 2

/-- The domain and resource kind join the COMPLETE stored head and ancestry
in one source-owned commitment. This is not a possession proof. -/
def storedCapabilityDigest (snapshot : Snapshot) {kind : ResourceKind}
    (stored : StoredCapability kind) : Digest :=
  (Sp800185Cshake256.hash "DREGG.AUTHORITY.CAPABILITY/v2".toUTF8.toList
    (capabilityKindTag kind ::
      (StreamCodec.product digestStream
        (CredentialAuthorityEntryCodec.storedCapabilityStream kind)).encode
          (snapshot.domain, stored))).digest

/-- Capability commitments include the historical origin data, but not the
current signing-key plane. A fresh invocation still authenticates against
the new snapshot root and the current recipient key. -/
theorem storedCapabilityDigest_eq_of_domain_eq (left right : Snapshot)
    (domain : left.domain = right.domain) {kind : ResourceKind}
    (stored : StoredCapability kind) :
    storedCapabilityDigest left stored = storedCapabilityDigest right stored := by
  simp only [storedCapabilityDigest, domain]

/-- Statement first: checking a capability commitment must recover the exact
stored head at its typed identifier, including the full stored lineage digest.
No finite-hash injectivity or requester-selected membership map is assumed. -/
def CapabilityBound (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) : Prop :=
  ∃ stored, readCapability snapshot.cell kind capability.id = some stored ∧
    stored.head = capability ∧ storedCapabilityDigest snapshot stored = commitment ∧
    LineageValid stored ∧ LineageAnchored snapshot.cell stored

def capabilityCheck (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) : Bool :=
  match readCapability snapshot.cell kind capability.id with
  | none => false
  | some stored => decide (stored.head = capability ∧
      storedCapabilityDigest snapshot stored = commitment) &&
      storedLineageCheck snapshot.cell stored

theorem capabilityCheck_iff (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) :
    capabilityCheck snapshot capability commitment = true ↔
      CapabilityBound snapshot capability commitment := by
  unfold capabilityCheck CapabilityBound
  cases selected : readCapability snapshot.cell kind capability.id <;>
    simp [storedLineageCheck_iff, and_assoc]

/-- Historical grantor-key rotation does not erase the recorded ancestry.
This is a data-check invariance statement; it does not reuse an old signature
receipt at a different authority root. -/
theorem capabilityCheck_eq_of_capability_reads_eq (left right : Snapshot)
    (domain : left.domain = right.domain)
    (same : ∀ readKind identifier, readCapability left.cell readKind identifier =
      readCapability right.cell readKind identifier)
    {kind : ResourceKind} (capability : Capability kind) (commitment : Digest) :
    capabilityCheck left capability commitment =
      capabilityCheck right capability commitment := by
  unfold capabilityCheck
  rw [same kind capability.id]
  cases readCapability right.cell kind capability.id with
  | none => rfl
  | some stored =>
      dsimp only
      rw [storedCapabilityDigest_eq_of_domain_eq left right domain stored,
        storedLineageCheck_congr left.cell right.cell same stored]

/-- Policy and capability claims are checked against their own exact source
coordinates. Policy membership alone never proves capability lookup. -/
def MembershipBound (snapshot : Snapshot) (root address : Digest) :
    MembershipClaim → Prop
  | .policy identifier epoch =>
      root = snapshot.cell.root ∧ snapshot.currentHead identifier = some ⟨epoch, address⟩
  | .capability kind identifier =>
      root = snapshot.cell.root ∧
        (readCapability snapshot.cell kind identifier).any
          (fun stored => storedCapabilityDigest snapshot stored == address) = true

instance membershipBoundDecidable (snapshot : Snapshot) (root address : Digest)
    (claim : MembershipClaim) : Decidable (MembershipBound snapshot root address claim) := by
  cases claim <;> unfold MembershipBound <;> infer_instance

def domainMember (snapshot : Snapshot) (root address : Digest) : Prop :=
  ∃ claim, MembershipBound snapshot root address claim

/-- Issuer evidence is checked against an ACTUAL stored capability and the
current complete-snapshot issuer epoch. It cannot be supplied by a base cache. -/
def issuerCheck (snapshot : Snapshot) (issuer : IssuerId) (epoch : Epoch)
    (commitment : Digest) : Bool :=
  decide (issuerEpochAt snapshot.cell issuer = epoch) &&
    snapshot.entries.any fun entry =>
      match entry with
      | .capability _ stored => decide (stored.head.issuer = issuer ∧
          stored.head.issuerEpoch = epoch ∧
          storedCapabilityDigest snapshot stored = commitment)
      | _ => false

def nonRevocationCheck (snapshot : Snapshot) (root : Digest) (key : RevocationKey) : Bool :=
  decide (root = snapshot.cell.root ∧ key ∈ snapshot.revocationUniverse.revocationKeys ∧
    isRevoked snapshot.cell key = false)

/-- Preserve the supplied cryptographic verifier checks AND require exact
complete-snapshot capability, issuer and revocation data. Membership has a
source-owned typed claim. Capability invocation additionally requires the
shared Evidence capability constructor's exact-request authentication. -/
def domainPortal (snapshot : Snapshot) (base : Portal) : Portal where
  SignatureWitness := base.SignatureWitness
  ProofWitness := base.ProofWitness
  CapabilityCommitmentWitness := base.CapabilityCommitmentWitness
  CapabilityUseWitness := base.CapabilityUseWitness
  MembershipWitness := MembershipClaim
  IssuerWitness := base.IssuerWitness
  NonRevocationWitness := base.NonRevocationWitness
  PolicyWitness := base.PolicyWitness
  policyAddress := base.policyAddress
  verifySignature := base.verifySignature
  verifyProof := base.verifyProof
  verifyCapabilityUse := base.verifyCapabilityUse
  verifyCapabilityCommitment := fun capability commitment witness =>
    base.verifyCapabilityCommitment capability commitment witness &&
      capabilityCheck snapshot capability commitment
  verifyMembership := fun root address claim => decide (MembershipBound snapshot root address claim)
  verifyIssuer := fun issuer epoch commitment witness =>
    base.verifyIssuer issuer epoch commitment witness && issuerCheck snapshot issuer epoch commitment
  verifyNonRevocation := fun root key witness =>
    base.verifyNonRevocation root key witness && nonRevocationCheck snapshot root key
  verifyCommittedPolicy := base.verifyCommittedPolicy

/-- A real stored capability has an inhabited exact membership opening. This
statement does not fabricate a request signature or an accepted action. -/
theorem stored_capability_membership (snapshot : Snapshot) {kind : ResourceKind}
    (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind stored.head.id = some stored) :
    MembershipBound snapshot snapshot.cell.root (storedCapabilityDigest snapshot stored)
      (.capability kind stored.head.id) := by
  simp [MembershipBound, present]

theorem stored_capability_check (snapshot : Snapshot) {kind : ResourceKind}
    (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind stored.head.id = some stored)
    (valid : LineageValid stored) (anchored : LineageAnchored snapshot.cell stored) :
    capabilityCheck snapshot stored.head (storedCapabilityDigest snapshot stored) = true :=
  (capabilityCheck_iff snapshot _ _).mpr ⟨stored, present, rfl, rfl, valid, anchored⟩

theorem no_capability_of_absent (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest)
    (absent : readCapability snapshot.cell kind capability.id = none) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, absent]

theorem no_capability_of_wrong_head (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind capability.id = some stored)
    (wrong : stored.head ≠ capability) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, present, wrong]

theorem no_capability_of_invalid_lineage (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind capability.id = some stored)
    (invalid : ¬LineageValid stored) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, present, storedLineageCheck_refuses_invalid _ _ invalid]

theorem no_capability_of_unanchored_lineage (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind capability.id = some stored)
    (missing : ¬LineageAnchored snapshot.cell stored) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, present, storedLineageCheck_refuses_unanchored _ _ missing]

theorem no_membership_of_wrong_root (snapshot : Snapshot) (root address : Digest)
    (wrong : root ≠ snapshot.cell.root) (claim : MembershipClaim) :
    ¬MembershipBound snapshot root address claim := by
  cases claim <;> exact fun bound => wrong bound.1

/-- Even presenting a policy-role membership opening cannot bypass the
separate exact stored capability lookup in the same receiving portal. -/
theorem domain_capability_requires_stored (snapshot : Snapshot) (base : Portal)
    {kind : ResourceKind} (capability : Capability kind) (commitment : Digest)
    (witness : base.CapabilityCommitmentWitness)
    (accepted : (domainPortal snapshot base).verifyCapabilityCommitment
      capability commitment witness = true) : CapabilityBound snapshot capability commitment := by
  exact (capabilityCheck_iff snapshot _ _).mp (Bool.and_eq_true_iff.mp accepted).2

/-- Full request-bound use of a subject-owned capability. Public stored data
and correct membership do not substitute for the native signature receipt.
Bearer possession has no implementation in this source profile and refuses;
the generic Holder.bearer semantics is unchanged. -/
def capabilityUseCheck (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (capability : Capability kind)
    (commitment : Digest) (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) : Bool :=
  capabilityCheck snapshot capability commitment &&
    match capability.holder with
    | .bearer => false
    | .subject holder =>
        decide (holder = request.subject ∧
          request.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.subject) &&
        CredentialSignatureAdmission.verifySignature snapshot expectedNullifier request receipt

/-- The one native evidence portal used by receiving policy/capability
controllers. Source checks own capability data; the private native receipt
owns invocation authentication. There is no arbitrary positive Boolean,
host-selected verifier, public receipt decoder or generic proof fallback.
The canonical policy compiler replaces the deliberately uninhabited policy
witness below; this base component cannot itself authorize a policy. -/
def sourcePortal (snapshot : Snapshot) (expectedNullifier : Nat) : Portal where
  SignatureWitness := CredentialSignatureAdmission.CheckedSignature snapshot
  ProofWitness := PEmpty
  CapabilityCommitmentWitness := Unit
  CapabilityUseWitness := CredentialSignatureAdmission.CheckedSignature snapshot
  MembershipWitness := MembershipClaim
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := PEmpty
  policyAddress := fun witness => nomatch witness
  verifySignature := CredentialSignatureAdmission.verifySignature snapshot expectedNullifier
  verifyProof := fun _ witness => nomatch witness
  verifyCapabilityCommitment := fun capability commitment _ =>
    capabilityCheck snapshot capability commitment
  verifyCapabilityUse := capabilityUseCheck snapshot expectedNullifier
  verifyMembership := fun root address claim => decide (MembershipBound snapshot root address claim)
  verifyIssuer := fun issuer epoch commitment _ => issuerCheck snapshot issuer epoch commitment
  verifyNonRevocation := fun root key _ => nonRevocationCheck snapshot root key
  verifyCommittedPolicy := fun _ _ _ witness => nomatch witness

/-- Mutation and policy-control receivers require capability authority in the
actual evidence type. Native signatures still authenticate capability use;
they cannot enter through a parallel signature-only evidence constructor. -/
def sourceCapabilityPortal (snapshot : Snapshot) (expectedNullifier : Nat) : Portal :=
  { sourcePortal snapshot expectedNullifier with
    SignatureWitness := PEmpty
    verifySignature := fun _ witness => nomatch witness }

/-- Subject-bound native use retains both exact source capability lookup and
an exact request/nullifier receipt from the selected complete authority state. -/
theorem native_use_request_exact (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (capability : Capability kind)
    (commitment : Digest) (receipt : CredentialSignatureAdmission.CheckedSignature snapshot)
    (accepted : (sourcePortal snapshot expectedNullifier).verifyCapabilityUse
      request capability commitment receipt = true) :
    CapabilityBound snapshot capability commitment ∧
      receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = expectedNullifier := by
  change capabilityUseCheck snapshot expectedNullifier request capability commitment receipt = true at accepted
  unfold capabilityUseCheck at accepted
  have checks := Bool.and_eq_true_iff.mp accepted
  refine ⟨(capabilityCheck_iff snapshot _ _).mp checks.1, ?_⟩
  cases holder : capability.holder with
  | bearer => simp [holder] at accepted
  | subject subject =>
      have use := checks.2
      rw [holder] at use
      have signature := (Bool.and_eq_true_iff.mp use).2
      exact CredentialSignatureAdmission.verified_request_exact
        snapshot expectedNullifier request receipt signature

/-- A mixed lineage does not authenticate the current user as the historical
grantor. The capability's actual recipient and that recipient's current key
epoch are mandatory on the same exact invocation request. -/
theorem native_use_holder_current (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (capability : Capability kind)
    (commitment : Digest) (receipt : CredentialSignatureAdmission.CheckedSignature snapshot)
    (accepted : (sourcePortal snapshot expectedNullifier).verifyCapabilityUse
      request capability commitment receipt = true) :
    capability.holder = .subject request.subject ∧
      request.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.subject := by
  change capabilityUseCheck snapshot expectedNullifier request capability commitment receipt = true at accepted
  unfold capabilityUseCheck at accepted
  have checks := Bool.and_eq_true_iff.mp accepted
  cases holder : capability.holder with
  | bearer => simp [holder] at accepted
  | subject subject =>
      have use := checks.2
      rw [holder] at use
      have current := of_decide_eq_true (Bool.and_eq_true_iff.mp use).1
      exact ⟨congrArg Holder.subject current.1, current.2⟩

theorem native_bearer_use_refused (snapshot : Snapshot) (expectedNullifier : Nat)
    {kind : ResourceKind} (request : Request kind) (capability : Capability kind)
    (commitment : Digest) (receipt : CredentialSignatureAdmission.CheckedSignature snapshot)
    (bearer : capability.holder = .bearer) :
    (sourcePortal snapshot expectedNullifier).verifyCapabilityUse
      request capability commitment receipt = false := by
  simp [sourcePortal, capabilityUseCheck, bearer]

/-- The receiving constructor requires the exact source-derived candidate
context. Its signature contains no binding-mode selector, digest callback or
predicate-view callback. -/
def config {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal)
    (step : PolicyStepContext) : CanonicalPolicyConfig F where
  base := domainPortal snapshot base
  registry := policyRegistry snapshot store
  recordDigest := policyRecordDigest
  stepBinding := .canonical step
  compilerProfile := profile

/-- Execute the existing semantic capability decider and every mandatory
portal check against the exact old snapshot. The returned evidence is already
for the canonical policy portal, so an upper controller cannot replace it by
an unrelated signature-mode token while claiming capability invocation. -/
private def capabilityEvidenceChecked {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness) :
    Option { evidence : Evidence (config (F := F) profile snapshot store base step).portal snapshot.authState request //
      ∃ stored, readCapability snapshot.cell kind identifier = some stored ∧
        evidence.capabilityValue = some (stored.head, storedCapabilityDigest snapshot stored) } :=
  match readCapability snapshot.cell kind identifier with
  | none => none
  | some stored =>
    let capability := stored.head
    let commitment := storedCapabilityDigest snapshot stored
    let portal := (config (F := F) profile snapshot store base step).portal
    if semantic : AuthorizationDeclaration.capabilityAdmissibleCheck capability snapshot.authState request = true then
      if used : portal.verifyCapabilityUse request capability commitment useWitness = true then
        if committed : portal.verifyCapabilityCommitment capability commitment commitmentWitness = true then
          if member : portal.verifyMembership snapshot.authState.capabilityRoot commitment
              (.capability kind capability.id) = true then
            if issuer : portal.verifyIssuer capability.issuer capability.issuerEpoch commitment issuerWitness = true then
              if self : portal.verifyNonRevocation snapshot.authState.revocationRoot
                  (.capability capability.id) (revocationWitness (.capability capability.id)) = true then
                if ancestors : ∀ identifier ∈ capability.ancestors,
                    portal.verifyNonRevocation snapshot.authState.revocationRoot (.capability identifier)
                      (revocationWitness (.capability identifier)) = true then
                  if channels : ∀ channel ∈ capability.channels,
                      portal.verifyNonRevocation snapshot.authState.revocationRoot (.channel channel)
                        (revocationWitness (.channel channel)) = true then
                    some ⟨(.capability capability commitment commitmentWitness
                      (.capability kind capability.id) issuerWitness
                      (revocationWitness (.capability capability.id)) useWitness
                      ((AuthorizationDeclaration.capabilityAdmissibleCheck_eq_true_iff
                        capability snapshot.authState request).mp semantic)
                      used committed member issuer self
                      (fun identifier member => ⟨revocationWitness (.capability identifier), ancestors identifier member⟩)
                      (fun channel member => ⟨revocationWitness (.channel channel), channels channel member⟩)),
                      ⟨stored, rfl, rfl⟩⟩
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    else none

/-- The single receiving constructor projects evidence from the checked source
result. Its erased proof records the exact parent lookup at the construction
site, while all semantic, native-use, membership and revocation gates above
remain mandatory. -/
def capabilityEvidence {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness) :
    Option (Evidence (config (F := F) profile snapshot store base step).portal snapshot.authState request) :=
  (capabilityEvidenceChecked profile snapshot store base step request identifier
    commitmentWitness useWitness issuerWitness revocationWitness).map Subtype.val

/-- Success preserves the exact storage lookup at the caller's identifier and
returns that stored head with its complete source-owned lineage commitment.
This is the shared constructor's identity law, not an endpoint-specific check. -/
theorem capabilityEvidence_success {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness)
    {evidence : Evidence (config (F := F) profile snapshot store base step).portal
      snapshot.authState request}
    (accepted : capabilityEvidence profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness = some evidence) :
    ∃ stored, readCapability snapshot.cell kind identifier = some stored ∧
      evidence.capabilityValue = some (stored.head, storedCapabilityDigest snapshot stored) := by
  unfold capabilityEvidence at accepted
  obtain ⟨checked, _, equal⟩ := Option.map_eq_some_iff.mp accepted
  rw [← equal]
  exact checked.property

/-- Native receiving convenience: data openings come from the complete
snapshot; invocation authentication comes only from the checked native receipt. -/
def sourceCapabilityEvidence {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Option (Evidence (config (F := F) profile snapshot store
      (sourcePortal snapshot expectedNullifier) step).portal snapshot.authState request) :=
  capabilityEvidence profile snapshot store (sourcePortal snapshot expectedNullifier) step
    request identifier () receipt () (fun _ => ())

/-- The same shared source checks for receivers whose type requires ownership
capability evidence, rather than allowing a signature-mode alternative. -/
def sourceCapabilityOnlyEvidence {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Option (Evidence (config (F := F) profile snapshot store
      (sourceCapabilityPortal snapshot expectedNullifier) step).portal snapshot.authState request) :=
  capabilityEvidence profile snapshot store (sourceCapabilityPortal snapshot expectedNullifier) step
    request identifier () receipt () (fun _ => ())

/-- The native capability-only helper names exactly the requested parent
record. Invocation authentication remains the current holder's checked receipt. -/
theorem sourceCapabilityOnlyEvidence_names_parent
    {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) (snapshot : Snapshot) (store : PayloadStore)
    (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot)
    {evidence : Evidence (config (F := F) profile snapshot store
      (sourceCapabilityPortal snapshot expectedNullifier) step).portal snapshot.authState request}
    (accepted : sourceCapabilityOnlyEvidence profile snapshot store expectedNullifier step
      request identifier receipt = some evidence) :
    ∃ stored, readCapability snapshot.cell kind identifier = some stored ∧
      evidence.capabilityValue = some (stored.head, storedCapabilityDigest snapshot stored) :=
  capabilityEvidence_success profile snapshot store
    (sourceCapabilityPortal snapshot expectedNullifier) step request identifier
    () receipt () (fun _ => ()) accepted

theorem source_capability_only_mode {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) (snapshot : Snapshot) (store : PayloadStore)
    (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence (config profile snapshot store
      (sourceCapabilityPortal snapshot expectedNullifier) step).portal snapshot.authState request) :
    ∃ capability commitment, evidence.capabilityValue = some (capability, commitment) := by
  cases evidence with
  | signature witness _ _ => exact nomatch witness
  | proof witness _ => exact nomatch witness
  | capability capability commitment _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨capability, commitment, rfl⟩

theorem source_capability_only_requires_native_request
    {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) (snapshot : Snapshot) (store : PayloadStore)
    (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence (config profile snapshot store
      (sourceCapabilityPortal snapshot expectedNullifier) step).portal snapshot.authState request) :
    ∃ capability commitment,
      evidence.capabilityValue = some (capability, commitment) ∧
      CapabilityBound snapshot capability commitment ∧
      ∃ receipt : CredentialSignatureAdmission.CheckedSignature snapshot,
        receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = expectedNullifier := by
  obtain ⟨capability, commitment, named⟩ :=
    source_capability_only_mode profile snapshot store expectedNullifier step evidence
  obtain ⟨receipt, verified⟩ :=
    capability_evidence_requires_use evidence capability commitment named
  have pinned := native_use_request_exact snapshot expectedNullifier
    request capability commitment receipt verified
  exact ⟨capability, commitment, named, pinned.1, receipt, pinned.2⟩

/-- The actual compiled-policy receiving portal cannot erase native
capability possession. Any capability-mode evidence, even if assembled
without the convenience helper, retains both source lookup and a private
receipt for the exact request and shared operation marker. -/
theorem source_capability_evidence_requires_native_request
    {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) (snapshot : Snapshot) (store : PayloadStore)
    (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence (config profile snapshot store
      (sourcePortal snapshot expectedNullifier) step).portal snapshot.authState request)
    (capability : Capability kind) (commitment : Digest)
    (named : evidence.capabilityValue = some (capability, commitment)) :
    CapabilityBound snapshot capability commitment ∧
      ∃ receipt : CredentialSignatureAdmission.CheckedSignature snapshot,
        receipt.request = ⟨kind, request⟩ ∧ receipt.nullifier = expectedNullifier := by
  obtain ⟨receipt, verified⟩ :=
    capability_evidence_requires_use evidence capability commitment named
  have pinned := native_use_request_exact snapshot expectedNullifier
    request capability commitment receipt verified
  exact ⟨pinned.1, receipt, pinned.2⟩

@[simp] theorem config_uses_canonical {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    (config (F := F) profile snapshot store base step).stepBinding = .canonical step := rfl

def contentAddressing {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    ContentAddressing (config (F := F) profile snapshot store base step) where
  codec := policyRecordCodec
  hashBytes := policyHashBytes
  recordDigest_exact := by intro record; rfl

/-- Availability for resolved records is proved from the same checked fetch,
not assumed for an independent logical registry. -/
def payloadAvailability {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    PayloadAvailability (config (F := F) profile snapshot store base step)
      (contentAddressing profile snapshot store base step) store where
  fetch_resolved := by
    intro policyId epoch committed resolved
    cases loaded : loadPolicy snapshot store policyId epoch with
    | none => simp [config, policyRegistry, loaded] at resolved
    | some value =>
        have equal : value.committed = committed := by
          simpa [config, policyRegistry, loaded] using resolved
        simpa only [equal] using value.fetched

def membershipSemantics {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    MembershipSemantics (config (F := F) profile snapshot store base step).portal where
  Member := domainMember snapshot
  verifier_sound := by
    intro root address witness accepted
    exact ⟨witness, of_decide_eq_true accepted⟩

/-! ## Explicit model examples of selection and stale-guard rejection

The examples below keep the older small-field model parameters to exercise
the generic kernel theorems. The receiving constructor above never selects
their model binding or fixed registry.
-/
namespace Example

/-- The bounded-page projection belongs only to this explicit model. -/
def projection := CredentialAuthorityPageMaterializer.projection


def committedPolicy : CommittedPolicy where
  address := policyRecordDigest demoRecord
  record := demoRecord

def policyEntry : Entry :=
  .policy demoRequest.policyId demoRequest.policyEpoch demoRequest.policyRevision committedPolicy.address

def policyPage : Page where
  authorityDomain := ⟨91000⟩
  pageNumber := 0
  slot0 := some policyEntry
  slot1 := none
  slot2 := none
  slot3 := none

def policyPageCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some policyPage))

theorem policyPage_valid : policyPage.Valid := by
  simp [Page.Valid, Page.fields, Page.entries, policyPage, policyEntry, Entry.fields]

@[simp] theorem policyPage_contains : policyPage.Contains policyEntry := by
  simp [Page.Contains, Page.entries, policyPage]

@[simp] theorem policyPage_revision_exact :
    policyPage.policyRevisionAt demoRequest.policyId = demoRequest.policyRevision := by
  simp [Page.policyRevisionAt, Page.toCanonicalState, Page.entries, policyPage,
    policyEntry, Entry.install]
  rfl

@[simp] theorem policyPage_address_exact :
    policyPage.policyAddressAt demoRequest.policyId demoRequest.policyRevision =
      committedPolicy.address := by
  simp [Page.policyAddressAt, Page.toCanonicalState, Page.entries, policyPage,
    policyEntry, Entry.install]
  rfl

@[simp] theorem policyPageCell_bytes :
    policyPageCell.bytes = wireFrame ++ 1 :: pageStream.encode policyPage :=
  rfl

/-! ## The physical page is the canonical authority cell -/

/-- The registry consumes the actual materializer; there is no focused
encoding, countable fallback, or second synthetic cell for its projection. -/
def authorityMaterializer := CredentialAuthorityPageMaterializer.materializer

def authorityCell : RegistryCell authorityMaterializer := policyPageCell

@[simp] theorem authorityCell_bytes_exact :
    authorityCell.bytes = policyPageCell.bytes := rfl

@[simp] theorem authorityCell_root_exact :
    authorityCell.root = policyPageCell.root := rfl

@[simp] theorem authorityCell_revision_exact :
    (projection.authState authorityCell).policyRevision
        demoRequest.policyId = demoRequest.policyRevision := by
  change (some demoRequest.policyRevision).getD 0 = demoRequest.policyRevision
  rfl

@[simp] theorem authorityCell_address_exact :
    addressAt projection authorityCell demoRequest.policyId demoRequest.policyRevision =
      committedPolicy.address := by
  change (some committedPolicy.address).getD ⟨0⟩ = committedPolicy.address
  rfl

/-! ## Page membership, registry, and compiler admission -/

/-- The inherited portal owns every non-membership verifier.  Page membership
is replaced by an exact decidable reading of this page and root.  Therefore no
signature acceptance or signature-soundness theorem is synthesized here. -/
def pagePortal (base : Portal) : Portal where
  SignatureWitness := base.SignatureWitness
  ProofWitness := base.ProofWitness
  CapabilityCommitmentWitness := base.CapabilityCommitmentWitness
  CapabilityUseWitness := base.CapabilityUseWitness
  MembershipWitness := Unit
  IssuerWitness := base.IssuerWitness
  NonRevocationWitness := base.NonRevocationWitness
  PolicyWitness := base.PolicyWitness
  policyAddress := base.policyAddress
  verifySignature := base.verifySignature
  verifyProof := base.verifyProof
  verifyCapabilityUse := base.verifyCapabilityUse
  verifyCapabilityCommitment := base.verifyCapabilityCommitment
  verifyMembership := fun root address _ =>
    decide (root = policyPageCell.root /\
      address = committedPolicy.address /\ policyPage.Contains policyEntry)
  verifyIssuer := base.verifyIssuer
  verifyNonRevocation := base.verifyNonRevocation
  verifyCommittedPolicy := base.verifyCommittedPolicy

def policyRegistry : PolicyRegistry where
  resolve := fun policyId epoch =>
    if policyId = demoRequest.policyId /\ epoch = demoRequest.policyRevision then
      some committedPolicy
    else none

def config (base : Portal) : CanonicalPolicyConfig (ZMod 13) where
  base := pagePortal base
  registry := policyRegistry
  recordDigest := policyRecordDigest
  stepBinding := .model demoStateDigest demoStepDigest
  compilerProfile := .researchDisabled demoRequest.semantics

@[simp] theorem config_verifyMembership (base : Portal)
    (root address : Digest) :
    (config base).portal.verifyMembership root address () =
      decide (root = policyPageCell.root /\
        address = committedPolicy.address /\ policyPage.Contains policyEntry) :=
  rfl

@[simp] theorem registry_resolves (base : Portal) :
    (config base).registry.resolve demoRequest.policyId demoRequest.policyRevision =
      some committedPolicy := by
  simp [config, policyRegistry]

def contentAddressing (base : Portal) :
    ContentAddressing (config base) where
  codec := policyRecordCodec
  hashBytes := policyHashBytes
  recordDigest_exact := by intro record; rfl

def payloadStore : PayloadStore where
  fetch := fun address =>
    if address = committedPolicy.address then
      some (policyRecordCodec.encode committedPolicy.record)
    else none

noncomputable def payloadAvailability (base : Portal) :
    PayloadAvailability (config base) (contentAddressing base) payloadStore where
  fetch_resolved := by
    intro policyId epoch selected resolved
    by_cases key :
        policyId = demoRequest.policyId /\ epoch = demoRequest.policyRevision
    · have selectedExact : selected = committedPolicy := by
        have reverse : committedPolicy = selected := by
          simpa [config, policyRegistry, key] using resolved
        exact reverse.symm
      subst selected
      change payloadStore.fetch committedPolicy.address =
        some ((contentAddressing base).codec.encode committedPolicy.record)
      simp [payloadStore, contentAddressing]
    · simp [config, policyRegistry, key] at resolved

def pageMember (root address : Digest) : Prop :=
  root = policyPageCell.root /\ address = committedPolicy.address /\
    policyPage.Contains policyEntry

noncomputable instance pageMemberDecidable (root address : Digest) :
    Decidable (pageMember root address) :=
  Classical.propDecidable _

noncomputable def membershipSemantics (base : Portal) :
    MembershipSemantics (config base).portal where
  Member := pageMember
  verifier_sound := by
    intro root address witness accepted
    have claim : root = policyPageCell.root /\
        address = committedPolicy.address /\ policyPage.Contains policyEntry := by
      apply of_decide_eq_true
      simpa only [config_verifyMembership] using accepted
    exact claim

noncomputable def policyWitness : CompiledPolicyWitness (ZMod 13) :=
  canonicalWitness CompilerProfile.disabled committedPolicy kOld kNew

theorem policy_verifies (base : Portal) :
    (config base).verifies demoRequest policyWitness = true := by
  have stepExact :
      (config base).stepBinding.matches demoRequest kOld kNew = true := by
    simp [config, PolicyStepBinding.matches, demoStateDigest, demoStepDigest]
  apply (canonical_verifies_iff_eval
    (config := config base) (request := demoRequest)
    (committed := committedPolicy) (oldState := kOld) (newState := kNew)
    (resolved := registry_resolves base)
    (policyIdExact := rfl) (versionExact := rfl)
    (domainExact := rfl) (semanticsExact := rfl)
    (recordDigestExact := rfl)
    (stepExact := stepExact)
    (profileCompatible := rfl) (profileSemanticsExact := rfl)
    (supportedExact := by change supported CompilerProfile.disabled kPol = true; decide)
    (rangesExact := by change inputsInRange CompilerProfile.disabled kPol kOld kNew = true; decide)
    (castExact := by decide)).mpr
  decide

theorem page_membership_verified (base : Portal) :
    (config base).portal.verifyMembership authorityCell.root
      committedPolicy.address () = true := by
  rw [config_verifyMembership]
  apply decide_eq_true
  exact ⟨authorityCell_root_exact, rfl, policyPage_contains⟩

/-- Positive committed authorization.  The non-policy proof witness and its
acceptance are explicit inputs from `base`; this construction proves only the
policy/page join and makes no signature claim. -/
noncomputable def positiveAuthorized
    (base : Portal) (proofWitness : base.ProofWitness)
    (proofAccepted : base.verifyProof demoRequest proofWitness = true) :
    CanonicalAuthorized (config base)
      (projection.authState authorityCell)
      demoRequest where
  evidence := .proof proofWitness (by
    simpa [config, CanonicalPolicyConfig.portal, pagePortal] using proofAccepted)
  policyWitness := policyWitness
  policyMembershipWitness := ()
  policyEpochExact := by
    change demoRequest.policyEpoch = (some demoRequest.policyEpoch).getD 0
    rfl
  policyRevisionExact := by
    exact authorityCell_revision_exact.symm
  policyAddressExact := by
    change committedPolicy.address =
      addressAt projection authorityCell demoRequest.policyId demoRequest.policyRevision
    exact authorityCell_address_exact.symm
  policyMembershipVerified := by
    change (config base).portal.verifyMembership authorityCell.root
      (addressAt projection authorityCell demoRequest.policyId demoRequest.policyRevision)
      () = true
    rw [authorityCell_address_exact]
    exact page_membership_verified base
  policyVerified := by
    rw [portal_verifyCommittedPolicy]
    rw [Bool.and_eq_true]
    refine ⟨?_, policy_verifies base⟩
    apply decide_eq_true
    change addressAt projection authorityCell demoRequest.policyId demoRequest.policyRevision =
      committedPolicy.address
    exact authorityCell_address_exact

/-- The concrete page produces the kernel's full proof-relevant selection:
canonical bytes, cSHAKE address, fetched source, exact page membership, and the
accepted source predicate all refer to the same `committedPolicy`. -/
noncomputable def selectedPayload
    (base : Portal) (proofWitness : base.ProofWitness)
    (proofAccepted : base.verifyProof demoRequest proofWitness = true) :
    SelectionPayload (config base) (contentAddressing base) payloadStore
      (membershipSemantics base) projection authorityCell demoRequest
      (positiveAuthorized base proofWitness proofAccepted) :=
  SelectionPayload.ofAuthorized (availability := payloadAvailability base)
    (positiveAuthorized base proofWitness proofAccepted)
    committedPolicy (registry_resolves base)

/-! ## The concrete page root is the durable read guard -/

def registryCellId : CellId := ⟨91010⟩
def dataCellId : CellId := ⟨91011⟩

def dataPreBytes : List UInt8 := [1, 2, 3]
def dataPostBytes : List UInt8 := [1, 2, 3, 4]

def dataWrite : DataWrite where
  cellId := dataCellId
  expectedPre := CredentialAuthorityPageMaterializer.rootBytes dataPreBytes
  exactPost := CredentialAuthorityPageMaterializer.rootBytes dataPostBytes
  canonicalPostBytes := dataPostBytes

def event : StableEvent where
  codecVersion := 1
  domain := ⟨91020⟩
  eventId := ⟨91021⟩
  canonicalBytes := [80, 79, 76, 73, 67, 89]

def baseIntent : DataIntent CredentialAuthorityPageMaterializer.rootBytes where
  transactionId := ⟨91030⟩
  writes := [dataWrite]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := event
  postRootsBound := by
    intro write member
    simp only [List.mem_singleton] at member
    subst write
    rfl
  guardsReadOnly := by simp

theorem registryCell_readOnly :
    registryCellId ∉ baseIntent.writes.map DataWrite.cellId := by
  decide

def sharedDigest :
    SharedDigest authorityMaterializer
      CredentialAuthorityPageMaterializer.rootBytes :=
  ⟨rfl⟩

noncomputable def guardedIntent :
    DataIntent CredentialAuthorityPageMaterializer.rootBytes :=
  guardPolicyRegistry authorityCell registryCellId sharedDigest baseIntent
    registryCell_readOnly

noncomputable def snapshotBytes (cellId : CellId) : List UInt8 :=
  if cellId = dataCellId then dataPreBytes
  else if cellId = registryCellId then policyPageCell.bytes
  else []

noncomputable def readySnapshot :
    DataSnapshot CredentialAuthorityPageMaterializer.rootBytes where
  model :=
    { roots := fun cellId =>
        CredentialAuthorityPageMaterializer.rootBytes (snapshotBytes cellId)
      consumed := fun _ => false
      available := 0
      history := []
      journal := [] }
  canonicalBytes := snapshotBytes
  coherent := by intro cellId; rfl

@[simp] theorem readySnapshot_registry_root :
    readySnapshot.model.roots registryCellId = authorityCell.root := by
  change CredentialAuthorityPageMaterializer.rootBytes
      (snapshotBytes registryCellId) = authorityCell.root
  have bytesExact : snapshotBytes registryCellId = policyPageCell.bytes := by
    simp [snapshotBytes, registryCellId, dataCellId]
  rw [bytesExact]
  exact authorityCell_root_exact.symm

theorem baseIntent_ready : baseIntent.preflight readySnapshot = .ok () := by
  have rootsReady :
      baseIntent.erase.rootsMatchCheck readySnapshot.model = true := by
    apply (Minidregg.Kernel.DurableCommitProtocol.Intent.rootsMatchCheck_eq_true_iff
      readySnapshot.model baseIntent.erase).mpr
    intro write member
    simp only [baseIntent, DataIntent.erase, List.map_singleton,
      List.mem_singleton] at member
    subst write
    change CredentialAuthorityPageMaterializer.rootBytes
        (snapshotBytes dataCellId) =
      CredentialAuthorityPageMaterializer.rootBytes dataPreBytes
    have bytesExact : snapshotBytes dataCellId = dataPreBytes := by
      simp [snapshotBytes, dataCellId]
    rw [bytesExact]
  have nullifiersReady :
      baseIntent.erase.nullifiersFreshCheck readySnapshot.model = true := by
    apply (Minidregg.Kernel.DurableCommitProtocol.Intent.nullifiersFreshCheck_eq_true_iff
      readySnapshot.model baseIntent.erase).mpr
    simp [baseIntent, DataIntent.erase]
  have funded : Charge.fundedCheck baseIntent.exactCharge
      readySnapshot.model.available = true := by
    apply (Charge.fundedCheck_eq_true_iff _ _).mpr
    intro lane
    rfl
  have durableReady :
      baseIntent.erase.preflight readySnapshot.model = .ok () := by
    unfold Minidregg.Kernel.DurableCommitProtocol.Intent.preflight
    rw [if_neg (by simp [baseIntent, DataIntent.erase])]
    rw [if_neg (by simp [baseIntent, DataIntent.erase])]
    rw [if_neg (by simp [baseIntent, DataIntent.erase])]
    rw [if_neg (by simp [rootsReady])]
    rw [if_neg (by simp [nullifiersReady])]
    have erasedFunded : Charge.fundedCheck baseIntent.erase.exactCharge
        readySnapshot.model.available = true := funded
    rw [erasedFunded]
    rfl
  have guardsReady :
      baseIntent.readGuardsMatchCheck readySnapshot = true := rfl
  unfold DataIntent.preflight
  rw [guardsReady]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [durableReady]

theorem guardedIntent_ready : guardedIntent.preflight readySnapshot = .ok () :=
  guardPolicyRegistry_preflight_ready authorityCell registryCellId sharedDigest
    baseIntent registryCell_readOnly readySnapshot readySnapshot_registry_root
    baseIntent_ready

/-! ## Pair-bound page rotation rejects the old authorization intent -/

noncomputable def rotatedPolicyEntry : Entry :=
  .policy demoRequest.policyId demoRequest.policyEpoch (demoRequest.policyRevision + 1) ⟨91040⟩

noncomputable def rotatedPage : Page :=
  { policyPage with slot0 := some rotatedPolicyEntry }

noncomputable def rotatedPageCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some rotatedPage))

theorem selected_rotated_states_ne :
    stateOfOption (some policyPage) ≠ stateOfOption (some rotatedPage) := by
  intro equal
  have pages := congrArg pageAt equal
  simp only [pageAt, stateOfOption] at pages
  have pageExact : policyPage = rotatedPage := Option.some.inj pages
  have slots := congrArg Page.slot0 pageExact
  simp [policyPage, rotatedPage, policyEntry, rotatedPolicyEntry] at slots

theorem rotated_root_ne
    (binding : PairBindingPremise
      (stateOfOption (some policyPage)) (stateOfOption (some rotatedPage))) :
    rotatedPageCell.root ≠ policyPageCell.root := by
  intro rootsEqual
  apply selected_rotated_states_ne
  apply state_eq_of_root_eq binding
  simpa [rotatedPageCell, policyPageCell, materializer] using rootsEqual.symm

noncomputable def rotatedSnapshotBytes (cellId : CellId) : List UInt8 :=
  if cellId = registryCellId then rotatedPageCell.bytes
  else snapshotBytes cellId

noncomputable def rotatedSnapshot :
    DataSnapshot CredentialAuthorityPageMaterializer.rootBytes where
  model :=
    { roots := fun cellId =>
        CredentialAuthorityPageMaterializer.rootBytes (rotatedSnapshotBytes cellId)
      consumed := fun _ => false
      available := 0
      history := []
      journal := [] }
  canonicalBytes := rotatedSnapshotBytes
  coherent := by intro cellId; rfl

theorem rotatedSnapshot_moved
    (binding : PairBindingPremise
      (stateOfOption (some policyPage)) (stateOfOption (some rotatedPage))) :
    rotatedSnapshot.model.roots registryCellId ≠ authorityCell.root := by
  simpa [rotatedSnapshot, rotatedSnapshotBytes] using rotated_root_ne binding

/-- Stale page-update tooth.  A policy revision/address rotation changes the
pair-bound page root, so the old content+authorization intent is rejected at
the read guard before its data write can be installed. -/
theorem rotated_page_rejects_old_intent
    (binding : PairBindingPremise
      (stateOfOption (some policyPage)) (stateOfOption (some rotatedPage))) :
    guardedIntent.preflight rotatedSnapshot = .error .staleReadGuard :=
  policy_registry_rotation_rejects_old_intent authorityCell registryCellId
    sharedDigest baseIntent registryCell_readOnly rotatedSnapshot
      (rotatedSnapshot_moved binding)

/-! ## Explicit physical ceiling -/

/-- A physical deployment does not inherit atomicity from the model by name;
it must provide exactly this simulation premise. -/
abbrev PhysicalAtomicityPremise
    (PhysicalState : Type) (PhysicalStep : PhysicalState ->
      DataIntent CredentialAuthorityPageMaterializer.rootBytes ->
      PhysicalState -> Type)
    (Represents : PhysicalState ->
      DataSnapshot CredentialAuthorityPageMaterializer.rootBytes -> Prop) :=
  ImplementationRefinement CredentialAuthorityPageMaterializer.rootBytes
    PhysicalState PhysicalStep Represents

end Example
end Minidregg.Compiler.CredentialAuthorityPolicyRegistry

/-! Concrete join audit. -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.positiveAuthorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.positiveAuthorized
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.selectedPayload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.selectedPayload
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.guardedIntent_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.guardedIntent_ready
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.rotated_page_rejects_old_intent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.rotated_page_rejects_old_intent
