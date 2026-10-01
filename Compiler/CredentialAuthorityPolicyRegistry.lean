/-
# Compiler.CredentialAuthorityPolicyRegistry -- complete authority selects policy

The receiving registry consumes the complete canonical authority domain. Its
policy source is the executable canonical v2 record, addressed by cSHAKE. The
current source revision, selected address, membership, and all authority epochs come
from that same snapshot: the deployment's one authority cell. The physical
receiver supplies that cell's provenance; semantic source bytes alone cannot
reconstruct it.

The explicit Example namespace instantiates the generic selection and
stale-guard theorems at one concrete authority cell. It is not a receiving
configuration or decoder fallback. Signature verification remains the
deployment portal's responsibility.
-/
import Compiler.CredentialAuthorityDomain
import Compiler.PolicyRecordCodec
import Compiler.CredentialSignatureAdmission
import Theory.CredentialLineageAdmission
import Kernel.CanonicalPolicyRegistry
import Compiler.RefusalReason

namespace Minidregg.Compiler.CredentialAuthorityPolicyRegistry

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
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
    LineageValid snapshot.authState.parent stored ∧ LineageAnchored snapshot.cell stored

def capabilityCheck (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) : Bool :=
  match readCapability snapshot.cell kind capability.id with
  | none => false
  | some stored => decide (stored.head = capability ∧
      storedCapabilityDigest snapshot stored = commitment) &&
      storedLineageCheck snapshot.cell snapshot.authState.parent stored

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
    (parents : ∀ cell, left.cell.logical ⟨.parent, cell⟩ = right.cell.logical ⟨.parent, cell⟩)
    {kind : ResourceKind} (capability : Capability kind) (commitment : Digest) :
    capabilityCheck left capability commitment =
      capabilityCheck right capability commitment := by
  unfold capabilityCheck
  rw [same kind capability.id, CredentialAuthorityDomain.Snapshot.authState_parent,
    CredentialAuthorityDomain.Snapshot.authState_parent,
    CredentialAuthorityState.parentageOf_congr parents]
  cases readCapability right.cell kind capability.id with
  | none => rfl
  | some stored =>
      dsimp only
      rw [storedCapabilityDigest_eq_of_domain_eq left right domain stored,
        storedLineageCheck_congr left.cell right.cell same _ stored]

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

/-- One stored capability, read at its own address, that was issued by
`issuer` at `epoch` and commits to `commitment`. -/
def issuedAt (snapshot : Snapshot) (issuer : IssuerId) (epoch : Epoch)
    (commitment : Digest) : Store.Address CredentialAuthorityState.layout → Bool
  | ⟨.capability kind, identifier⟩ =>
      match readCapability snapshot.cell kind identifier with
      | some stored => decide (stored.head.issuer = issuer ∧
          stored.head.issuerEpoch = epoch ∧
          storedCapabilityDigest snapshot stored = commitment)
      | none => false
  | _ => false

/-- Issuer evidence is checked against an ACTUAL stored capability and the
current complete-snapshot issuer epoch. It cannot be supplied by a base cache.
The search ranges over the cell's finite support. -/
def issuerCheck (snapshot : Snapshot) (issuer : IssuerId) (epoch : Epoch)
    (commitment : Digest) : Bool :=
  decide (issuerEpochAt snapshot.cell issuer = epoch) &&
    decide (∃ address ∈ snapshot.logical.support,
      issuedAt snapshot issuer epoch commitment address = true)

/-- Issuer acceptance names a stored capability of that issuer and epoch. -/
theorem issuerCheck_sound (snapshot : Snapshot) (issuer : IssuerId) (epoch : Epoch)
    (commitment : Digest) (accepted : issuerCheck snapshot issuer epoch commitment = true) :
    issuerEpochAt snapshot.cell issuer = epoch ∧
      ∃ kind identifier stored, readCapability snapshot.cell kind identifier = some stored ∧
        stored.head.issuer = issuer ∧ stored.head.issuerEpoch = epoch ∧
        storedCapabilityDigest snapshot stored = commitment := by
  simp only [issuerCheck, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨current, ⟨plane, identifier⟩, _, issued⟩ := accepted
  refine ⟨current, ?_⟩
  cases plane with
  | capability kind =>
      simp only [issuedAt] at issued
      cases read : readCapability snapshot.cell kind identifier with
      | none => simp [read] at issued
      | some stored =>
          simp only [read, decide_eq_true_eq] at issued
          exact ⟨kind, identifier, stored, read, issued⟩
  | _ => simp [issuedAt] at issued

/-- A stored capability of the current issuer epoch is found. -/
theorem issuerCheck_complete (snapshot : Snapshot) {kind : ResourceKind}
    (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind stored.head.id = some stored)
    (current : issuerEpochAt snapshot.cell stored.head.issuer = stored.head.issuerEpoch) :
    issuerCheck snapshot stored.head.issuer stored.head.issuerEpoch
      (storedCapabilityDigest snapshot stored) = true := by
  simp only [issuerCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨current, ⟨.capability kind, stored.head.id⟩, ?_, ?_⟩
  · rw [DFinsupp.mem_support_iff]
    change readCapability snapshot.cell kind stored.head.id ≠ none
    rw [present]; simp
  · simp [issuedAt, present]

/-- Non-revocation at the exact root: the key is registered and not revoked, both
read from the cell's presence planes.  There is no key list beside them. -/
def nonRevocationCheck (snapshot : Snapshot) (root : Digest) (key : RevocationKey) : Bool :=
  decide (root = snapshot.cell.root ∧ isRegistered snapshot.cell key = true ∧
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
    (valid : LineageValid snapshot.authState.parent stored)
    (anchored : LineageAnchored snapshot.cell stored) :
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
    (invalid : ¬LineageValid snapshot.authState.parent stored) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, present, storedLineageCheck_refuses_invalid _ _ _ invalid]

theorem no_capability_of_unanchored_lineage (snapshot : Snapshot) {kind : ResourceKind}
    (capability : Capability kind) (commitment : Digest) (stored : StoredCapability kind)
    (present : readCapability snapshot.cell kind capability.id = some stored)
    (missing : ¬LineageAnchored snapshot.cell stored) :
    capabilityCheck snapshot capability commitment = false := by
  simp [capabilityCheck, present, storedLineageCheck_refuses_unanchored _ _ _ missing]

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

/-- The evidence names exactly the stored capability at the caller's identifier.
Named so that the checked constructor's result type does not mention its own
lookup syntactically. -/
def NamesStored {portal : Portal} {state : AuthState} {kind : ResourceKind} {request : Request kind}
    (snapshot : Snapshot) (identifier : CapabilityId) (evidence : Evidence portal state request) : Prop :=
  ∃ stored, readCapability snapshot.cell kind identifier = some stored ∧
    evidence.capabilityValue = some (stored.head, storedCapabilityDigest snapshot stored)

/-- Execute the existing semantic capability decider and every mandatory
portal check against the exact old snapshot. The returned evidence is already
for the canonical policy portal, so an upper controller cannot replace it by
an unrelated signature-mode token while claiming capability invocation.

Each refusing branch names its reason. Absence, a failed native use and every
holder/scope failure are `noGrant`, and they are decided before any other
component, so only the capability's own holder can learn that it is revoked,
outside its window or stale (`RefusalReason.capabilityRefusal`). -/
private def capabilityEvidenceChecked {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness) :
    Except RefusalReason
      { evidence : Evidence (config (F := F) profile snapshot store base step).portal snapshot.authState request //
        NamesStored snapshot identifier evidence } :=
  match found : readCapability snapshot.cell kind identifier with
  | none => .error .noGrant
  | some stored =>
    let capability := stored.head
    let commitment := storedCapabilityDigest snapshot stored
    let portal := (config (F := F) profile snapshot store base step).portal
    if used : portal.verifyCapabilityUse request capability commitment useWitness = true then
      match refusal : RefusalReason.capabilityRefusal capability snapshot.authState request with
      | some reason => .error reason
      | none =>
        have semantic : AuthorizationDeclaration.capabilityAdmissibleCheck capability
            snapshot.authState request = true :=
          (RefusalReason.capabilityRefusal_eq_none_iff capability snapshot.authState request).mp refusal
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
                    .ok ⟨(.capability capability commitment commitmentWitness
                      (.capability kind capability.id) issuerWitness
                      (revocationWitness (.capability capability.id)) useWitness
                      ((AuthorizationDeclaration.capabilityAdmissibleCheck_eq_true_iff
                        capability snapshot.authState request).mp semantic)
                      used committed member issuer self
                      (fun identifier member => ⟨revocationWitness (.capability identifier), ancestors identifier member⟩)
                      (fun channel member => ⟨revocationWitness (.channel channel), channels channel member⟩)),
                      Exists.intro stored (And.intro found rfl)⟩
                  else .error .revoked
                else .error .revoked
              else .error .revoked
            else .error .staleGrant
          else .error .noGrant
        else .error .noGrant
    else .error .noGrant

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
    commitmentWitness useWitness issuerWitness revocationWitness).toOption.map Subtype.val

/-- The same decision with the refusing branch named. `capabilityEvidence` is
its projection (`capabilityEvidenceRefusal_toOption`), not a second decider. -/
def capabilityEvidenceRefusal {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness) :
    Except RefusalReason
      (Evidence (config (F := F) profile snapshot store base step).portal snapshot.authState request) :=
  (capabilityEvidenceChecked profile snapshot store base step request identifier
    commitmentWitness useWitness issuerWitness revocationWitness).map Subtype.val

theorem capabilityEvidenceRefusal_toOption {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness) :
    (capabilityEvidenceRefusal profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness).toOption =
    capabilityEvidence profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness := by
  unfold capabilityEvidenceRefusal capabilityEvidence
  cases capabilityEvidenceChecked profile snapshot store base step request identifier
    commitmentWitness useWitness issuerWitness revocationWitness <;> rfl

private theorem capabilityEvidenceChecked_absent {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness)
    (absent : readCapability snapshot.cell kind identifier = none) :
    capabilityEvidenceChecked profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness = .error .noGrant := by
  unfold capabilityEvidenceChecked
  split
  · rfl
  · rename_i stored found
    rw [absent] at found
    cases found

private theorem capabilityEvidenceChecked_semantic {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness)
    (stored : StoredCapability kind) (reason : RefusalReason)
    (present : readCapability snapshot.cell kind identifier = some stored)
    (used : (config (F := F) profile snapshot store base step).portal.verifyCapabilityUse request
      stored.head (storedCapabilityDigest snapshot stored) useWitness = true)
    (refused : RefusalReason.capabilityRefusal stored.head snapshot.authState request = some reason) :
    capabilityEvidenceChecked profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness = .error reason := by
  unfold capabilityEvidenceChecked
  split
  · rename_i found
    rw [present] at found
    cases found
  · rename_i stored' found
    rw [present] at found
    cases found
    dsimp only
    rw [dif_pos used]
    split
    · rename_i named decided
      rw [refused] at decided
      cases decided
      rfl
    · rename_i decided
      rw [refused] at decided
      cases decided

/-- An absent capability is refused as `noGrant`. -/
theorem capabilityEvidenceRefusal_absent {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness)
    (absent : readCapability snapshot.cell kind identifier = none) :
    capabilityEvidenceRefusal profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness = .error .noGrant := by
  rw [capabilityEvidenceRefusal, capabilityEvidenceChecked_absent profile snapshot store base step
    request identifier commitmentWitness useWitness issuerWitness revocationWitness absent]
  rfl

/-- A present capability whose semantic component fails is refused under that
component's reason, after native use and before any portal opening. -/
theorem capabilityEvidenceRefusal_semantic {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (commitmentWitness : base.CapabilityCommitmentWitness)
    (useWitness : base.CapabilityUseWitness) (issuerWitness : base.IssuerWitness)
    (revocationWitness : RevocationKey → base.NonRevocationWitness)
    (stored : StoredCapability kind) (reason : RefusalReason)
    (present : readCapability snapshot.cell kind identifier = some stored)
    (used : (config (F := F) profile snapshot store base step).portal.verifyCapabilityUse request
      stored.head (storedCapabilityDigest snapshot stored) useWitness = true)
    (refused : RefusalReason.capabilityRefusal stored.head snapshot.authState request = some reason) :
    capabilityEvidenceRefusal profile snapshot store base step request identifier
      commitmentWitness useWitness issuerWitness revocationWitness = .error reason := by
  rw [capabilityEvidenceRefusal, capabilityEvidenceChecked_semantic profile snapshot store base step
    request identifier commitmentWitness useWitness issuerWitness revocationWitness stored reason
    present used refused]
  rfl

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

/-- `sourceCapabilityOnlyEvidence` with the refusing branch named. -/
def sourceCapabilityOnlyEvidenceChecked {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Except RefusalReason (Evidence (config (F := F) profile snapshot store
      (sourceCapabilityPortal snapshot expectedNullifier) step).portal snapshot.authState request) :=
  capabilityEvidenceRefusal profile snapshot store (sourceCapabilityPortal snapshot expectedNullifier) step
    request identifier () receipt () (fun _ => ())

theorem sourceCapabilityOnlyEvidenceChecked_toOption {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (store : PayloadStore) (expectedNullifier : Nat) (step : PolicyStepContext)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    (sourceCapabilityOnlyEvidenceChecked profile snapshot store expectedNullifier step
      request identifier receipt).toOption =
    sourceCapabilityOnlyEvidence profile snapshot store expectedNullifier step request identifier receipt :=
  capabilityEvidenceRefusal_toOption profile snapshot store
    (sourceCapabilityPortal snapshot expectedNullifier) step request identifier () receipt () (fun _ => ())

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

open Minidregg.Theory.Store (Address)

abbrev layout := CredentialAuthorityState.layout

def committedPolicy : CommittedPolicy where
  address := policyRecordDigest demoRecord
  record := demoRecord

def policyAt : Address layout := ⟨.policyAddress, (demoRequest.policyId, demoRequest.policyRevision)⟩

/-- One authority store holding exactly the demo policy group: generation,
current revision, and that revision's content address. -/
def policyStore : Store.Store layout :=
  (((0 : Store.Store layout).set ⟨.policyEpoch, demoRequest.policyId⟩
      (some demoRequest.policyEpoch)).set ⟨.policyRevision, demoRequest.policyId⟩
      (some demoRequest.policyRevision)).set policyAt (some committedPolicy.address)

/-- The registry consumes the actual authority-cell materializer; there is
no focused encoding or second synthetic cell for its projection. -/
def authorityMaterializer := CredentialAuthorityCell.materializer

/-- The authority wire's byte-level root (the salted store root). -/
abbrev authorityRootBytes : List UInt8 → Digest := StoreCodec.rootBytes CredentialAuthorityCell.wire

def authorityCell : RegistryCell authorityMaterializer :=
  CellState.materialize authorityMaterializer policyStore


theorem policyStore_epoch :
    policyStore ⟨.policyEpoch, demoRequest.policyId⟩ = some demoRequest.policyEpoch := by
  unfold policyStore
  rw [Store.Store.set_ne _ _ _ _ (by simp [policyAt]),
    Store.Store.set_ne _ _ _ _ (by simp), Store.Store.set_eq]; rfl

theorem policyStore_revision :
    policyStore ⟨.policyRevision, demoRequest.policyId⟩ = some demoRequest.policyRevision := by
  unfold policyStore
  rw [Store.Store.set_ne _ _ _ _ (by simp [policyAt]), Store.Store.set_eq]; rfl

theorem policyStore_address : policyStore policyAt = some committedPolicy.address := by
  unfold policyStore
  rw [Store.Store.set_eq]; rfl

/-- The cell holds the committed policy as its current head. -/
theorem policyStore_head :
    CredentialAuthorityDomain.headAt policyStore demoRequest.policyId =
      some ⟨demoRequest.policyRevision, committedPolicy.address⟩ :=
  CredentialAuthorityDomain.headAt_of_fields _ _ (by rw [policyStore_epoch]; rfl) _ _
    policyStore_revision policyStore_address

@[simp] theorem authorityCell_revision_exact :
    (CredentialAuthorityState.authState authorityCell).policyRevision
        demoRequest.policyId = demoRequest.policyRevision := by
  change (show Option PolicyRevision from policyStore ⟨.policyRevision, demoRequest.policyId⟩).getD 0 =
    demoRequest.policyRevision
  rw [policyStore_revision]
  rfl

@[simp] theorem authorityCell_address_exact :
    addressAt authorityCell demoRequest.policyId demoRequest.policyRevision =
      committedPolicy.address := by
  change (show Option Digest from policyStore policyAt).getD ⟨0⟩ = committedPolicy.address
  rw [policyStore_address]
  rfl

/-! ## Cell membership, registry, and compiler admission -/

/-- The cell holds this policy as its current head. -/
def Contains : Prop :=
  CredentialAuthorityDomain.headAt authorityCell.logical demoRequest.policyId =
    some ⟨demoRequest.policyRevision, committedPolicy.address⟩

instance : Decidable Contains := by unfold Contains; infer_instance

theorem contains : Contains := policyStore_head

/-- The inherited portal owns every non-membership verifier.  Membership is
replaced by an exact decidable reading of this cell and root.  Therefore no
signature acceptance or signature-soundness theorem is synthesized here. -/
def cellPortal (base : Portal) : Portal where
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
    decide (root = authorityCell.root /\ address = committedPolicy.address /\ Contains)
  verifyIssuer := base.verifyIssuer
  verifyNonRevocation := base.verifyNonRevocation
  verifyCommittedPolicy := base.verifyCommittedPolicy

def policyRegistry : PolicyRegistry where
  resolve := fun policyId epoch =>
    if policyId = demoRequest.policyId /\ epoch = demoRequest.policyRevision then
      some committedPolicy
    else none

def config (base : Portal) : CanonicalPolicyConfig (ZMod 13) where
  base := cellPortal base
  registry := policyRegistry
  recordDigest := policyRecordDigest
  stepBinding := .model demoStateDigest demoStepDigest
  compilerProfile := .researchDisabled demoRequest.semantics

@[simp] theorem config_verifyMembership (base : Portal)
    (root address : Digest) :
    (config base).portal.verifyMembership root address () =
      decide (root = authorityCell.root /\ address = committedPolicy.address /\ Contains) :=
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

def cellMember (root address : Digest) : Prop :=
  root = authorityCell.root /\ address = committedPolicy.address /\ Contains

noncomputable def membershipSemantics (base : Portal) :
    MembershipSemantics (config base).portal where
  Member := cellMember
  verifier_sound := by
    intro root address witness accepted
    have claim : root = authorityCell.root /\
        address = committedPolicy.address /\ Contains := by
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

theorem cell_membership_verified (base : Portal) :
    (config base).portal.verifyMembership authorityCell.root
      committedPolicy.address () = true := by
  rw [config_verifyMembership]
  apply decide_eq_true
  exact ⟨rfl, rfl, contains⟩

/-- Positive committed authorization.  The non-policy proof witness and its
acceptance are explicit inputs from `base`; this construction proves only the
policy/cell join and makes no signature claim. -/
noncomputable def positiveAuthorized
    (base : Portal) (proofWitness : base.ProofWitness)
    (proofAccepted : base.verifyProof demoRequest proofWitness = true) :
    CanonicalAuthorized (config base)
      (CredentialAuthorityState.authState authorityCell)
      demoRequest where
  evidence := .proof proofWitness (by
    simpa [config, CanonicalPolicyConfig.portal, cellPortal] using proofAccepted)
  policyWitness := policyWitness
  policyMembershipWitness := ()
  policyEpochExact := by
    change demoRequest.policyEpoch =
      (show Option Epoch from policyStore ⟨.policyEpoch, demoRequest.policyId⟩).getD 0
    rw [policyStore_epoch]
    rfl
  policyRevisionExact := by
    exact authorityCell_revision_exact.symm
  policyAddressExact := by
    change committedPolicy.address =
      addressAt authorityCell demoRequest.policyId demoRequest.policyRevision
    exact authorityCell_address_exact.symm
  policyMembershipVerified := by
    change (config base).portal.verifyMembership authorityCell.root
      (addressAt authorityCell demoRequest.policyId demoRequest.policyRevision)
      () = true
    rw [authorityCell_address_exact]
    exact cell_membership_verified base
  policyVerified := by
    rw [portal_verifyCommittedPolicy]
    rw [Bool.and_eq_true]
    refine ⟨?_, policy_verifies base⟩
    apply decide_eq_true
    change addressAt authorityCell demoRequest.policyId demoRequest.policyRevision =
      committedPolicy.address
    exact authorityCell_address_exact

/-- The concrete cell produces the kernel's full proof-relevant selection:
canonical bytes, cSHAKE address, fetched source, exact cell membership, and the
accepted source predicate all refer to the same `committedPolicy`. -/
noncomputable def selectedPayload
    (base : Portal) (proofWitness : base.ProofWitness)
    (proofAccepted : base.verifyProof demoRequest proofWitness = true) :
    SelectionPayload (config base) (contentAddressing base) payloadStore
      (membershipSemantics base) authorityCell demoRequest
      (positiveAuthorized base proofWitness proofAccepted) :=
  SelectionPayload.ofAuthorized (availability := payloadAvailability base)
    (positiveAuthorized base proofWitness proofAccepted)
    committedPolicy (registry_resolves base)

/-! ## The concrete cell root is the durable read guard -/

def registryCellId : CellId := ⟨91010⟩
def dataCellId : CellId := ⟨91011⟩

def dataPreBytes : List UInt8 := [1, 2, 3]
def dataPostBytes : List UInt8 := [1, 2, 3, 4]

def dataWrite : DataWrite where
  cellId := dataCellId
  expectedPre := authorityRootBytes dataPreBytes
  exactPost := authorityRootBytes dataPostBytes
  canonicalPostBytes := dataPostBytes

def event : StableEvent where
  codecVersion := 1
  domain := ⟨91020⟩
  eventId := ⟨91021⟩
  canonicalBytes := [80, 79, 76, 73, 67, 89]

def baseIntent : DataIntent authorityRootBytes where
  transactionId := ⟨91030⟩
  writes := [dataWrite]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := event
  subject := none
  postRootsBound := by
    intro write member
    simp only [List.mem_singleton] at member
    subst write
    rfl
  guardsReadOnly := by simp

theorem registryCell_readOnly :
    registryCellId ∉ baseIntent.writes.map DataWrite.cellId := by
  decide

def sharedDigest : SharedDigest authorityMaterializer authorityRootBytes :=
  ⟨rfl⟩

noncomputable def guardedIntent : DataIntent authorityRootBytes :=
  guardPolicyRegistry authorityCell registryCellId sharedDigest baseIntent
    registryCell_readOnly

noncomputable def snapshotBytes (cellId : CellId) : List UInt8 :=
  if cellId = dataCellId then dataPreBytes
  else if cellId = registryCellId then authorityCell.bytes
  else []

noncomputable def readySnapshot : DataSnapshot authorityRootBytes where
  model :=
    { roots := fun cellId => authorityRootBytes (snapshotBytes cellId)
      consumed := fun _ => false
      available := 0
      history := []
      journal := [] }
  canonicalBytes := snapshotBytes
  coherent := by intro cellId; rfl

@[simp] theorem readySnapshot_registry_root :
    readySnapshot.model.roots registryCellId = authorityCell.root := by
  change authorityRootBytes (snapshotBytes registryCellId) = authorityCell.root
  have bytesExact : snapshotBytes registryCellId = authorityCell.bytes := by
    simp [snapshotBytes, registryCellId, dataCellId]
  rw [bytesExact]
  rfl

theorem baseIntent_ready : baseIntent.preflight readySnapshot = .ok () := by
  have rootsReady :
      baseIntent.erase.rootsMatchCheck readySnapshot.model = true := by
    apply (Minidregg.Kernel.DurableCommitProtocol.Intent.rootsMatchCheck_eq_true_iff
      readySnapshot.model baseIntent.erase).mpr
    intro write member
    simp only [baseIntent, DataIntent.erase, List.map_singleton,
      List.mem_singleton] at member
    subst write
    change authorityRootBytes (snapshotBytes dataCellId) = authorityRootBytes dataPreBytes
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
  rw [if_neg (by simp [baseIntent])]
  rw [durableReady]

theorem guardedIntent_ready : guardedIntent.preflight readySnapshot = .ok () :=
  guardPolicyRegistry_preflight_ready authorityCell registryCellId sharedDigest
    baseIntent registryCell_readOnly readySnapshot readySnapshot_registry_root
    baseIntent_ready

/-! ## Pair-bound policy rotation rejects the old authorization intent -/

/-- The same cell after the policy's revision advances to a new address. -/
def rotatedStore : Store.Store layout :=
  (((0 : Store.Store layout).set ⟨.policyEpoch, demoRequest.policyId⟩
      (some demoRequest.policyEpoch)).set ⟨.policyRevision, demoRequest.policyId⟩
      (some (demoRequest.policyRevision + 1))).set
    ⟨.policyAddress, (demoRequest.policyId, demoRequest.policyRevision + 1)⟩ (some ⟨91040⟩)

def rotatedCell : RegistryCell authorityMaterializer :=
  CellState.materialize authorityMaterializer rotatedStore

/-- The root-collision premise for this one pair of authority stores. -/
def RootPairBinding (left right : Store.Store layout) : Prop :=
  authorityMaterializer.rootOf left = authorityMaterializer.rootOf right → left = right

theorem selected_rotated_states_ne : policyStore ≠ rotatedStore := by
  intro equal
  have revisions := congrArg (fun store : Store.Store layout =>
    store ⟨.policyRevision, demoRequest.policyId⟩) equal
  simp only at revisions
  rw [policyStore_revision] at revisions
  unfold rotatedStore at revisions
  rw [Store.Store.set_ne _ _ _ _ (by simp), Store.Store.set_eq] at revisions
  exact Nat.succ_ne_self demoRequest.policyRevision (Option.some.inj revisions).symm

theorem rotated_root_ne (binding : RootPairBinding policyStore rotatedStore) :
    rotatedCell.root ≠ authorityCell.root := by
  intro rootsEqual
  exact selected_rotated_states_ne (binding rootsEqual.symm)

noncomputable def rotatedSnapshotBytes (cellId : CellId) : List UInt8 :=
  if cellId = registryCellId then rotatedCell.bytes
  else snapshotBytes cellId

noncomputable def rotatedSnapshot : DataSnapshot authorityRootBytes where
  model :=
    { roots := fun cellId => authorityRootBytes (rotatedSnapshotBytes cellId)
      consumed := fun _ => false
      available := 0
      history := []
      journal := [] }
  canonicalBytes := rotatedSnapshotBytes
  coherent := by intro cellId; rfl

theorem rotatedSnapshot_moved (binding : RootPairBinding policyStore rotatedStore) :
    rotatedSnapshot.model.roots registryCellId ≠ authorityCell.root := by
  have bytesExact : rotatedSnapshotBytes registryCellId = rotatedCell.bytes := by
    simp [rotatedSnapshotBytes]
  change authorityRootBytes (rotatedSnapshotBytes registryCellId) ≠ authorityCell.root
  rw [bytesExact]
  exact rotated_root_ne binding

/-- Stale policy-update tooth.  A policy revision/address rotation changes the
pair-bound authority-cell root, so the old content+authorization intent is
rejected at the read guard before its data write can be installed. -/
theorem rotated_policy_rejects_old_intent (binding : RootPairBinding policyStore rotatedStore) :
    guardedIntent.preflight rotatedSnapshot = .error .staleReadGuard :=
  policy_registry_rotation_rejects_old_intent authorityCell registryCellId
    sharedDigest baseIntent registryCell_readOnly rotatedSnapshot
      (rotatedSnapshot_moved binding)

/-! ## Explicit physical ceiling -/

/-- A physical deployment does not inherit atomicity from the model by name;
it must provide exactly this simulation premise. -/
abbrev PhysicalAtomicityPremise
    (PhysicalState : Type) (PhysicalStep : PhysicalState ->
      DataIntent authorityRootBytes -> PhysicalState -> Type)
    (Represents : PhysicalState -> DataSnapshot authorityRootBytes -> Prop) :=
  ImplementationRefinement authorityRootBytes PhysicalState PhysicalStep Represents

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
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.rotated_policy_rejects_old_intent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.Example.rotated_policy_rejects_old_intent
