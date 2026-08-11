/-
# Assurance.DeployedCredentialLifecycle -- one deployed credential story

This module joins the concrete deployed authority registry, the bounded
credential-authority page, the canonical authority effect families, token
transport, and guarded durable data installation in one closed witness.

The logical story is complete: a root capability is issued, strictly
attenuated, used as a token, revoked, and made stale by a policy-epoch
rotation.  The public bounded page independently pins the exact policy
addresses for epochs two and three.  The durable use intent carries its
payload and observes the exact canonical authority-cell root read-only.

Three deployment ceilings remain deliberately visible.  The full sparse
authority cell still uses the countability-selected codec and byte-length root;
the real bounded page is not yet its production shard layout.  The portal
below is an inhabitation verifier, not a signature or membership security
claim.  Durable execution is a model until a physical handler inhabits the
existing `ImplementationRefinement` simulation boundary.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Compiler.DeployedCellRegistry
import Kernel.CanonicalPolicyRegistry
import Theory.CredentialAuthorityEffects

namespace Minidregg.Assurance.DeployedCredentialLifecycle

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityPageMaterializer
open Minidregg.Kernel
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Exact deployed carriers and public policy pins -/

noncomputable abbrev AuthorityMaterializer : Materializer :=
  Compiler.DeployedCellRegistry.materializer
    Compiler.DeployedCellRegistry.Kind.credentialAuthority

/-- The next policy address may be staged before it becomes current.  Epoch
two still selects exactly the address published by `prePage`; epoch three is
unreachable until the canonical epoch field rotates. -/
def initialLogical : LogicalState CredentialAuthorityState.schema.{0, 0} where
  fields := prePage.toCanonicalState.fields.write
    (.policyAddress examplePolicy 3) ⟨3300⟩
  resources := fun resource => nomatch resource

noncomputable def initialCell : Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer initialLogical

@[simp] theorem initialCell_logical : initialCell.logical = initialLogical := rfl

@[simp] theorem initial_policy_epoch :
    policyEpochAt initialCell examplePolicy = 2 := by
  simp [initialCell_logical, initialLogical, policyEpochAt, prePage,
    Page.toCanonicalState, Page.entries, oldPolicy, Entry.install]

@[simp] theorem initial_policy_address :
    policyAddressAt initialCell examplePolicy 2 = ⟨2200⟩ := by
  simp [initialCell_logical, initialLogical, policyAddressAt, prePage,
    Page.toCanonicalState, Page.entries, oldPolicy, Entry.install]
  rfl

@[simp] theorem staged_policy_address :
    policyAddressAt initialCell examplePolicy 3 = ⟨3300⟩ := by
  simp [initialCell_logical, initialLogical, policyAddressAt]

/-- The bounded production page and the full semantic cell agree on the
currently selected `(policy,epoch,address)` tuple. -/
theorem bounded_page_agrees_with_initial_selection :
    prePage.policyEpochAt examplePolicy =
        policyEpochAt initialCell examplePolicy /\
      prePage.policyAddressAt examplePolicy 2 =
        policyAddressAt initialCell examplePolicy 2 := by
  constructor <;>
    simp [Page.policyEpochAt, Page.policyAddressAt, Page.toCanonicalState,
      Page.entries, prePage, oldPolicy, Entry.install, initialCell_logical,
      initialLogical]
  all_goals rfl

/-! ## A verifier boundary suitable only for inhabitation -/

/-- Policy witnesses name their exact content address.  Every Boolean verifier
accepts because this module studies the semantic lifecycle, not cryptographic
soundness of a fabricated verifier. -/
def lifecyclePortal : Portal where
  SignatureWitness := Unit
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Digest
  policyAddress := id
  verifySignature := fun _ _ => true
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyMembership := fun _ _ _ => true
  verifyIssuer := fun _ _ _ _ => true
  verifyNonRevocation := fun _ _ _ => true
  verifyCommittedPolicy := fun _ _ _ _ => true

/-- A deployment may interpret the Boolean signature face only after proving a
relation-specific refinement like this.  No instance is provided here. -/
structure SignatureRefinement
    (Authenticates : {kind : ResourceKind} -> Request kind -> Unit -> Prop) : Prop where
  sound : forall {kind} (request : Request kind) witness,
    lifecyclePortal.verifySignature request witness = true ->
      Authenticates request witness

def authorityDomain : ProjectionUniverse where
  revocationKeys :=
    { .capability ⟨100⟩, .capability ⟨101⟩, .channel ⟨9⟩ }

noncomputable def adminRequest (pre : Cell AuthorityMaterializer) (effects : Digest)
    (nonce : Nat) : Request .object where
  domain := prePage.authorityDomain
  semantics := ⟨9001⟩
  federation := ⟨1⟩
  subject := ⟨41⟩
  subjectKeyEpoch := 0
  target := ⟨700⟩
  verb := .mutateObject
  argsDigest := ⟨9002⟩
  effectsDigest := effects
  nonce := nonce
  height := 20
  preStateRoot := pre.root
  policyId := examplePolicy
  policyEpoch := policyEpochAt pre examplePolicy
  cost := 1

/-- Every administrative effect still crosses the common policy-address,
membership, epoch, and policy gates.  Proof mode avoids pretending the
signature face above is sound. -/
noncomputable def adminAuthorization (pre : Cell AuthorityMaterializer) (effects : Digest)
    (nonce : Nat) :
    Authorized lifecyclePortal (authState authorityDomain pre)
      (adminRequest pre effects nonce) where
  evidence := .proof () rfl
  policyWitness := policyAddressAt pre examplePolicy
    (policyEpochAt pre examplePolicy)
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

/-! ## Issue and strict attenuation -/

def rootScope : Scope .object where
  targets := {⟨700⟩, ⟨701⟩}
  verbs := {.observeObject, .mutateObject}
  maxCost := 10

def childScope : Scope .object where
  targets := {⟨700⟩}
  verbs := {.mutateObject}
  maxCost := 4

def rootCapability : Capability .object where
  id := ⟨100⟩
  root := ⟨100⟩
  parent := none
  issuer := ⟨7⟩
  holder := .subject ⟨41⟩
  scope := rootScope
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := examplePolicy
  policyEpoch := 2
  ancestors := ∅
  channels := {⟨9⟩}

def childCapability : Capability .object where
  id := ⟨101⟩
  root := rootCapability.root
  parent := some rootCapability.id
  issuer := rootCapability.issuer
  holder := .subject ⟨41⟩
  scope := childScope
  notBefore := 10
  notAfter := 80
  issuerEpoch := rootCapability.issuerEpoch
  policyId := rootCapability.policyId
  policyEpoch := rootCapability.policyEpoch
  ancestors := {rootCapability.id}
  channels := rootCapability.channels

theorem strict_edge : childCapability.StrictAttenuates rootCapability := by
  refine
    { payload :=
        { parentId := rfl
          root := rfl
          issuer := rfl
          scopeNarrows := ?_
          notBefore := by decide
          notAfter := by decide
          issuerEpoch := rfl
          policyId := rfl
          policyEpoch := rfl
          ancestors := by simp [childCapability, rootCapability]
          channels := by simp [childCapability] }
      holder := ?_ }
  · exact
      { targets := by
          intro target member
          change target ∈ childScope.targets at member
          have exact : target = ⟨700⟩ := by simpa [childScope] using member
          subst target
          change ⟨700⟩ ∈ rootScope.targets
          simp [rootScope]
        verbs := by
          intro verb member
          change verb ∈ childScope.verbs at member
          have exact : verb = Verb.mutateObject := by
            simpa [childScope] using member
          subst verb
          change Verb.mutateObject ∈ rootScope.verbs
          simp [rootScope]
        maxCost := by decide }
  · intro subject covered
    simpa [childCapability, rootCapability, Holder.Covers] using covered

noncomputable def issueDeclaration : IssueDeclaration .object where
  capability := rootCapability
  expectedPreRoot := initialCell.root
  operationNullifier := 1001

def issueDigest (_ : IssueDeclaration .object) : Digest := ⟨9101⟩

deriving instance Countable for IssueDeclaration
deriving instance Countable for AttenuateDeclaration
deriving instance Countable for RevokeDeclaration
deriving instance Countable for EpochTarget
deriving instance Countable for RotateEpochDeclaration

noncomputable def issueCodec : LawfulCodec (IssueDeclaration .object) := by
  letI : Nonempty (IssueDeclaration .object) := ⟨issueDeclaration⟩
  exact codecOfCountable _

def issueEvidence : IssueEvidence authorityDomain initialCell issueDeclaration where
  preRootExact := rfl
  slotFresh := by
    simp [readCapability, initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      issueDeclaration, rootCapability]
    rfl
  nullifierFresh := by
    simp [isNullified, initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      issueDeclaration]
    rfl
  rootParent := rfl
  rootSelf := rfl
  rootAncestors := rfl
  issuerCurrent := by
    simp [issuerEpochAt, initialCell_logical, initialLogical, rootCapability,
      issueDeclaration, prePage, Page.toCanonicalState, Page.entries,
      oldPolicy, Entry.install]
    rfl
  policyCurrent := by simp [issueDeclaration, rootCapability]
  selfRegistered := by decide
  channelsRegistered := by
    simp [issueDeclaration, rootCapability, authorityDomain]
  selfLive := by
    simp [isRevoked, initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      issueDeclaration, rootCapability]
    rfl
  channelsLive := by
    simp [isRevoked, initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      issueDeclaration, rootCapability]
    rfl

noncomputable def issued :=
  acceptIssue authorityDomain initialCell issueCodec issueDigest issueDeclaration
    (adminAuthorization initialCell (issueDigest issueDeclaration) 1001)
    rfl rfl issueEvidence

noncomputable abbrev issuedCell : Cell AuthorityMaterializer :=
  issued.prepared.post

@[simp] theorem issued_root_exact :
    readCapability issuedCell .object rootCapability.id =
      some ⟨rootCapability, []⟩ :=
  issue_post_capability_exact issued

@[simp] theorem issue_nullifier_consumed :
    isNullified issuedCell issueDeclaration.operationNullifier = true :=
  issue_post_nullifier_exact issued

def parentStored : StoredCapability .object := ⟨rootCapability, []⟩

noncomputable def attenuateDeclaration : AttenuateDeclaration .object where
  child := childCapability
  parentId := rootCapability.id
  expectedPreRoot := issuedCell.root
  operationNullifier := 1002

def attenuateDigest (_ : AttenuateDeclaration .object) : Digest := ⟨9102⟩

noncomputable def attenuateCodec :
    LawfulCodec (AttenuateDeclaration .object) := by
  letI : Nonempty (AttenuateDeclaration .object) := ⟨attenuateDeclaration⟩
  exact codecOfCountable _

noncomputable def storedCapabilityCodec :
    LawfulCodec (StoredCapability .object) := by
  letI : Nonempty (StoredCapability .object) := ⟨parentStored⟩
  exact codecOfCountable _

theorem issued_frame (field : CredentialAuthorityState.schema.{0, 0}.Field)
    (outside : field ∉
      (show CellState.Patch CredentialAuthorityState.schema.{0, 0} Digest from
        issueDeclaration.patch).fieldFootprint) :
    issuedCell.logical.fields field = initialCell.logical.fields field :=
  issued.field_frame field outside

def attenuateEvidence :
    AttenuateEvidence authorityDomain issuedCell attenuateDeclaration parentStored where
  preRootExact := rfl
  parentExact := by simpa [parentStored] using issued_root_exact
  parentIdExact := rfl
  parentLineageValid := .root rootCapability rfl rfl rfl
  strict := strict_edge
  childSlotFresh := by
    change issuedCell.logical.fields
      (.capability .object childCapability.id) = none
    rw [issued_frame (.capability .object childCapability.id) (by
      change AuthorityField.capability .object ⟨101⟩ ∉
        (show Finset AuthorityField from
          {AuthorityField.capability .object ⟨100⟩,
            AuthorityField.nullifier 1001})
      decide)]
    simp [initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      childCapability]
    rfl
  nullifierFresh := by
    change (issuedCell.logical.fields
      (.nullifier attenuateDeclaration.operationNullifier)).getD false = false
    rw [issued_frame (.nullifier attenuateDeclaration.operationNullifier)
      (by
        change AuthorityField.nullifier 1002 ∉
          (show Finset AuthorityField from
            {AuthorityField.capability .object ⟨100⟩,
              AuthorityField.nullifier 1001})
        decide)]
    simp [initialCell_logical, initialLogical, prePage,
      Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
      attenuateDeclaration]
    rfl
  issuerCurrent := by
    change childCapability.issuerEpoch = issuerEpochAt issuedCell childCapability.issuer
    rw [show issuerEpochAt issuedCell childCapability.issuer =
        issuerEpochAt initialCell childCapability.issuer by
      unfold issuerEpochAt
      rw [issued_frame (.issuerEpoch childCapability.issuer) (by
        change AuthorityField.issuerEpoch ⟨7⟩ ∉
          (show Finset AuthorityField from
            {AuthorityField.capability .object ⟨100⟩,
              AuthorityField.nullifier 1001})
        decide)]]
    simp [childCapability, rootCapability, issuerEpochAt, initialCell_logical,
      initialLogical, prePage, Page.toCanonicalState, Page.entries, oldPolicy,
      Entry.install]
    rfl
  policyCurrent := by
    change childCapability.policyEpoch = policyEpochAt issuedCell childCapability.policyId
    rw [show policyEpochAt issuedCell childCapability.policyId =
        policyEpochAt initialCell childCapability.policyId by
      unfold policyEpochAt
      rw [issued_frame (.policyEpoch childCapability.policyId) (by
        change AuthorityField.policyEpoch examplePolicy ∉
          (show Finset AuthorityField from
            {AuthorityField.capability .object ⟨100⟩,
              AuthorityField.nullifier 1001})
        decide)]]
    simp [childCapability, rootCapability]
  selfRegistered := by decide
  ancestorsRegistered := by
    simp [attenuateDeclaration, childCapability, rootCapability, authorityDomain]
  channelsRegistered := by
    simp [attenuateDeclaration, childCapability, rootCapability, authorityDomain]
  selfLive := by
    unfold isRevoked
    change (issuedCell.logical.fields
      (.revoked (.capability childCapability.id))).getD false = false
    rw [issued_frame (.revoked (.capability childCapability.id)) (by
      change AuthorityField.revoked (.capability ⟨101⟩) ∉
        (show Finset AuthorityField from
          {AuthorityField.capability .object ⟨100⟩,
            AuthorityField.nullifier 1001})
      decide)]
    simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
      Page.entries, oldPolicy, Entry.install]
    rfl
  ancestorsLive := by
    intro ancestor member
    have exact : ancestor = rootCapability.id := by
      simpa [attenuateDeclaration, childCapability] using member
    subst ancestor
    unfold isRevoked
    rw [issued_frame (.revoked (.capability rootCapability.id)) (by
      change AuthorityField.revoked (.capability ⟨100⟩) ∉
        (show Finset AuthorityField from
          {AuthorityField.capability .object ⟨100⟩,
            AuthorityField.nullifier 1001})
      decide)]
    simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
      Page.entries, oldPolicy, Entry.install]
    rfl
  channelsLive := by
    intro channel member
    have exact : channel = ⟨9⟩ := by
      simpa [attenuateDeclaration, childCapability, rootCapability] using member
    subst channel
    unfold isRevoked
    rw [issued_frame (.revoked (.channel ⟨9⟩)) (by
      change AuthorityField.revoked (.channel ⟨9⟩) ∉
        (show Finset AuthorityField from
          {AuthorityField.capability .object ⟨100⟩,
            AuthorityField.nullifier 1001})
      decide)]
    simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
      Page.entries, oldPolicy, Entry.install]
    rfl

noncomputable def attenuated :=
  acceptAttenuation authorityDomain issuedCell attenuateCodec
    storedCapabilityCodec attenuateDigest attenuateDeclaration parentStored
    (adminAuthorization issuedCell (attenuateDigest attenuateDeclaration) 1002)
    rfl rfl attenuateEvidence

noncomputable abbrev attenuatedCell : Cell AuthorityMaterializer :=
  attenuated.prepared.post

@[simp] theorem attenuated_child_exact :
    readCapability attenuatedCell .object childCapability.id =
      some (descendedCapability childCapability parentStored) :=
  attenuation_post_capability_exact attenuated

theorem attenuated_child_lineage :
    LineageValid (descendedCapability childCapability parentStored) :=
  attenuateEvidence.childLineageValid

/-! ## Capability transport and one exact token use -/

theorem attenuated_frame
    (field : CredentialAuthorityState.schema.{0, 0}.Field)
    (outside : field ∉
      (show CellState.Patch CredentialAuthorityState.schema.{0, 0} Digest from
        attenuateDeclaration.patch parentStored).fieldFootprint) :
    attenuatedCell.logical.fields field = issuedCell.logical.fields field :=
  attenuated.field_frame field outside

@[simp] theorem attenuated_policy_epoch_two :
    policyEpochAt attenuatedCell examplePolicy = 2 := by
  unfold policyEpochAt
  rw [attenuated_frame (.policyEpoch examplePolicy) (by
    change AuthorityField.policyEpoch examplePolicy ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.policyEpoch examplePolicy) (by
    change AuthorityField.policyEpoch examplePolicy ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  exact initial_policy_epoch

@[simp] theorem attenuated_policy_address_two :
    policyAddressAt attenuatedCell examplePolicy 2 = ⟨2200⟩ := by
  unfold policyAddressAt
  rw [attenuated_frame (.policyAddress examplePolicy 2) (by
    change AuthorityField.policyAddress examplePolicy 2 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.policyAddress examplePolicy 2) (by
    change AuthorityField.policyAddress examplePolicy 2 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  exact initial_policy_address

@[simp] theorem attenuated_issuer_epoch_zero :
    issuerEpochAt attenuatedCell rootCapability.issuer = 0 := by
  unfold issuerEpochAt
  rw [attenuated_frame (.issuerEpoch rootCapability.issuer) (by
    change AuthorityField.issuerEpoch ⟨7⟩ ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.issuerEpoch rootCapability.issuer) (by
    change AuthorityField.issuerEpoch ⟨7⟩ ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  simp [initialCell_logical, initialLogical, issuerEpochAt, prePage,
    Page.toCanonicalState, Page.entries, oldPolicy, Entry.install,
    rootCapability]
  rfl

theorem attenuated_live (key : RevocationKey) :
    isRevoked attenuatedCell key = false := by
  unfold isRevoked
  rw [attenuated_frame (.revoked key) (by
    change AuthorityField.revoked key ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    simp)]
  rw [issued_frame (.revoked key) (by
    change AuthorityField.revoked key ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    simp)]
  simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
    Page.entries, oldPolicy, Entry.install]
  rfl

noncomputable def useRequest : Request .object :=
  adminRequest attenuatedCell ⟨9200⟩ 2001

theorem child_admissible_for_use :
    childCapability.Admissible (authState authorityDomain attenuatedCell)
      useRequest := by
  refine
    { holder := by simp [childCapability, useRequest, adminRequest, Holder.Covers]
      scope :=
        { target := by simp [childCapability, childScope, useRequest, adminRequest]
          verb := by simp [childCapability, childScope, useRequest, adminRequest]
          cost := by simp [childCapability, childScope, useRequest, adminRequest] }
      validFrom := by simp [childCapability, useRequest, adminRequest]
      validUntil := by simp [childCapability, useRequest, adminRequest]
      policyId := by simp [childCapability, rootCapability, useRequest, adminRequest]
      policyEpoch := by
        simpa [childCapability, rootCapability, useRequest, adminRequest] using
          attenuated_policy_epoch_two.symm
      policyCurrent := by
        simpa [childCapability, rootCapability,
          CredentialAuthorityState.authState] using
          attenuated_policy_epoch_two.symm
      issuerCurrent := by
        simpa [childCapability, rootCapability,
          CredentialAuthorityState.authState] using
          attenuated_issuer_epoch_zero.symm
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · intro member
    rcases (mem_authState_revoked_iff authorityDomain attenuatedCell
      (.capability childCapability.id)).mp member with ⟨_, revoked⟩
    rw [attenuated_live] at revoked
    contradiction
  · intro ancestor ancestorMember revokedMember
    rcases (mem_authState_revoked_iff authorityDomain attenuatedCell
      (.capability ancestor)).mp revokedMember with ⟨_, revoked⟩
    rw [attenuated_live] at revoked
    contradiction
  · intro channel channelMember revokedMember
    rcases (mem_authState_revoked_iff authorityDomain attenuatedCell
      (.channel channel)).mp revokedMember with ⟨_, revoked⟩
    rw [attenuated_live] at revoked
    contradiction

def tokenEvidence :
    Evidence lifecyclePortal (authState authorityDomain attenuatedCell)
      useRequest :=
  .capability childCapability ⟨9500⟩ () () () () child_admissible_for_use
    rfl rfl rfl rfl
    (by intro ancestor member; exact ⟨(), rfl⟩)
    (by intro channel member; exact ⟨(), rfl⟩)

def tokenAuthorization :
    Authorized lifecyclePortal (authState authorityDomain attenuatedCell)
      useRequest where
  evidence := tokenEvidence
  policyWitness := ⟨2200⟩
  policyMembershipWitness := ()
  policyEpochExact := by simp [useRequest, adminRequest]
  policyAddressExact := by
    change ⟨2200⟩ = policyAddressAt attenuatedCell examplePolicy 2
    exact attenuated_policy_address_two.symm
  policyMembershipVerified := rfl
  policyVerified := rfl

def requestDigestScheme : RequestDigestScheme where
  digestWire := fun wire => ⟨wire.nonce + wire.effectsDigest⟩

def childLineage : childCapability.Lineage :=
  .attenuate childCapability rootCapability (.root rootCapability rfl rfl rfl)
    strict_edge

/-- Token is only a carrier for the exact capability evidence; the same common
policy epoch/address/membership gate remains in `tokenAuthorization`. -/
noncomputable def acceptedToken :
    AcceptedCredential requestDigestScheme lifecyclePortal
      (authState authorityDomain attenuatedCell) useRequest where
  authorization := tokenAuthorization
  carrier := .token
  carrierSupported := by
    change CarrierKind.token = .capability ∨ CarrierKind.token = .token
    exact Or.inr rfl
  requestBinding := .canonical requestDigestScheme useRequest
  lineage := childLineage

theorem token_selects_exact_policy_address :
    lifecyclePortal.policyAddress acceptedToken.authorization.policyWitness =
      policyAddressAt attenuatedCell examplePolicy 2 := by
  exact acceptedToken.authorization.policyAddressExact

/-! ## Revocation and epoch rotation -/

noncomputable def revokeDeclaration : RevokeDeclaration where
  key := .channel ⟨9⟩
  expectedPreRoot := attenuatedCell.root
  operationNullifier := 1003

def revokeDigest (_ : RevokeDeclaration) : Digest := ⟨9301⟩

noncomputable def revokeCodec : LawfulCodec RevokeDeclaration := by
  letI : Nonempty RevokeDeclaration := ⟨revokeDeclaration⟩
  exact codecOfCountable _

theorem attenuated_nullifier_fresh :
    isNullified attenuatedCell revokeDeclaration.operationNullifier = false := by
  unfold isNullified
  rw [attenuated_frame (.nullifier revokeDeclaration.operationNullifier) (by
    change AuthorityField.nullifier 1003 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.nullifier revokeDeclaration.operationNullifier) (by
    change AuthorityField.nullifier 1003 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
    Page.entries, oldPolicy, Entry.install, revokeDeclaration]
  rfl

def revokeEvidence :
    RevokeEvidence authorityDomain attenuatedCell revokeDeclaration where
  preRootExact := rfl
  registered := by decide
  live := attenuated_live _
  nullifierFresh := attenuated_nullifier_fresh

noncomputable def revoked :=
  acceptRevocation authorityDomain attenuatedCell revokeCodec revokeDigest
    revokeDeclaration
    (adminAuthorization attenuatedCell (revokeDigest revokeDeclaration) 1003)
    rfl rfl revokeEvidence

noncomputable abbrev revokedCell : Cell AuthorityMaterializer :=
  revoked.prepared.post

@[simp] theorem revoked_channel_exact :
    isRevoked revokedCell (.channel ⟨9⟩) = true :=
  revocation_post_exact revoked

theorem revoked_channel_authorizer_member :
    .channel ⟨9⟩ ∈ (authState authorityDomain revokedCell).revoked :=
  revocation_post_is_authorizer_member revoked

theorem revoked_frame
    (field : CredentialAuthorityState.schema.{0, 0}.Field)
    (outside : field ∉
      (show CellState.Patch CredentialAuthorityState.schema.{0, 0} Digest from
        revokeDeclaration.patch).fieldFootprint) :
    revokedCell.logical.fields field = attenuatedCell.logical.fields field :=
  revoked.field_frame field outside

noncomputable def rotateDeclaration : RotateEpochDeclaration where
  target := .policy examplePolicy
  expectedEpoch := 2
  nextEpoch := 3
  expectedPreRoot := revokedCell.root
  operationNullifier := 1004

def rotateDigest (_ : RotateEpochDeclaration) : Digest := ⟨9302⟩

noncomputable def rotateCodec : LawfulCodec RotateEpochDeclaration := by
  letI : Nonempty RotateEpochDeclaration := ⟨rotateDeclaration⟩
  exact codecOfCountable _

theorem revoked_policy_epoch_two :
    policyEpochAt revokedCell examplePolicy = 2 := by
  unfold policyEpochAt
  rw [revoked_frame (.policyEpoch examplePolicy) (by
    change AuthorityField.policyEpoch examplePolicy ∉
      (show Finset AuthorityField from
        {AuthorityField.revoked (.channel ⟨9⟩),
          AuthorityField.nullifier 1003})
    decide)]
  exact attenuated_policy_epoch_two

theorem revoked_rotation_nullifier_fresh :
    isNullified revokedCell rotateDeclaration.operationNullifier = false := by
  unfold isNullified
  rw [revoked_frame (.nullifier rotateDeclaration.operationNullifier) (by
    change AuthorityField.nullifier 1004 ∉
      (show Finset AuthorityField from
        {AuthorityField.revoked (.channel ⟨9⟩),
          AuthorityField.nullifier 1003})
    decide)]
  change isNullified attenuatedCell 1004 = false
  unfold isNullified
  rw [attenuated_frame (.nullifier 1004) (by
    change AuthorityField.nullifier 1004 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.nullifier 1004) (by
    change AuthorityField.nullifier 1004 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  simp [initialCell_logical, initialLogical, prePage, Page.toCanonicalState,
    Page.entries, oldPolicy, Entry.install]
  rfl

def rotateEvidence : RotateEpochEvidence revokedCell rotateDeclaration where
  preRootExact := rfl
  currentExact := revoked_policy_epoch_two
  successorExact := by decide
  nullifierFresh := revoked_rotation_nullifier_fresh

noncomputable def rotated :=
  acceptEpochRotation authorityDomain revokedCell rotateCodec rotateDigest
    rotateDeclaration
    (adminAuthorization revokedCell (rotateDigest rotateDeclaration) 1004)
    rfl rfl rotateEvidence

noncomputable abbrev finalCell : Cell AuthorityMaterializer :=
  rotated.prepared.post

@[simp] theorem final_policy_epoch_three :
    policyEpochAt finalCell examplePolicy = 3 := by
  simpa [rotateDeclaration, EpochTarget.read] using rotation_post_exact rotated

theorem rotated_frame
    (field : CredentialAuthorityState.schema.{0, 0}.Field)
    (outside : field ∉
      (show CellState.Patch CredentialAuthorityState.schema.{0, 0} Digest from
        rotateDeclaration.patch).fieldFootprint) :
    finalCell.logical.fields field = revokedCell.logical.fields field :=
  rotated.field_frame field outside

@[simp] theorem final_policy_address_three :
    policyAddressAt finalCell examplePolicy 3 = ⟨3300⟩ := by
  unfold policyAddressAt
  rw [rotated_frame (.policyAddress examplePolicy 3) (by
    change AuthorityField.policyAddress examplePolicy 3 ∉
      (show Finset AuthorityField from
        {AuthorityField.policyEpoch examplePolicy,
          AuthorityField.nullifier 1004})
    decide)]
  rw [revoked_frame (.policyAddress examplePolicy 3) (by
    change AuthorityField.policyAddress examplePolicy 3 ∉
      (show Finset AuthorityField from
        {AuthorityField.revoked (.channel ⟨9⟩),
          AuthorityField.nullifier 1003})
    decide)]
  rw [attenuated_frame (.policyAddress examplePolicy 3) (by
    change AuthorityField.policyAddress examplePolicy 3 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨101⟩,
          AuthorityField.nullifier 1002})
    decide)]
  rw [issued_frame (.policyAddress examplePolicy 3) (by
    change AuthorityField.policyAddress examplePolicy 3 ∉
      (show Finset AuthorityField from
        {AuthorityField.capability .object ⟨100⟩,
          AuthorityField.nullifier 1001})
    decide)]
  exact staged_policy_address

@[simp] theorem final_channel_revoked :
    isRevoked finalCell (.channel ⟨9⟩) = true := by
  unfold isRevoked
  rw [rotated_frame (.revoked (.channel ⟨9⟩)) (by
    change AuthorityField.revoked (.channel ⟨9⟩) ∉
      (show Finset AuthorityField from
        {AuthorityField.policyEpoch examplePolicy,
          AuthorityField.nullifier 1004})
    decide)]
  exact revoked_channel_exact

theorem final_channel_authorizer_member :
    .channel ⟨9⟩ ∈ (authState authorityDomain finalCell).revoked := by
  apply (mem_authState_revoked_iff authorityDomain finalCell _).2
  exact ⟨by decide, final_channel_revoked⟩

/-- The exact child token used above cannot be authorized after the same
canonical cell records the channel revocation. -/
theorem subsequent_child_authorization_rejected :
    ¬ childCapability.Admissible (authState authorityDomain finalCell)
      useRequest := by
  exact channel_revocation_rejected childCapability
    (authState authorityDomain finalCell) useRequest ⟨9⟩
    (by simp [childCapability, rootCapability]) final_channel_authorizer_member

/-- Epoch rotation supplies an independent rejection tooth: the old token's
policy epoch is no longer current. -/
theorem subsequent_child_policy_stale :
    childCapability.policyEpoch ≠
      (authState authorityDomain finalCell).policyEpoch childCapability.policyId := by
  intro current
  have impossible : (2 : Nat) = 3 := by
    exact current.trans final_policy_epoch_three
  contradiction

theorem wrong_scope_rejected :
    ¬ childCapability.Admissible (authState authorityDomain attenuatedCell)
      (useRequest.retarget ⟨701⟩) := by
  apply target_substitution_rejected childCapability
    (authState authorityDomain attenuatedCell) useRequest ⟨701⟩
  simp [childCapability, childScope]

/-! ## Replay and stale-root teeth at the semantic effect boundary -/

theorem issue_replay_rejected :
    IssueEvidence authorityDomain issuedCell issueDeclaration -> False := by
  intro replay
  have impossible : true = false :=
    issue_nullifier_consumed.symm.trans replay.nullifierFresh
  contradiction

noncomputable def staleIssueDeclaration : IssueDeclaration .object :=
  { issueDeclaration with
    expectedPreRoot := ⟨initialCell.root.value + 1⟩
    operationNullifier := 1999 }

theorem stale_root_rejected :
    IssueEvidence authorityDomain initialCell staleIssueDeclaration -> False := by
  intro stale
  have equal := stale.preRootExact
  have values := congrArg Digest.value equal
  simp [staleIssueDeclaration] at values

/-! The bounded page publishes the same final selection/revocation facts. -/

theorem bounded_page_agrees_with_final_selection :
    postPage.policyEpochAt examplePolicy = policyEpochAt finalCell examplePolicy /\
      postPage.policyAddressAt examplePolicy 3 =
        policyAddressAt finalCell examplePolicy 3 /\
      .channel ⟨9⟩ ∈ postPage.revoked := by
  exact ⟨post_policy_epoch_exact.trans final_policy_epoch_three.symm,
    post_policy_address_exact.trans final_policy_address_three.symm,
    post_revocation_member⟩

end Minidregg.Assurance.DeployedCredentialLifecycle
