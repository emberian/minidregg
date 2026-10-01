/-
# Assurance.DeployedCredentialLifecycle -- one deployed credential story

This module joins the deployed authority cell (`CredentialAuthorityCell`, the
one store cell of the authority domain), the canonical authority effect
families, token transport, and guarded durable data installation in one closed
witness.

The logical story is complete: a root capability is issued, strictly
attenuated, used as a token, revoked, and made stale by a policy-epoch
rotation.  Every step is the validated patch of its family at the exact post of
the previous one, starting from a built pre-cell.  The revoked channel ends
registered present AND revoked present, and neither presence can be erased.
The refusing poles are stated at the validator: erasing a registration or a
revocation is rejected with the exact failing operation, and replaying an
issuance is refused by its occupied capability slot.  Operation nullifiers are
not authority-cell state; their single use is the durable consumed set's
(`DurableDataIntent.DataIntent.consumed_nullifier_refused`).  The durable use intent carries its payload and observes the exact
authority-cell root read-only.

Two deployment ceilings remain deliberately visible.  The portal below is an
inhabitation verifier, not a signature or membership security claim.  Root
movement of the authority cell is conditional on the pair-scoped cSHAKE256
no-collision premise (`CellState.PairBindingPremise`), never on a
global injection into 256 bits.  Durable execution is a model until a physical
handler inhabits the existing `ImplementationRefinement` simulation boundary.
-/
import Compiler.CredentialAuthorityCell
import Compiler.DeployedCellRegistry
import Kernel.CanonicalPolicyRegistry
import Theory.CredentialAuthorityEffects

namespace Minidregg.Assurance.DeployedCredentialLifecycle

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.CanonicalPolicyRegistry
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The deployed authority cell and its built pre-cell -/

abbrev AuthorityMaterializer : Materializer :=
  Compiler.DeployedCellRegistry.materializer
    Compiler.DeployedCellRegistry.Kind.credentialAuthority

/-- The deployed authority kind's materializer is the one authority cell's. -/
theorem authorityMaterializer_deployed :
    AuthorityMaterializer = CredentialAuthorityCell.materializer := rfl

def examplePolicy : PolicyId := ⟨17⟩

/-- The authority domain this lifecycle's requests and durable records name. -/
def lifecycleDomain : Digest := ⟨8100⟩

/-- Policy generation two at current revision two, a staged revision-three
address, and the shared channel registered (present in the append-only
`registered` plane) and live (absent from `revoked`).  The root and child
capabilities are NOT registered here: issuance and attenuation register them.  A staged
revision does not become current until an explicit policy installation changes
the revision plane; grant-generation rotation does not select it. -/
def initialEntries : List (Minidregg.Theory.Store.Entry layout) :=
  [⟨⟨.policyEpoch, examplePolicy⟩, (2 : Epoch)⟩,
   ⟨⟨.policyRevision, examplePolicy⟩, (2 : PolicyRevision)⟩,
   ⟨⟨.policyAddress, (examplePolicy, 2)⟩, (⟨2200⟩ : Digest)⟩,
   ⟨⟨.policyAddress, (examplePolicy, 3)⟩, (⟨3300⟩ : Digest)⟩,
   ⟨⟨.registered, .channel ⟨9⟩⟩, ()⟩]

def initialLogical : Store layout := StoreCodec.fromEntries initialEntries

/-- The pre-cell: the deployed authority cell built from its store.  Its bytes
are the store codec's and decode back to it (`initial_roundtrip`). -/
def initialCell : Cell AuthorityMaterializer :=
  CellState.materialize AuthorityMaterializer initialLogical

@[simp] theorem initialCell_logical : initialCell.logical = initialLogical := rfl

theorem initial_roundtrip :
    AuthorityMaterializer.codec.decode initialCell.bytes = some initialCell.logical :=
  CredentialAuthorityCell.cell_decode initialCell

@[simp] theorem initial_policy_epoch :
    policyEpochAt initialCell examplePolicy = 2 := by decide

@[simp] theorem initial_policy_revision :
    policyRevisionAt initialCell examplePolicy = 2 := by decide

@[simp] theorem initial_policy_address :
    policyAddressAt initialCell examplePolicy 2 = ⟨2200⟩ := by decide

@[simp] theorem staged_policy_address :
    policyAddressAt initialCell examplePolicy 3 = ⟨3300⟩ := by decide

/-- The shared channel is registered and live in the pre-cell. -/
theorem initial_channel_registered_live :
    isRegistered initialCell (.channel ⟨9⟩) = true ∧
      isRevoked initialCell (.channel ⟨9⟩) = false := by
  decide

/-- Neither lifecycle capability is registered before it is created. -/
theorem initial_capabilities_unregistered :
    isRegistered initialCell (.capability ⟨100⟩) = false ∧
      isRegistered initialCell (.capability ⟨101⟩) = false := by
  decide

/-! ## A verifier boundary suitable only for inhabitation -/

/-- Policy witnesses name their exact content address.  Every Boolean verifier
accepts because this module studies the semantic lifecycle, not cryptographic
soundness of a fabricated verifier. -/
def lifecyclePortal : Portal where
  SignatureWitness := Unit
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  CapabilityUseWitness := Unit
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Digest
  policyAddress := id
  verifySignature := fun _ _ => true
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyCapabilityUse := fun _ _ _ _ => true
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

noncomputable def adminRequest (pre : Cell AuthorityMaterializer) (effects : Digest)
    (nonce : Nat) (args : Digest := ⟨9002⟩) : Request .object where
  domain := lifecycleDomain
  semantics := ⟨9001⟩
  federation := ⟨1⟩
  subject := ⟨41⟩
  subjectKeyEpoch := 0
  target := ⟨700⟩
  verb := .mutateObject
  argsDigest := args
  effectsDigest := effects
  nonce := nonce
  height := 20
  preStateRoot := pre.root
  policyId := examplePolicy
  policyEpoch := policyEpochAt pre examplePolicy
  policyRevision := policyRevisionAt pre examplePolicy
  cost := 1

/-- Non-cryptographic argument addressing for this inhabitation fixture only.
The family still hashes the complete lawful declaration encoding, and no
digest-reflection claim is made. -/
def adminArgsDigest (bytes : List UInt8) : Digest := ⟨bytes.length⟩

noncomputable def adminContext (pre : Cell AuthorityMaterializer) :
    CredentialAuthorityEffects.RequestContext where
  authority :=
    { kind := .object
      domain := lifecycleDomain
      semantics := ⟨9001⟩
      federation := ⟨1⟩
      subject := ⟨41⟩
      subjectKeyEpoch := 0
      target := ⟨700⟩
      verb := .mutateObject
      nonce := 0 -- each family replaces this with its operation nullifier
      height := 20
      policyId := examplePolicy
      policyEpoch := policyEpochAt pre examplePolicy
      policyRevision := policyRevisionAt pre examplePolicy
      cost := 1 }
  argsDigestBytes := adminArgsDigest

/-- Every administrative effect still crosses the common policy-address,
membership, epoch, and policy gates.  Proof mode avoids pretending the
signature face above is sound. -/
noncomputable def adminAuthorization (pre : Cell AuthorityMaterializer) (effects : Digest)
    (nonce : Nat) (args : Digest := ⟨9002⟩) :
    Authorized lifecyclePortal (authState pre)
      (adminRequest pre effects nonce args) where
  evidence := .proof () rfl
  policyWitness := policyAddressAt pre examplePolicy
    (policyRevisionAt pre examplePolicy)
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

/-! ## Issue and strict attenuation -/

def rootScope : Scope .object where
  targets := .explicit {⟨700⟩, ⟨701⟩}
  verbs := {.observeObject, .mutateObject}
  maxCost := 10

def childScope : Scope .object where
  targets := .explicit {⟨700⟩}
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

theorem strict_edge :
    childCapability.StrictAttenuates rootCapability CredentialAuthorityState.noParents := by
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
          change (TargetSet.explicit {⟨700⟩}).Narrows (TargetSet.explicit {⟨700⟩, ⟨701⟩}) _
          decide
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

def issueEvidence : IssueEvidence initialCell issueDeclaration where
  preRootExact := rfl
  slotFresh := by intro kind; cases kind <;> decide
  rootParent := rfl
  rootSelf := rfl
  rootAncestors := rfl
  issuerCurrent := by decide
  policyCurrent := by decide
  selfUnregistered := by decide
  channelsRegistered := by decide
  selfLive := by decide
  channelsLive := by decide

noncomputable def issued :=
  acceptIssue initialCell (adminContext initialCell) issueCodec issueDigest issueDeclaration
    (adminAuthorization initialCell (issueDigest issueDeclaration) 1001
      (adminArgsDigest (issueCodec.encode issueDeclaration)))
    rfl rfl rfl issueEvidence

noncomputable abbrev issuedCell : Cell AuthorityMaterializer :=
  issued.prepared.post

@[simp] theorem issued_root_exact :
    readCapability issuedCell .object rootCapability.id =
      some ⟨rootCapability, []⟩ :=
  issue_post_capability_exact issued

/-- Issuance registered the root capability's own key. -/
@[simp] theorem issued_root_registered :
    isRegistered issuedCell (.capability rootCapability.id) = true :=
  issue_post_registered issued

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

def attenuateEvidence :
    AttenuateEvidence issuedCell attenuateDeclaration parentStored where
  preRootExact := rfl
  parentExact := by simpa [parentStored] using issued_root_exact
  parentIdExact := rfl
  parentLineageValid := .root rootCapability rfl rfl rfl
  parentLineageAnchored := True.intro
  strict := strict_edge
  childSlotFresh := by intro kind; cases kind <;> decide
  issuerCurrent := by decide
  policyCurrent := by decide
  selfUnregistered := by decide
  ancestorsRegistered := by decide
  channelsRegistered := by decide
  selfLive := by decide
  ancestorsLive := by decide
  channelsLive := by decide

noncomputable def attenuated :=
  acceptAttenuation issuedCell (adminContext issuedCell) attenuateCodec
    storedCapabilityCodec attenuateDigest attenuateDeclaration parentStored
    (adminAuthorization issuedCell (attenuateDigest attenuateDeclaration) 1002
      (adminArgsDigest (attenuateCodec.encode attenuateDeclaration)))
    rfl rfl rfl attenuateEvidence

noncomputable abbrev attenuatedCell : Cell AuthorityMaterializer :=
  attenuated.prepared.post

@[simp] theorem attenuated_child_exact :
    readCapability attenuatedCell .object childCapability.id =
      some (descendedCapability childCapability parentStored) :=
  attenuation_post_capability_exact attenuated

/-- Attenuation registered the child capability's own key. -/
@[simp] theorem attenuated_child_registered :
    isRegistered attenuatedCell (.capability childCapability.id) = true :=
  attenuation_post_registered attenuated

theorem attenuated_child_lineage :
    LineageValid CredentialAuthorityState.noParents
      (descendedCapability childCapability parentStored) :=
  attenuateEvidence.childLineageValid

/-! ## Capability transport and one exact token use -/

@[simp] theorem attenuated_policy_epoch_two :
    policyEpochAt attenuatedCell examplePolicy = 2 := by decide

@[simp] theorem attenuated_policy_revision_two :
    policyRevisionAt attenuatedCell examplePolicy = 2 := by decide

@[simp] theorem attenuated_policy_address_two :
    policyAddressAt attenuatedCell examplePolicy 2 = ⟨2200⟩ := by decide

@[simp] theorem attenuated_issuer_epoch_zero :
    issuerEpochAt attenuatedCell rootCapability.issuer = 0 := by decide

/-- No key is revoked after issuance and attenuation: neither family patch
names the revoked plane (their exact footprints), and the pre-cell holds no
revocation. -/
theorem attenuated_live (key : RevocationKey) :
    isRevoked attenuatedCell key = false := by
  have attenuatedFrame : attenuatedCell.logical ⟨.revoked, key⟩ =
      issuedCell.logical ⟨.revoked, key⟩ :=
    attenuated.frame _ (by
      change _ ∉ Patch.writeFootprint
        (attenuateDeclaration.patch parentStored issuedCell.logical)
      rw [AttenuateDeclaration.patch_writeFootprint]
      simp)
  have issuedFrame : issuedCell.logical ⟨.revoked, key⟩ =
      initialCell.logical ⟨.revoked, key⟩ :=
    issued.frame _ (by
      change _ ∉ Patch.writeFootprint (issueDeclaration.patch initialCell.logical)
      rw [IssueDeclaration.patch_writeFootprint]
      simp)
  have initialAbsent : initialLogical ⟨.revoked, key⟩ = none :=
    (StoreCodec.fromEntries_apply_eq_none_iff _ _).2 (by simp [initialEntries])
  unfold isRevoked
  rw [attenuatedFrame, issuedFrame, initialCell_logical, initialAbsent]
  rfl

noncomputable def useRequest : Request .object :=
  adminRequest attenuatedCell ⟨9200⟩ 2001

theorem child_admissible_for_use :
    childCapability.Admissible (authState attenuatedCell)
      useRequest := by
  refine
    { holder := by simp [childCapability, useRequest, adminRequest, Holder.Covers]
      scope :=
        { target := by
            simp [TargetSet.Covers, childCapability, childScope, useRequest, adminRequest]
          verb := by simp [childCapability, childScope, useRequest, adminRequest]
          cost := by simp [childCapability, childScope, useRequest, adminRequest] }
      validFrom := by simp [childCapability, useRequest, adminRequest]
      validUntil := by simp [childCapability, useRequest, adminRequest]
      requestLaw := by
        refine ⟨by simp [childCapability, rootCapability, useRequest, adminRequest], ?_⟩
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
    have revoked := (mem_authState_revoked_iff attenuatedCell (.capability childCapability.id)).mp member
    rw [attenuated_live] at revoked
    contradiction
  · intro ancestor ancestorMember revokedMember
    have revoked := (mem_authState_revoked_iff attenuatedCell (.capability ancestor)).mp revokedMember
    rw [attenuated_live] at revoked
    contradiction
  · intro channel channelMember revokedMember
    have revoked := (mem_authState_revoked_iff attenuatedCell (.channel channel)).mp revokedMember
    rw [attenuated_live] at revoked
    contradiction

def tokenEvidence :
    Evidence lifecyclePortal (authState attenuatedCell)
      useRequest :=
  .capability childCapability ⟨9500⟩ () () () () () child_admissible_for_use
    rfl rfl rfl rfl rfl
    (by intro ancestor member; exact ⟨(), rfl⟩)
    (by intro channel member; exact ⟨(), rfl⟩)

def tokenAuthorization :
    Authorized lifecyclePortal (authState attenuatedCell)
      useRequest where
  evidence := tokenEvidence
  policyWitness := ⟨2200⟩
  policyMembershipWitness := ()
  policyEpochExact := by simp [useRequest, adminRequest]
  policyRevisionExact := rfl
  policyAddressExact := by
    change ⟨2200⟩ = policyAddressAt attenuatedCell examplePolicy
      (policyRevisionAt attenuatedCell examplePolicy)
    rw [attenuated_policy_revision_two]
    exact attenuated_policy_address_two.symm
  policyMembershipVerified := rfl
  policyVerified := rfl

def requestDigestScheme : RequestDigestScheme where
  digestWire := fun wire => ⟨wire.nonce + wire.effectsDigest⟩

def childLineage : childCapability.Lineage CredentialAuthorityState.noParents :=
  .attenuate childCapability rootCapability (.root rootCapability rfl rfl rfl)
    strict_edge

/-- Token is only a carrier for the exact capability evidence; the same common
policy epoch/address/membership gate remains in `tokenAuthorization`. -/
noncomputable def acceptedToken :
    AcceptedCredential requestDigestScheme lifecyclePortal
      (authState attenuatedCell) useRequest where
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
  simpa only [useRequest, adminRequest, authState, attenuated_policy_revision_two] using
    acceptedToken.authorization.policyAddressExact

/-! ## Revocation and epoch rotation -/

noncomputable def revokeDeclaration : RevokeDeclaration where
  key := .channel ⟨9⟩
  expectedPreRoot := attenuatedCell.root
  operationNullifier := 1003

def revokeDigest (_ : RevokeDeclaration) : Digest := ⟨9301⟩

noncomputable def revokeCodec : LawfulCodec RevokeDeclaration := by
  letI : Nonempty RevokeDeclaration := ⟨revokeDeclaration⟩
  exact codecOfCountable _

def revokeEvidence :
    RevokeEvidence attenuatedCell revokeDeclaration where
  preRootExact := rfl
  registered := by decide
  live := attenuated_live _

noncomputable def revoked :=
  acceptRevocation attenuatedCell (adminContext attenuatedCell) revokeCodec revokeDigest
    revokeDeclaration
    (adminAuthorization attenuatedCell (revokeDigest revokeDeclaration) 1003
      (adminArgsDigest (revokeCodec.encode revokeDeclaration)))
    rfl rfl rfl revokeEvidence

noncomputable abbrev revokedCell : Cell AuthorityMaterializer :=
  revoked.prepared.post

@[simp] theorem revoked_channel_exact :
    isRevoked revokedCell (.channel ⟨9⟩) = true :=
  revocation_post_exact revoked

theorem revoked_channel_authorizer_member :
    .channel ⟨9⟩ ∈ (authState revokedCell).revoked :=
  revocation_post_is_authorizer_member revoked

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
    policyEpochAt revokedCell examplePolicy = 2 := by decide

def rotateEvidence : RotateEpochEvidence revokedCell rotateDeclaration where
  preRootExact := rfl
  currentExact := revoked_policy_epoch_two
  successorExact := by decide

noncomputable def rotated :=
  acceptEpochRotation revokedCell (adminContext revokedCell) rotateCodec rotateDigest
    rotateDeclaration
    (adminAuthorization revokedCell (rotateDigest rotateDeclaration) 1004
      (adminArgsDigest (rotateCodec.encode rotateDeclaration)))
    rfl rfl rfl rotateEvidence

noncomputable abbrev finalCell : Cell AuthorityMaterializer :=
  rotated.prepared.post

@[simp] theorem final_policy_epoch_three :
    policyEpochAt finalCell examplePolicy = 3 := by
  simpa [rotateDeclaration, EpochTarget.read] using rotation_post_exact rotated

/-- Grant generation changes independently of the current resource law. -/
@[simp] theorem final_policy_revision_two :
    policyRevisionAt finalCell examplePolicy = 2 := by decide

@[simp] theorem final_policy_address_two :
    policyAddressAt finalCell examplePolicy 2 = ⟨2200⟩ := by decide

@[simp] theorem final_policy_address_three :
    policyAddressAt finalCell examplePolicy 3 = ⟨3300⟩ := by decide

@[simp] theorem final_channel_revoked :
    isRevoked finalCell (.channel ⟨9⟩) = true := by decide

/-- The revoked channel is registered present AND revoked present in the final
cell: its registration survived the revocation and the rotation. -/
theorem final_channel_registered_and_revoked :
    isRegistered finalCell (.channel ⟨9⟩) = true ∧
      isRevoked finalCell (.channel ⟨9⟩) = true := by
  decide

theorem final_channel_authorizer_member :
    .channel ⟨9⟩ ∈ (authState finalCell).revoked := by
  exact (mem_authState_revoked_iff finalCell _).2 final_channel_revoked

/-- The exact child token used above cannot be authorized after the same
canonical cell records the channel revocation. -/
theorem subsequent_child_authorization_rejected :
    ¬ childCapability.Admissible (authState finalCell)
      useRequest := by
  exact channel_revocation_rejected childCapability
    (authState finalCell) useRequest ⟨9⟩
    (by simp [childCapability, rootCapability]) final_channel_authorizer_member

/-- Epoch rotation supplies an independent rejection tooth: the old token's
policy epoch is no longer current. -/
theorem subsequent_child_policy_stale :
    childCapability.policyEpoch ≠
      (authState finalCell).policyEpoch childCapability.policyId := by
  intro current
  have impossible : (2 : Nat) = 3 := by
    exact current.trans final_policy_epoch_three
  contradiction

theorem wrong_scope_rejected :
    ¬ childCapability.Admissible (authState attenuatedCell)
      (useRequest.retarget ⟨701⟩) := by
  apply target_substitution_rejected childCapability
    (authState attenuatedCell) useRequest ⟨701⟩
  simp [TargetSet.Covers, childCapability, childScope]

/-! ## Replay and stale-root teeth at the semantic effect boundary -/

theorem issue_replay_rejected :
    IssueEvidence issuedCell issueDeclaration -> False := fun replay =>
  replay.reject_existing_id .object ⟨rootCapability, []⟩ issued_root_exact

noncomputable def staleIssueDeclaration : IssueDeclaration .object :=
  { issueDeclaration with
    expectedPreRoot := ⟨initialCell.root.value + 1⟩
    operationNullifier := 1999 }

theorem stale_root_rejected :
    IssueEvidence initialCell staleIssueDeclaration -> False := by
  intro stale
  have equal := stale.preRootExact
  have values := congrArg Digest.value equal
  simp [staleIssueDeclaration] at values

/-! ## Refusing poles at the validator

The steps above are accepted.  The same validator refuses the moves the
append-only planes forbid, naming the exact failing operation. -/

/-- Refuting pole (validator): the revoked channel's registration cannot be
erased; the free is rejected at operation 0. -/
theorem final_deregistration_rejected :
    CellState.validate AuthorityMaterializer finalCell finalCell.root
        [Op.free (L := layout) .registered (.channel ⟨9⟩) ()] =
      .rejected (.disabledOperation 0) :=
  deregister_rejected AuthorityMaterializer finalCell _

/-- Refuting pole (validator): nor can its revocation. -/
theorem final_unrevocation_rejected :
    CellState.validate AuthorityMaterializer finalCell finalCell.root
        [Op.free (L := layout) .revoked (.channel ⟨9⟩) ()] =
      .rejected (.disabledOperation 0) :=
  unrevoke_rejected AuthorityMaterializer finalCell _

/-! ## Payload-bearing durable use with an exact authority read guard -/

/-- The durable snapshot's root function is the deployed store root (cSHAKE256
under `DREGG.STORE.ROOT/v1`), the same function the authority cell uses. -/
abbrev fullRoot : List UInt8 -> Digest := StoreCodec.rootBytes

def authorityCellId : Minidregg.Kernel.DurableDataIntent.CellId := ⟨102⟩
def resultCellId : Minidregg.Kernel.DurableDataIntent.CellId := ⟨902⟩

def resultBeforeBytes : List UInt8 := [1, 2]
def resultAfterBytes : List UInt8 := [7, 8, 9]

noncomputable def durableBeforeBytes
    (cellId : Minidregg.Kernel.DurableDataIntent.CellId) : List UInt8 :=
  if cellId = authorityCellId then attenuatedCell.bytes
  else if cellId = resultCellId then resultBeforeBytes
  else []

noncomputable def durableBeforeModel :
    Snapshot TransactionId Minidregg.Kernel.DurableDataIntent.CellId
      StableNullifier ReplayEnvelope where
  roots := fun cellId => fullRoot (durableBeforeBytes cellId)
  consumed := fun _ => false
  available := fun _ => 10
  history := []
  journal := []

noncomputable def durableBefore : DataSnapshot fullRoot where
  model := durableBeforeModel
  canonicalBytes := durableBeforeBytes
  coherent := fun _ => rfl

def useWrite : DataWrite where
  cellId := resultCellId
  expectedPre := fullRoot resultBeforeBytes
  exactPost := fullRoot resultAfterBytes
  canonicalPostBytes := resultAfterBytes

def useNullifier : StableNullifier where
  codecVersion := 1
  domain := lifecycleDomain
  nullifierId := ⟨2001⟩
  canonicalBytes := [116, 111, 107, 101, 110, 45, 117, 115, 101]

def useEvent : StableEvent where
  codecVersion := 1
  domain := lifecycleDomain
  eventId := ⟨9200⟩
  canonicalBytes := [117, 115, 101, 45, 97, 99, 99, 101, 112, 116, 101, 100]

def baseUseIntent : DataIntent fullRoot where
  transactionId := ⟨2001⟩
  writes := [useWrite]
  readGuards := []
  nullifiers := [useNullifier]
  exactCharge := fun _ => 1
  event := useEvent
  subject := none
  postRootsBound := by
    intro write member
    have exact : write = useWrite := by simpa using member
    subst write
    rfl
  guardsReadOnly := by simp

def sharedFullDigest : SharedDigest AuthorityMaterializer fullRoot where
  exact := rfl

theorem authority_read_only :
    authorityCellId ∉ baseUseIntent.writes.map DataWrite.cellId := by
  decide

noncomputable def guardedUseIntent : DataIntent fullRoot :=
  guardPolicyRegistry attenuatedCell authorityCellId sharedFullDigest
    baseUseIntent authority_read_only

@[simp] theorem guarded_use_payload_exact :
    guardedUseIntent.writes = [useWrite] /\
      guardedUseIntent.nullifiers = [useNullifier] /\
      guardedUseIntent.event = useEvent := by
  simp [guardedUseIntent, guardPolicyRegistry, baseUseIntent]

@[simp] theorem guarded_use_observes_exact_authority_root :
    guardedUseIntent.readGuards =
      [{ cellId := authorityCellId, expectedRoot := attenuatedCell.root }] := by
  simp [guardedUseIntent, baseUseIntent,
    guardPolicyRegistry_readGuards]

@[simp] theorem base_use_ready :
    baseUseIntent.preflight durableBefore = .ok () := by
  simp [DataIntent.preflight, DataIntent.readGuardsMatchCheck, DataIntent.erase,
    Intent.preflight, Intent.rootsMatchCheck, Intent.nullifiersFreshCheck,
    Charge.fundedCheck, baseUseIntent, durableBefore, durableBeforeModel,
    durableBeforeBytes, useWrite, useNullifier, resultCellId, authorityCellId,
    Lane.allCheck]

@[simp] theorem guarded_use_ready :
    guardedUseIntent.preflight durableBefore = .ok () := by
  apply guardPolicyRegistry_preflight_ready attenuatedCell authorityCellId
    sharedFullDigest baseUseIntent authority_read_only durableBefore
  · rfl
  · exact base_use_ready

@[simp] theorem guarded_use_installs_payload :
    Minidregg.Kernel.DurableDataIntent.execute .complete durableBefore
      guardedUseIntent =
        .accepted (DataSnapshot.install durableBefore guardedUseIntent) := by
  apply Minidregg.Kernel.DurableDataIntent.execute_complete_ready
  · rfl
  · exact guarded_use_ready

noncomputable abbrev durableAfterUse : DataSnapshot fullRoot :=
  DataSnapshot.install durableBefore guardedUseIntent

/-- The first installation debits exactly the Lean-derived charge in every
closed resource lane. -/
theorem first_use_exact_charge :
    guardedUseIntent.exactCharge + durableAfterUse.model.available =
      durableBefore.model.available := by
  change guardedUseIntent.erase.exactCharge +
      (Snapshot.install durableBefore.model guardedUseIntent.erase).available =
        durableBefore.model.available
  apply Snapshot.install_exact_debit
  intro lane
  change 1 ≤ 10
  exact (by decide : (1 : Nat) ≤ 10)

@[simp] theorem installed_use_bytes :
    durableAfterUse.canonicalBytes resultCellId = resultAfterBytes := by
  decide

@[simp] theorem exact_retry_is_replay :
    Minidregg.Kernel.DurableDataIntent.execute .complete durableAfterUse
      guardedUseIntent = .replayed guardedUseIntent.erase := by
  simp [Minidregg.Kernel.DurableDataIntent.execute, durableAfterUse,
    DataSnapshot.install_model, Snapshot.lookupRecorded,
    Intent.sameCheck_self]

/-- Journal lookup precedes root/nullifier/charge checks, so an exact retry is
an identity on the already-debited snapshot: no second charge is possible. -/
theorem exact_retry_no_double_charge :
    (Minidregg.Kernel.DurableDataIntent.execute .complete durableAfterUse
      guardedUseIntent).storeAfter durableAfterUse = durableAfterUse /\
      forall lane,
        ((Minidregg.Kernel.DurableDataIntent.execute .complete durableAfterUse
          guardedUseIntent).storeAfter durableAfterUse).model.available lane =
            durableAfterUse.model.available lane := by
  rw [exact_retry_is_replay]
  exact ⟨rfl, fun _ => rfl⟩

/-- The authority update between the admitted use and settlement changed the
authority store: the grant generation moved from two to three. -/
theorem authority_update_changes_store :
    finalCell.logical ≠ attenuatedCell.logical := by
  intro same
  have epochs : policyEpochAt finalCell examplePolicy =
      policyEpochAt attenuatedCell examplePolicy := by
    unfold policyEpochAt
    rw [same]
  rw [final_policy_epoch_three, attenuated_policy_epoch_two] at epochs
  exact absurd epochs (by decide)

/-- Under the pair-scoped no-collision premise for exactly these two stores,
the authority update moves the root a durable read guard observes. -/
theorem authority_update_moves_root
    (binding : CellState.PairBindingPremise AuthorityMaterializer
      finalCell.logical attenuatedCell.logical) :
    finalCell.root ≠ attenuatedCell.root :=
  binding.root_ne authority_update_changes_store

noncomputable def afterAuthorityUpdateBytes
    (cellId : Minidregg.Kernel.DurableDataIntent.CellId) : List UInt8 :=
  if cellId = authorityCellId then finalCell.bytes
  else durableBeforeBytes cellId

noncomputable def afterAuthorityUpdateModel :
    Snapshot TransactionId Minidregg.Kernel.DurableDataIntent.CellId
      StableNullifier ReplayEnvelope :=
  { durableBeforeModel with
    roots := fun cellId => fullRoot (afterAuthorityUpdateBytes cellId) }

noncomputable def afterAuthorityUpdate : DataSnapshot fullRoot where
  model := afterAuthorityUpdateModel
  canonicalBytes := afterAuthorityUpdateBytes
  coherent := fun _ => rfl

/-- The old accepted use cannot cross settlement after the authority cell has
moved.  This is conditional exactly on the pair-scoped no-collision premise
for the two authority stores. -/
theorem authority_update_rejects_old_use
    (binding : CellState.PairBindingPremise AuthorityMaterializer
      finalCell.logical attenuatedCell.logical) :
    guardedUseIntent.preflight afterAuthorityUpdate =
      .error .staleReadGuard := by
  apply policy_registry_rotation_rejects_old_intent attenuatedCell
    authorityCellId sharedFullDigest baseUseIntent authority_read_only
    afterAuthorityUpdate
  simpa [afterAuthorityUpdate, afterAuthorityUpdateModel,
    afterAuthorityUpdateBytes, authorityCellId] using authority_update_moves_root binding

/-- No filesystem, database, RPC stack, or physical transport is claimed here.
Such a claim must inhabit the existing simulation boundary. -/
abbrev PhysicalDurabilityCeiling
    (PhysicalState : Type) (PhysicalStep : PhysicalState ->
      DataIntent fullRoot -> PhysicalState -> Type)
    (Represents : PhysicalState -> DataSnapshot fullRoot -> Prop) : Prop :=
  ImplementationRefinement fullRoot PhysicalState PhysicalStep Represents

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.initial_channel_registered_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_channel_registered_live
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.issued_root_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms issued_root_registered
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.attenuated_child_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuated_child_registered
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.final_channel_registered_and_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms final_channel_registered_and_revoked
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.final_deregistration_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms final_deregistration_rejected
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.authority_update_moves_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authority_update_moves_root
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.subsequent_child_authorization_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subsequent_child_authorization_rejected
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.first_use_exact_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_use_exact_charge
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.exact_retry_no_double_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_retry_no_double_charge
/-- info: 'Minidregg.Assurance.DeployedCredentialLifecycle.authority_update_rejects_old_use' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authority_update_rejects_old_use

end Minidregg.Assurance.DeployedCredentialLifecycle
