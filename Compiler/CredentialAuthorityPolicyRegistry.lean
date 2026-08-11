/-
# Compiler.CredentialAuthorityPolicyRegistry -- the bounded page reaches settlement

`CredentialAuthorityPageMaterializer` supplies a real, framed four-slot
authority page.  `Kernel.CanonicalPolicyRegistry` proves exact policy selection
and stale-root rejection for the canonical `CredentialAuthorityState` cell.
This module joins those two constructions without adding a second policy root:

* the selected page projects to the canonical authority logical state;
* a focused lawful authority codec emits the page's exact framed bytes for
  that state (and a disjoint tagged fallback for every other logical state);
* the policy source has one pinned lawful codec and cSHAKE content address;
* page lookup, registry resolution, content fetch, authenticated membership,
  compiler acceptance, and `Authorized` meet in one `SelectionPayload`;
* the exact page root is installed as a read-only durable guard; and
* a pair-bound page rotation makes the previously admitted intent stale.

The inherited non-policy portal remains an input.  In particular this module
does not turn an accepting signature Boolean into signature soundness.  Hash
collision resistance is requested only for the concrete old/new page pair.
The durable result remains a model result; a physical store must still supply
`DurableDataIntent.ImplementationRefinement`.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Kernel.CanonicalPolicyRegistry
import Mathlib.Data.Char
import Mathlib.Tactic.DeriveCountable
import Theory.DeployedMaterializerWitness

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
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Stable policy-source content address -/

private theorem charToNat_injective : Function.Injective Char.toNat := by
  intro left right equal
  apply Char.ext
  exact UInt32.toNat_inj.mp equal

noncomputable instance stringCountable : Countable String :=
  (show Function.Injective
      (fun value : String => value.toList.map Char.toNat) from by
    intro left right equal
    have charsEqual : left.toList = right.toList :=
      (List.map_injective_iff.mpr charToNat_injective) equal
    rw [← left.ofList_toList, ← right.ofList_toList, charsEqual]).countable

deriving instance Countable for Minidregg.Pred.Vk
deriving instance Countable for Minidregg.Pred.Pred
deriving instance Countable for Minidregg.Pred.PredList
deriving instance Countable for PolicyRecord

/-- Version/tag byte for the policy-source codec.  The following natural is
the pinned `Encodable` enumeration of the complete first-order record. -/
def policyRecordFrame : UInt8 := 165

/-- A total lawful codec for the exact `PolicyRecord` carrier.  The derived
enumeration is part of this codec version; changing it changes source bytes. -/
noncomputable def policyRecordCodec : LawfulCodec PolicyRecord := by
  letI : Encodable PolicyRecord := Encodable.ofCountable PolicyRecord
  exact
    { encode := fun record =>
        policyRecordFrame ::
          StreamCodec.nat.toLawful.encode (Encodable.encode record)
      decode := fun bytes =>
        match bytes with
        | frame :: payload =>
            if frame = policyRecordFrame then
              match StreamCodec.nat.toLawful.decode payload with
              | some code => Encodable.decode code
              | none => none
            else none
        | [] => none
      decode_encode := by
        intro record
        change (match StreamCodec.nat.toLawful.decode
          (StreamCodec.nat.toLawful.encode (Encodable.encode record)) with
          | some code => Encodable.decode code
          | none => none) = some record
        rw [StreamCodec.nat.toLawful.decode_encode]
        exact Encodable.encodek record }

def policyRecordCustomization : List UInt8 :=
  "LOOM.AUTH.POLICY.RECORD/v1".toUTF8.toList

def policyHashBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash policyRecordCustomization bytes).digest

noncomputable def policyRecordDigest (record : PolicyRecord) : Digest :=
  policyHashBytes (policyRecordCodec.encode record)

/-- Pair-scoped collision boundary for policy substitution.  Ordinary exact
selection below needs only the digest equality; semantic substitution claims
must additionally supply this premise for the particular pair in question. -/
structure PolicyRecordPairBinding (left right : PolicyRecord) : Prop where
  noCollision :
    policyHashBytes (policyRecordCodec.encode left) =
        policyHashBytes (policyRecordCodec.encode right) ->
      left = right

/-! ## One concrete committed policy page -/

noncomputable def committedPolicy : CommittedPolicy where
  address := policyRecordDigest demoRecord
  record := demoRecord

noncomputable def policyEntry : Entry :=
  .policy demoRequest.policyId demoRequest.policyEpoch committedPolicy.address

noncomputable def policyPage : Page where
  authorityDomain := ⟨91000⟩
  pageNumber := 0
  slot0 := some policyEntry
  slot1 := none
  slot2 := none
  slot3 := none

noncomputable def policyPageCell : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some policyPage))

theorem policyPage_valid : policyPage.Valid := by
  simp [Page.Valid, Page.fields, Page.entries, policyPage, policyEntry, Entry.fields]

@[simp] theorem policyPage_contains : policyPage.Contains policyEntry := by
  simp [Page.Contains, Page.entries, policyPage]

@[simp] theorem policyPage_epoch_exact :
    policyPage.policyEpochAt demoRequest.policyId = demoRequest.policyEpoch := by
  simp [Page.policyEpochAt, Page.toCanonicalState, Page.entries, policyPage,
    policyEntry, Entry.install]
  rfl

@[simp] theorem policyPage_address_exact :
    policyPage.policyAddressAt demoRequest.policyId demoRequest.policyEpoch =
      committedPolicy.address := by
  simp [Page.policyAddressAt, Page.toCanonicalState, Page.entries, policyPage,
    policyEntry, Entry.install]
  rfl

@[simp] theorem policyPageCell_bytes :
    policyPageCell.bytes = wireFrame ++ 1 :: pageStream.encode policyPage :=
  rfl

/-! ## Exact page bytes as a canonical authority cell -/

/-- Countability supplies only the disjoint fallback branch.  The selected
page state itself never uses these existential bytes. -/
noncomputable def fallbackAuthorityCodec :
    LawfulCodec (LogicalState CredentialAuthorityState.schema.{0, 0}) :=
  logicalCodecOfCountable CredentialAuthorityState.schema.{0, 0}
    (fun resource => nomatch resource)

theorem fallback_tag_ne_page_bytes (bytes : List UInt8) :
    policyRecordFrame :: bytes ≠ policyPageCell.bytes := by
  intro equal
  have heads := congrArg List.head? equal
  norm_num [policyRecordFrame, policyPageCell, materializer, stateCodec,
    wireFrame] at heads
  exact (show (165 : UInt8) ≠ 76 by decide) heads

/-- A lawful total codec focused on this bounded page.  The exact canonical
page projection receives the page's production frame.  All other authority
states receive a disjoint leading tag followed by the lawful countable
fallback, so decoding remains total and injective. -/
noncomputable def focusedAuthorityCodec :
    LawfulCodec (LogicalState CredentialAuthorityState.schema.{0, 0}) := by
  classical
  let selected := policyPage.toCanonicalState
  let fallback := fallbackAuthorityCodec
  exact
    { encode := fun logical =>
        if logical = selected then policyPageCell.bytes
        else policyRecordFrame :: fallback.encode logical
      decode := fun bytes =>
        if bytes = policyPageCell.bytes then some selected
        else
          match bytes with
          | tag :: payload =>
              if tag = policyRecordFrame then fallback.decode payload else none
          | [] => none
      decode_encode := by
        intro logical
        by_cases selectedExact : logical = selected
        · subst logical
          simp
        · have taggedDifferent :
              policyRecordFrame :: fallback.encode logical ≠
                policyPageCell.bytes :=
            fallback_tag_ne_page_bytes _
          rw [if_neg selectedExact]
          simp only
          rw [if_neg taggedDifferent]
          simp [fallback.decode_encode] }

noncomputable def authorityMaterializer :
    CredentialAuthorityState.Materializer where
  codec := focusedAuthorityCodec
  rootBytes := CredentialAuthorityPageMaterializer.rootBytes

noncomputable def authorityCell : RegistryCell authorityMaterializer :=
  CellState.materialize authorityMaterializer policyPage.toCanonicalState

@[simp] theorem authorityCell_bytes_exact :
    authorityCell.bytes = policyPageCell.bytes := by
  classical
  change (if policyPage.toCanonicalState = policyPage.toCanonicalState then
      policyPageCell.bytes
    else policyRecordFrame :: fallbackAuthorityCodec.encode
      policyPage.toCanonicalState) = policyPageCell.bytes
  rw [if_pos rfl]

@[simp] theorem authorityCell_root_exact :
    authorityCell.root = policyPageCell.root := by
  change CredentialAuthorityPageMaterializer.rootBytes authorityCell.bytes =
    CredentialAuthorityPageMaterializer.rootBytes policyPageCell.bytes
  rw [authorityCell_bytes_exact]

def projection : CredentialAuthorityState.ProjectionUniverse :=
  { revocationKeys := ∅ }

@[simp] theorem authorityCell_epoch_exact :
    (CredentialAuthorityState.authState projection authorityCell).policyEpoch
        demoRequest.policyId = demoRequest.policyEpoch := by
  change (some demoRequest.policyEpoch).getD 0 = demoRequest.policyEpoch
  rfl

@[simp] theorem authorityCell_address_exact :
    addressAt authorityCell demoRequest.policyId demoRequest.policyEpoch =
      committedPolicy.address := by
  change (some committedPolicy.address).getD ⟨0⟩ = committedPolicy.address
  rfl

/-! ## Page membership, registry, and compiler admission -/

/-- The inherited portal owns every non-membership verifier.  Page membership
is replaced by an exact decidable reading of this page and root.  Therefore no
signature acceptance or signature-soundness theorem is synthesized here. -/
noncomputable def pagePortal (base : Portal) : Portal where
  SignatureWitness := base.SignatureWitness
  ProofWitness := base.ProofWitness
  CapabilityCommitmentWitness := base.CapabilityCommitmentWitness
  MembershipWitness := Unit
  IssuerWitness := base.IssuerWitness
  NonRevocationWitness := base.NonRevocationWitness
  PolicyWitness := base.PolicyWitness
  policyAddress := base.policyAddress
  verifySignature := base.verifySignature
  verifyProof := base.verifyProof
  verifyCapabilityCommitment := base.verifyCapabilityCommitment
  verifyMembership := fun root address _ =>
    decide (root = policyPageCell.root /\
      address = committedPolicy.address /\ policyPage.Contains policyEntry)
  verifyIssuer := base.verifyIssuer
  verifyNonRevocation := base.verifyNonRevocation
  verifyCommittedPolicy := base.verifyCommittedPolicy

noncomputable def policyRegistry : PolicyRegistry where
  resolve := fun policyId epoch =>
    if policyId = demoRequest.policyId /\ epoch = demoRequest.policyEpoch then
      some committedPolicy
    else none

noncomputable def config (base : Portal) : CanonicalPolicyConfig (ZMod 13) where
  base := pagePortal base
  registry := policyRegistry
  recordDigest := policyRecordDigest
  stateDigest := demoStateDigest
  stepDigest := demoStepDigest

@[simp] theorem config_verifyMembership (base : Portal)
    (root address : Digest) :
    (config base).portal.verifyMembership root address () =
      decide (root = policyPageCell.root /\
        address = committedPolicy.address /\ policyPage.Contains policyEntry) :=
  rfl

@[simp] theorem registry_resolves (base : Portal) :
    (config base).registry.resolve demoRequest.policyId demoRequest.policyEpoch =
      some committedPolicy := by
  simp [config, policyRegistry]

noncomputable def contentAddressing (base : Portal) :
    ContentAddressing (config base) where
  codec := policyRecordCodec
  hashBytes := policyHashBytes
  recordDigest_exact := by intro record; rfl

noncomputable def payloadStore : PayloadStore where
  fetch := fun address =>
    if address = committedPolicy.address then
      some (policyRecordCodec.encode committedPolicy.record)
    else none

noncomputable def payloadAvailability (base : Portal) :
    PayloadAvailability (config base) (contentAddressing base) payloadStore where
  fetch_resolved := by
    intro policyId epoch selected resolved
    by_cases key :
        policyId = demoRequest.policyId /\ epoch = demoRequest.policyEpoch
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
  canonicalWitness committedPolicy kOld kNew

theorem policy_verifies (base : Portal) :
    (config base).verifies demoRequest policyWitness = true := by
  have preRootExact :
      (config base).stateDigest kOld = demoRequest.preStateRoot := by
    simp [config, demoStateDigest]
  have effectDigestExact :
      (config base).stepDigest kOld kNew = demoRequest.effectsDigest := by
    simp [config, demoStepDigest]
  apply (canonical_verifies_iff_eval
    (config := config base) (request := demoRequest)
    (committed := committedPolicy) (oldState := kOld) (newState := kNew)
    (resolved := registry_resolves base)
    (policyIdExact := rfl) (versionExact := rfl)
    (domainExact := rfl) (semanticsExact := rfl)
    (recordDigestExact := rfl)
    (preRootExact := preRootExact) (effectDigestExact := effectDigestExact)
    (supportedExact := by decide) (castExact := by decide)).mpr
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
      (CredentialAuthorityState.authState projection authorityCell)
      demoRequest where
  evidence := .proof proofWitness (by
    simpa [config, CanonicalPolicyConfig.portal, pagePortal] using proofAccepted)
  policyWitness := policyWitness
  policyMembershipWitness := ()
  policyEpochExact := by
    exact authorityCell_epoch_exact.symm
  policyAddressExact := by
    change committedPolicy.address =
      addressAt authorityCell demoRequest.policyId demoRequest.policyEpoch
    exact authorityCell_address_exact.symm
  policyMembershipVerified := by
    change (config base).portal.verifyMembership authorityCell.root
      (addressAt authorityCell demoRequest.policyId demoRequest.policyEpoch)
      () = true
    rw [authorityCell_address_exact]
    exact page_membership_verified base
  policyVerified := by
    rw [portal_verifyCommittedPolicy]
    rw [Bool.and_eq_true]
    refine ⟨?_, policy_verifies base⟩
    apply decide_eq_true
    change addressAt authorityCell demoRequest.policyId demoRequest.policyEpoch =
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
  @SelectionPayload.ofAuthorized _ _ _ (config base)
    (contentAddressing base) payloadStore (membershipSemantics base)
    (payloadAvailability base) authorityMaterializer projection authorityCell
    .object demoRequest (positiveAuthorized base proofWitness proofAccepted)
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
  .policy demoRequest.policyId (demoRequest.policyEpoch + 1) ⟨91040⟩

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

/-- Stale page-update tooth.  A policy epoch/address rotation changes the
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

end Minidregg.Compiler.CredentialAuthorityPolicyRegistry

/-! Concrete join audit. -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.focusedAuthorityCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.focusedAuthorityCodec
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.positiveAuthorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.positiveAuthorized
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.selectedPayload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.selectedPayload
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.guardedIntent_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.guardedIntent_ready
/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.rotated_page_rejects_old_intent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.rotated_page_rejects_old_intent
