/-
# Compiler.CredentialAuthorityPolicyRegistry -- the bounded page reaches settlement

`CredentialAuthorityPageMaterializer` supplies a real, framed four-slot
authority page.  `Kernel.CanonicalPolicyRegistry` proves exact policy selection
and stale-root rejection for the canonical `CredentialAuthorityState` cell.
This module joins those two constructions without adding a second policy root:

* the selected page projects to the canonical authority logical state;
* a schema-owned authority view reads that physical page directly, retaining
  its actual materialized bytes and root for selection and settlement;
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
import Compiler.PolicyRecordCodec
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

/-- Schema-owned projection for every physical authority page. The decoder
and receiver require page validity before admission; all roots still come
from the exact materialized page bytes. -/
def projection : CredentialAuthorityState.StateProjection
    CredentialAuthorityPageMaterializer.schema where
  toCanonicalState := fun logical =>
    match pageAt logical with
    | some page => page.toCanonicalState
    | none =>
        { fields := 0
          resources := fun resource => nomatch resource }
  revocationKeys := fun logical =>
    match pageAt logical with
    | some page => page.revoked
    | none => ∅

/-! ## Canonical page snapshots and source resolution -/

structure Snapshot where
  private mk ::
  page : Page
  valid : page.Valid

def Snapshot.ofPage (page : Page) (valid : page.Valid) : Snapshot := ⟨page, valid⟩

def Snapshot.cell (snapshot : Snapshot) : Materialized materializer :=
  materialize materializer (stateOfOption (some snapshot.page))

/-- Canonical page bytes are checked at the receiving boundary, including the
page validity invariant. A caller cannot assert an independent page root. -/
def decodeSnapshot (bytes : List UInt8) :
    Option { snapshot : Snapshot // snapshot.cell.bytes = bytes } :=
  match materializer.codec.decode bytes with
  | none => none
  | some logical =>
      match pageAt logical with
      | none => none
      | some page =>
          if valid : page.Valid then
            let snapshot := Snapshot.ofPage page valid
            if canonical : snapshot.cell.bytes = bytes then
              some ⟨snapshot, canonical⟩
            else none
          else none

/-- Data returned by the actual resolver retains every checked source fact. -/
structure LoadedPolicy (snapshot : Snapshot) (store : PayloadStore)
    (policyId : PolicyId) (epoch : Epoch) where
  committed : CommittedPolicy
  current : snapshot.page.policyEpochAt policyId = epoch
  member : snapshot.page.Contains (.policy policyId epoch committed.address)
  policyIdExact : committed.record.policyId = policyId
  epochExact : committed.record.version = epoch
  domainExact : committed.record.domain = snapshot.page.authorityDomain
  addressExact : policyRecordDigest committed.record = committed.address
  fetched : store.fetch committed.address = some (policyRecordCodec.encode committed.record)

/-- Resolve from current canonical authority state, then fetch and decode the
selected source. A store response cannot choose another address or record. -/
def loadPolicy (snapshot : Snapshot) (store : PayloadStore)
    (policyId : PolicyId) (epoch : Epoch) : Option (LoadedPolicy snapshot store policyId epoch) :=
  let address := snapshot.page.policyAddressAt policyId epoch
  if current : snapshot.page.policyEpochAt policyId = epoch then
    if member : snapshot.page.Contains (.policy policyId epoch address) then
      match fetched : store.fetch address with
      | none => none
      | some bytes =>
          match decoded : policyRecordCodec.decode bytes with
          | none => none
          | some record =>
              if policyIdExact : record.policyId = policyId then
                if epochExact : record.version = epoch then
                  if domainExact : record.domain = snapshot.page.authorityDomain then
                    if addressExact : policyRecordDigest record = address then
                      some
                        { committed := ⟨address, record⟩
                          current := current
                          member := member
                          policyIdExact := policyIdExact
                          epochExact := epochExact
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
  resolve := fun policyId epoch =>
    (loadPolicy snapshot store policyId epoch).map LoadedPolicy.committed

def hasPolicyAddress (page : Page) (address : Digest) : Bool :=
  page.entries.any fun entry =>
    match entry with
    | .policy _ _ selected => selected == address
    | _ => false

def pageMember (snapshot : Snapshot) (root address : Digest) : Prop :=
  root = snapshot.cell.root ∧ hasPolicyAddress snapshot.page address = true

instance pageMemberDecidable (snapshot : Snapshot) (root address : Digest) :
    Decidable (pageMember snapshot root address) := by
  unfold pageMember
  infer_instance

/-- This complete-page membership check is exact for policy selection. Other
evidence families keep the deployment's verifier functions. -/
def pagePortal (snapshot : Snapshot) (base : Portal) : Portal where
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
  verifyMembership := fun root address _ => decide (pageMember snapshot root address)
  verifyIssuer := base.verifyIssuer
  verifyNonRevocation := base.verifyNonRevocation
  verifyCommittedPolicy := base.verifyCommittedPolicy

/-- The receiving constructor requires the exact source-derived candidate
context. Its signature contains no binding-mode selector, digest callback or
predicate-view callback. -/
def config {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal)
    (step : PolicyStepContext) : CanonicalPolicyConfig F where
  base := pagePortal snapshot base
  registry := policyRegistry snapshot store
  recordDigest := policyRecordDigest
  stepBinding := .canonical step

@[simp] theorem config_uses_canonical {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    (config (F := F) snapshot store base step).stepBinding = .canonical step := rfl

def contentAddressing {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    ContentAddressing (config (F := F) snapshot store base step) where
  codec := policyRecordCodec
  hashBytes := policyHashBytes
  recordDigest_exact := by intro record; rfl

/-- Availability for resolved records is proved from the same checked fetch,
not assumed for an independent logical registry. -/
def payloadAvailability {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    PayloadAvailability (config (F := F) snapshot store base step)
      (contentAddressing snapshot store base step) store where
  fetch_resolved := by
    intro policyId epoch committed resolved
    cases loaded : loadPolicy snapshot store policyId epoch with
    | none => simp [config, policyRegistry, loaded] at resolved
    | some value =>
        have equal : value.committed = committed := by
          simpa [config, policyRegistry, loaded] using resolved
        simpa only [equal] using value.fetched

def membershipSemantics {F : Type} [Field F] [DecidableEq F]
    (snapshot : Snapshot) (store : PayloadStore) (base : Portal) (step : PolicyStepContext) :
    MembershipSemantics (config (F := F) snapshot store base step).portal where
  Member := pageMember snapshot
  verifier_sound := by
    intro root address witness accepted
    exact of_decide_eq_true accepted

/-! ## Explicit model examples of selection and stale-guard rejection

The examples below keep the older small-field model parameters to exercise
the generic kernel theorems. The receiving constructor above never selects
their model binding or fixed registry.
-/
namespace Example



def committedPolicy : CommittedPolicy where
  address := policyRecordDigest demoRecord
  record := demoRecord

def policyEntry : Entry :=
  .policy demoRequest.policyId demoRequest.policyEpoch committedPolicy.address

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

/-! ## The physical page is the canonical authority cell -/

/-- The registry consumes the actual materializer; there is no focused
encoding, countable fallback, or second synthetic cell for its projection. -/
def authorityMaterializer := CredentialAuthorityPageMaterializer.materializer

def authorityCell : RegistryCell authorityMaterializer := policyPageCell

@[simp] theorem authorityCell_bytes_exact :
    authorityCell.bytes = policyPageCell.bytes := rfl

@[simp] theorem authorityCell_root_exact :
    authorityCell.root = policyPageCell.root := rfl

@[simp] theorem authorityCell_epoch_exact :
    (projection.authState authorityCell).policyEpoch
        demoRequest.policyId = demoRequest.policyEpoch := by
  change (some demoRequest.policyEpoch).getD 0 = demoRequest.policyEpoch
  rfl

@[simp] theorem authorityCell_address_exact :
    addressAt projection authorityCell demoRequest.policyId demoRequest.policyEpoch =
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

def policyRegistry : PolicyRegistry where
  resolve := fun policyId epoch =>
    if policyId = demoRequest.policyId /\ epoch = demoRequest.policyEpoch then
      some committedPolicy
    else none

def config (base : Portal) : CanonicalPolicyConfig (ZMod 13) where
  base := pagePortal base
  registry := policyRegistry
  recordDigest := policyRecordDigest
  stepBinding := .model demoStateDigest demoStepDigest

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
      (projection.authState authorityCell)
      demoRequest where
  evidence := .proof proofWitness (by
    simpa [config, CanonicalPolicyConfig.portal, pagePortal] using proofAccepted)
  policyWitness := policyWitness
  policyMembershipWitness := ()
  policyEpochExact := by
    exact authorityCell_epoch_exact.symm
  policyAddressExact := by
    change committedPolicy.address =
      addressAt projection authorityCell demoRequest.policyId demoRequest.policyEpoch
    exact authorityCell_address_exact.symm
  policyMembershipVerified := by
    change (config base).portal.verifyMembership authorityCell.root
      (addressAt projection authorityCell demoRequest.policyId demoRequest.policyEpoch)
      () = true
    rw [authorityCell_address_exact]
    exact page_membership_verified base
  policyVerified := by
    rw [portal_verifyCommittedPolicy]
    rw [Bool.and_eq_true]
    refine ⟨?_, policy_verifies base⟩
    apply decide_eq_true
    change addressAt projection authorityCell demoRequest.policyId demoRequest.policyEpoch =
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
