/-
# Assurance.QuotaGcSettlementWitness -- a non-vacuous safe compaction

This closed witness exercises the quota/GC kernel rather than merely exposing
its proposition carriers.  A two-slot page contains one tombstoned object with
an expired canonical lease.  The object is absent from roots, finalized
history, and every live reachability closure.  A scoped authority admits one
compaction, its canonical fee posting and page removal share one durable
intent, and all exact quota lanes are funded.  Companion teeth show that the
same object cannot be collected once finalized or referenced by a live object.
-/
import Kernel.QuotaGcSettlement

namespace Minidregg.Assurance.QuotaGcSettlementWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.QuotaGcSettlement

set_option autoImplicit false

local instance canonicalFieldDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Field := by
  change DecidableEq CanonicalResourceKernel.Field
  infer_instance

local instance canonicalResourceDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Resource := by
  change DecidableEq Empty
  infer_instance

def expiredRecord : LeaseRecord where
  holder := 1
  lessor := 2
  asset := 0
  prepaid := 5
  startsAt := 0
  expiresAt := 5

def book : Book where
  accounts := {0, 1, 2}
  balances :=
    DFinsupp.single (0, 0) (-10) +
      DFinsupp.single (1, 0) 10
  leaseRecords := DFinsupp.single 8 (some expiredRecord)

def logical : LogicalState CanonicalResourceKernel.schema where
  fields := (0 : FieldStore CanonicalResourceKernel.schema).write .book book
  resources := fun resource => nomatch resource

noncomputable def resourcePre : Materialized CanonicalResourceKernel.materializer :=
  materialize CanonicalResourceKernel.materializer logical

@[simp] theorem resourcePre_book : logicalBook resourcePre.logical = book := by
  simp [resourcePre, logical, logicalBook, materialize, FieldStore.read]

def object : Object where
  contentId := 11
  owner := 1
  leaseId := 8
  payload := [10, 20, 30]
  status := .tombstoned 6

def page : Page 2 where
  epoch := 7
  slots := fun slot => if slot.val = 0 then some object else none

def protection : Protection where
  roots := []
  edges := []
  historyFinalized := []

def command : Command 2 := .compact 7 10 ⟨0, by decide⟩ object

def config : Config where
  collector := 2
  lessor := 2
  asset := 0
  baseFee := 3
  feePerPayloadByte := 0

@[simp] theorem resourceOperation_exact :
    command.resourceOperation config = .fee 1 2 0 3 := by
  rfl

def resourceAdmission :
    CanonicalResourceKernel.Admission book (command.resourceOperation config) where
  sourcePresent := by decide
  destinationPresent := by decide
  sourceSolvent := Or.inr (by decide)
  leaseWellFormed := trivial

noncomputable def accepted :
    Accepted resourcePre (command.resourceOperation config) :=
  Accepted.ofAdmission (by simpa using resourceAdmission)

def manifest := AuthorizedResourceCharge.witnessManifest
def context := AuthorizedResourceCharge.witnessContext

noncomputable def authorization :
    Authorized demoPortal demoState (context.request manifest accepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def exact : Charge :=
  totalCharge manifest accepted page protection command

@[simp] theorem accepted_exact_fee :
    AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit = 3 := by
  rw [AuthorizedResourceCharge.exactCharge_feeDebit]
  apply incidenceOnlyBillable
  · rfl
  · rfl
  · intro lane different
    cases lane <;> simp_all [manifest, AuthorizedResourceCharge.witnessManifest,
      AuthorizedResourceCharge.witnessUnitFee]

@[simp] theorem exact_fee : exact .feeDebit = 3 := by
  rw [exact, totalCharge_feeDebit, accepted_exact_fee]

noncomputable def limits : Limits where
  maxOccupied := 1
  maxPageBytes := 64
  available := exact

theorem page_valid : page.Valid := by
  intro left right leftObject rightObject leftStored rightStored sameId
  have leftZero : left.val = 0 := by
    by_contra nonzero
    change (if left.val = 0 then some object else none) = some leftObject at leftStored
    rw [if_neg nonzero] at leftStored
    contradiction
  have rightZero : right.val = 0 := by
    by_contra nonzero
    change (if right.val = 0 then some object else none) = some rightObject at rightStored
    rw [if_neg nonzero] at rightStored
    contradiction
  exact Fin.ext (leftZero.trans rightZero.symm)

theorem post_valid : (command.apply page).Valid := by
  intro left right leftObject rightObject leftStored rightStored sameId
  have allNone : forall slot, (command.apply page).slots slot = none := by
    intro slot
    fin_cases slot <;> rfl
  rw [allNone left] at leftStored
  contradiction

theorem expired : ExpiredLease book object command.height := by
  refine ⟨expiredRecord, ?_, by decide⟩
  constructor
  · simp [book, object, Book.leases, expiredRecord]
  · rfl

theorem unprotected : Not (Protected page protection object.contentId) := by
  intro protectedEvidence
  rcases protectedEvidence with rooted | protectedEvidence
  · simp [protection] at rooted
  rcases protectedEvidence with finalized | ⟨slot, source, stored, live, _, _⟩
  · simp [protection] at finalized
  · have slotZero : slot.val = 0 := by
      by_contra nonzero
      change (if slot.val = 0 then some object else none) = some source at stored
      rw [if_neg nonzero] at stored
      contradiction
    have sourceObject : source = object := by
      have storedParts : slot = ⟨0, by decide⟩ ∧ object = source := by
        simpa [page] using stored
      exact storedParts.2.symm
    subst source
    simp [object] at live

def allowed : Allowed page protection book command := by
  apply Allowed.compact (tombstonedAt := 6)
  · rfl
  · rfl
  · exact expired
  · exact unprotected

set_option maxRecDepth 10000 in
noncomputable def admission :
    QuotaGcSettlement.Admission manifest config limits page protection command accepted where
  currentEpoch := rfl
  preValid := page_valid
  allowed := by simpa [resourcePre_book] using allowed
  postValid := post_valid
  occupiedBound := by decide
  byteBound := by decide
  exactFunded := by intro lane; exact Nat.le_refl _
  operationFeeExact := by
    simpa only [resourceOperation_exact, Operation.feeDebit] using
      accepted_exact_fee.symm

noncomputable def grant : Grant where
  subject := context.subject
  domain := context.domain
  pageCell := ⟨910⟩
  commandDigest := QuotaGcSettlement.commandDigest
    CanonicalResourceKernel.materializer.rootBytes page command
  notBefore := 0
  notAfter := 20
  maxEpoch := 7
  maxOccupied := limits.maxOccupied
  maxPageBytes := limits.maxPageBytes
  maxCharge := limits.available

noncomputable def runtime : Runtime where
  transactionId := ⟨900⟩
  nullifierId := ⟨901⟩
  pageCell := ⟨910⟩
  resourceCell := ⟨911⟩
  authorityCell := ⟨912⟩
  protectionCell := ⟨913⟩
  clockCell := ⟨914⟩
  authorityRoot := CanonicalResourceKernel.materializer.rootBytes grant.canonicalBytes
  protectionRoot := CanonicalResourceKernel.materializer.rootBytes protection.canonicalBytes
  clockRoot := CanonicalResourceKernel.materializer.rootBytes (encodeNat command.height)
  pageResourceDistinct := by decide
  authorityPageDistinct := by decide
  authorityResourceDistinct := by decide
  protectionPageDistinct := by decide
  protectionResourceDistinct := by decide
  clockPageDistinct := by decide
  clockResourceDistinct := by decide

set_option maxRecDepth 10000 in
theorem scopeEvidenceWitness : ScopedAuthority
    CanonicalResourceKernel.materializer.rootBytes
    grant limits page command context
      (AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit) := by
  constructor
  · rfl
  · rfl
  · rfl
  · decide
  · decide
  · rfl
  · decide
  · rfl
  · rfl
  · intro lane; exact Nat.le_refl _
  · rw [accepted_exact_fee]
    change 3 <= exact .feeDebit
    rw [exact_fee]

noncomputable def plan : Plan CanonicalResourceKernel.materializer
    demoPortal demoState resourcePre 2 where
  config := config
  limits := limits
  page := page
  protection := protection
  command := command
  manifest := manifest
  context := context
  accepted := accepted
  authorization := authorization
  admission := admission
  runtime := runtime
  grant := grant
  scopeEvidence := scopeEvidenceWitness
  grantPage := rfl
  grantRootBound := rfl
  protectionRootBound := rfl
  clockRootBound := rfl

/-! ## Positive execution-facing facts -/

example : (command.apply page).slots ⟨0, by decide⟩ = none := by decide

example : (command.apply page).occupiedCount = 0 := by decide

example : plan.intent.writes.length = 2 := by rfl

example : plan.intent.readGuards.length = 3 := by rfl

example : plan.intent.exactCharge .feeDebit = 3 := by
  rw [Plan.intent_fee_exact]
  rfl

example (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes)
    (schedule : Schedule) :
    DurableDataIntent.execute schedule (DataSnapshot.install before plan.intent)
      plan.intent = .replayed plan.intent.erase :=
  plan.exact_retry_replays schedule before

example : Not (QuotaGcSettlement.Admission manifest config limits
    (command.apply page) protection command accepted) :=
  stale_epoch_has_no_admission admission

/-! ## The same identity becomes non-collectable when protected -/

def finalizedProtection : Protection where
  roots := []
  edges := []
  historyFinalized := [object.contentId]

example : Not (Allowed page finalizedProtection book command) := by
  exact finalized_content_cannot_compact (by simp [finalizedProtection])

def source : Object where
  contentId := 12
  owner := 1
  leaseId := 8
  payload := [40]
  status := .live

def referencedPage : Page 2 where
  epoch := 7
  slots := fun slot => if slot.val = 0 then some object else some source

def referencedProtection : Protection where
  roots := []
  edges := [(source.contentId, object.contentId)]
  historyFinalized := []

example : Not (Allowed referencedPage referencedProtection book command) := by
  apply live_reachable_content_cannot_compact
    (sourceSlot := ⟨1, by decide⟩) (source := source)
  · rfl
  · rfl
  · decide
  · exact .step
      (by simp [Protection.outgoing, referencedProtection, source, object])
      (.refl object.contentId)

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.QuotaGcSettlementWitness.admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admission
/-- info: 'Minidregg.Assurance.QuotaGcSettlementWitness.plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms plan

end Minidregg.Assurance.QuotaGcSettlementWitness
