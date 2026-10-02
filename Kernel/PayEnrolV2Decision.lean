/-
# Quote-bound paid-entry observation decision

This leaf does not submit, spend a nullifier, mint, or mutate authority. The
receiver loads the authority snapshot, verifies the observer/finalized-tip
boundary, obtains exact v2 Checked possession, and atomically commits the
selected effect. An unrelated signer cannot create a victim-owned claim.

Source pricing is recomputed from the observed amount. Stale authenticated
terms become immutable pending value; requested duration is never silently
changed. Pending-custody rotation is distinct from initial enrollment and never
causes this decision to replace the current custody row with the original key.
-/
import Kernel.PayObservation
import Kernel.PayEnrolPricing
import Compiler.PayEnrolSignatureV2IO
import Compiler.CredentialAuthorityDomain

namespace Minidregg.Kernel.PayEnrolV2Decision

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.CredentialAuthorityState (currentSigningKey signingKeyRevocation keyStanding)
open Minidregg.Theory.CredentialSigningKey (KeyRecord)
open Minidregg.Theory.Store (Store Patch)
open Minidregg.Theory.ResourceBirth (CreationTariff)
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff (Tariff)
open Minidregg.Kernel.PayObservation (Observation Credit decideObservation nullifierBytes)

set_option autoImplicit false

abbrev Memo := PayEnrolMemoV2.Memo
abbrev Unsigned := PayEnrolMemoV2.Unsigned
abbrev Owner := PayEnrolClaim.PendingOwner
abbrev FixedQuote := PayEnrolClaim.FixedQuote
abbrev Authority := CredentialAuthorityDomain.Snapshot

/-- The receiver computes birthFee with its actual factory descriptor. The
other inputs are the same loaded source inputs used by the public quote. -/
structure Pricing where
  domain : Digest
  /-- The exact original genesis seed identity, pinned by validateLoaded and preserved by carry. -/
  expectedSeed : Digest
  semantics : Digest
  creation : CreationTariff
  template : CanonicalRuntimeProfile.FactoryTemplate
  birthFee : Nat

/-- Exact observed asset/recipient, not client-supplied verifier context. -/
def observationContext (o : Observation) : PayEnrolMemoV2.Context :=
  ⟨o.mint, o.tokenProgram, o.address⟩

def stableSubject (value : Unsigned) : SubjectId :=
  ⟨PayEnrolMemo.subjectOf value.enrollmentIdentityKey⟩

def mode (value : Unsigned) : PayEnrolClaim.Mode :=
  match value.mode with
  | .enroll => .enroll
  | .renew | .renewWithoutCommitment => .renew

def initialIdentity (value : Unsigned) : Prop :=
  value.mode = .enroll ∧ value.authorizingKey = value.enrollmentIdentityKey ∧
    value.authorityEpoch = 1

instance (value : Unsigned) : Decidable (initialIdentity value) := by
  unfold initialIdentity; infer_instance

inductive Reject where
  | tariffInvalid | selfEnrolOff | notEnrolIndex | malformedMemo | memoMismatch
  | deploymentMismatch | authorityDomainMismatch | amountMismatch | malformedObservation
  | chainTipInvalid | observation (reason : PayObservation.Reject)
  | unrelatedSigner | subjectTaken | custodyConflict | malformedCustody
  | authorityUnavailable | sshKeyTaken | sshKeyMismatch
  deriving DecidableEq, Repr

inductive CustodySource where
  | fresh | pending | admitted
  deriving DecidableEq, Repr

/-- Current authority is not a pending-owner row: an admitted legacy key may
have no commitment. Carry the actual Option instead of inventing Some(0). -/
structure CurrentOwner where
  identityKey : List UInt8
  currentKey : List UInt8
  epoch : Nat
  nextKeyDigest : Option Digest
  deriving DecidableEq, Repr

def CurrentOwner.ofPending (owner : Owner) : CurrentOwner :=
  ⟨owner.identityKey, owner.currentKey, owner.epoch, some owner.nextKeyDigest⟩

def CurrentOwner.ofRegistry (identity : List UInt8) (key : KeyRecord) : CurrentOwner :=
  ⟨identity, key.publicKey, key.keyEpoch, key.nextKeyDigest⟩

def CurrentOwner.valid (owner : CurrentOwner) : Prop :=
  owner.identityKey.length = 32 ∧ owner.currentKey.length = 32 ∧
  0 < owner.epoch ∧ owner.epoch < 2 ^ 64 ∧
  (match owner.nextKeyDigest with | none => True | some next => next.value < 2 ^ 256)

instance (owner : CurrentOwner) : Decidable owner.valid := by
  unfold CurrentOwner.valid
  cases owner.nextKeyDigest <;> infer_instance

/-- Claim acceptance consumes no NEXT field. Keep exact optional state here
for signed mode binding, and project only authenticated acceptance authority. -/
def CurrentOwner.toClaimOwner (owner : CurrentOwner) : PayEnrolClaim.CurrentOwner :=
  ⟨owner.identityKey, owner.currentKey, owner.epoch⟩

theorem CurrentOwner.toClaimOwner_valid (owner : CurrentOwner) (valid : owner.valid) :
    owner.toClaimOwner.valid :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩

theorem pending_claim_projection (owner : Owner) :
    (CurrentOwner.ofPending owner).toClaimOwner = owner.toCurrentOwner := rfl

theorem registry_claim_projection (identity : List UInt8) (key : KeyRecord) :
    (CurrentOwner.ofRegistry identity key).toClaimOwner =
      (⟨identity, key.publicKey, key.keyEpoch⟩ : PayEnrolClaim.CurrentOwner) := rfl

/-- Exact optional-state binding: mode 3 is None and has canonical zero bytes;
modes 1/2 declare Some, including the legitimate Some(0) digest value. -/
def matchesNext (value : Unsigned) (actual : Option Digest) : Bool :=
  match value.mode with
  | .enroll | .renew => decide (actual = some value.nextKeyDigest)
  | .renewWithoutCommitment => decide (actual = none ∧ value.nextKeyDigest = ⟨0⟩)

/-- `stale` is a comparison result produced below, never an external signature
oracle. `owner` is current custody, even when the depositing signer is old. -/
structure Custody where
  owner : CurrentOwner
  source : CustodySource
  stale : Bool
  nextMatches : Bool
  deriving DecidableEq, Repr

/-- Only a fresh original identity may allocate custody. Existing rows are
preserved byte-for-byte, including after pre-rotation. -/
def Custody.allocation (custody : Custody) : Option Owner :=
  match custody.source, custody.owner.nextKeyDigest with
  | .fresh, some next => some ⟨custody.owner.identityKey, custody.owner.currentKey,
      custody.owner.epoch, next⟩
  | _, _ => none

def originalOwner (value : Unsigned) : Owner :=
  ⟨value.enrollmentIdentityKey, value.enrollmentIdentityKey, 1, value.nextKeyDigest⟩

/-- Pending custody history establishes a former signer's provenance, never
current authority. This also survives first admission at epoch > 1, whose
registry intentionally starts at the current key rather than inventing older
key rows. Every history row was installed by initial custody or its rotation. -/
def knownPendingSigner (store : PayStore) (value : Unsigned) : Bool :=
  match pendingOwnerHistoryAt store value.enrollmentIdentityKey value.authorityEpoch with
  | none => false
  | some owner => decide (owner.valid ∧
      owner.identityKey = value.enrollmentIdentityKey ∧
      owner.epoch = value.authorityEpoch ∧ owner.currentKey = value.authorizingKey) &&
      matchesNext value (some owner.nextKeyDigest)

/-- A known historical key can establish deposit provenance; it is not current
recovery authority. No match against a different subject or key is accepted. -/
def knownRegistrySigner (authority : Authority) (value : Unsigned) : Bool :=
  match authority.logical ⟨.subjectKey, (stableSubject value, value.authorityEpoch)⟩ with
  | none => false
  | some key => decide (
      key.subject = (stableSubject value).value ∧ key.keyEpoch = value.authorityEpoch ∧
      key.publicKey = value.authorizingKey ∧
      key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
      (authority.logical ⟨.registered, signingKeyRevocation key⟩).isSome = true)

def keyCurrent (authority : Authority) (value : Unsigned) (key : KeyRecord) : Bool :=
  decide (key.publicKey = value.authorizingKey ∧ key.keyEpoch = value.authorityEpoch ∧
    key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    keyStanding authority.cell (signingKeyRevocation key) = .live ∧
    key.activeFrom ≤ authority.revision ∧ authority.revision ≤ key.activeUntil)

/-- The registry wins after admission. A leftover pending row can never revive
old custody or authenticate an old key as current. -/
def resolveCustody (store : PayStore) (authority : Authority) (value : Unsigned) :
    Except Reject Custody :=
  match enrolmentAt store value.enrollmentIdentityKey with
  | some _ =>
      if knownRegistrySigner authority value || knownPendingSigner store value then
        match currentSigningKey authority.logical (stableSubject value) with
        | none => .error .authorityUnavailable
        | some key =>
            let owner := CurrentOwner.ofRegistry value.enrollmentIdentityKey key
            if owner.valid then .ok ⟨owner, .admitted, !(keyCurrent authority value key),
              matchesNext value key.nextKeyDigest⟩
            else .error .malformedCustody
      else .error .unrelatedSigner
  | none =>
      if (authority.logical ⟨.subjectKeyEpoch, stableSubject value⟩).isSome then
        .error .subjectTaken
      else
        match pendingOwnerAt store value.enrollmentIdentityKey with
        | none =>
            if initialIdentity value then
              let owner := originalOwner value
              if owner.valid then .ok ⟨CurrentOwner.ofPending owner, .fresh, false, true⟩
              else .error .malformedCustody
            else .error .unrelatedSigner
        | some owner =>
            if ¬owner.valid ∨ owner.identityKey ≠ value.enrollmentIdentityKey then
              .error .malformedCustody
            else if value.mode = .renewWithoutCommitment then .error .custodyConflict
            else if value.authorizingKey = owner.currentKey ∧ value.authorityEpoch = owner.epoch then
              if value.nextKeyDigest = owner.nextKeyDigest then
                .ok ⟨CurrentOwner.ofPending owner, .pending, false, true⟩
              else .error .custodyConflict
            else if knownPendingSigner store value then
              .ok ⟨CurrentOwner.ofPending owner, .pending, true,
                matchesNext value (some owner.nextKeyDigest)⟩
            else .error .unrelatedSigner

structure EnrolPlan where
  memo : Memo
  float : Nat
  quote : FixedQuote
  index : Option Nat
  leaseUntil : Nat
  origin : PayEnrolClaim.Claim
  consumption : PayEnrolClaim.Consumption
  deriving DecidableEq, Repr

structure RenewPlan where
  memo : Memo
  float : Nat
  account : Nat
  quote : FixedQuote
  before : EnrolRecord
  leaseFrom : Nat
  leaseUntil : Nat
  origin : PayEnrolClaim.Claim
  consumption : PayEnrolClaim.Consumption
  deriving DecidableEq, Repr

structure PendingPlan where
  claim : PayEnrolClaim.Claim
  /-- Allocate only on first pending deposit; no write replacing prior custody. -/
  ownerAllocation : Option Owner
  deriving DecidableEq, Repr

inductive Decision where
  | enrol (plan : EnrolPlan)
  | renew (plan : RenewPlan)
  | pending (plan : PendingPlan)
  | journal (reason : PayEnrolMemo.JournalReason)
  deriving DecidableEq, Repr

/-- Every authenticated economic event has this immutable source record.
None tags direct quoted admission; a pending reason is retained forever. -/
def originClaim (o : Observation) (memo : Memo)
    (reason : Option PayEnrolClaim.PendingReason) : PayEnrolClaim.Claim :=
  { original := ⟨o.signature, o.address, o.slot, o.amount, o.mint, o.tokenProgram, o.index⟩
    rawMemo := PayEnrolMemoV2.encode memo
    ownerIdentityKey := memo.unsigned.enrollmentIdentityKey
    reason := reason
    originalPricingCommitment := memo.unsigned.pricingCommitment }

/-- Pure projection of the actual original signed memo. No nonce, acceptance
command or detached possession signature is synthesized. The PayCell law uses
these same seven fields when checking originalMemo consumption coherence. -/
def termsOfMemo (claimId : List UInt8) (memo : Memo) : PayEnrolClaim.Terms :=
  ⟨mode memo.unsigned, claimId, memo.unsigned.enrollmentIdentityKey,
    memo.unsigned.pricingCommitment, memo.unsigned.weeks,
    memo.unsigned.minimumStarterCredit, memo.unsigned.expiresAtProcessingChainHour⟩

def originalConsumption (o : Observation) (memo : Memo) (tariff : Tariff)
    (quote : FixedQuote) : PayEnrolClaim.Consumption :=
  { authorization := .originalMemo
    terms := termsOfMemo (nullifierBytes o) memo
    originalAmountAtomic := o.amount
    tariff := tariff
    mintedCredit := quote.credit
    birthFee := quote.birthFee
    membershipCredit := quote.membershipCredit
    creditedRemainder := quote.creditedRemainder }

/-- Pending value has an origin but no consumption and therefore no mint. -/
def pendingPlan (o : Observation) (memo : Memo) (custody : Custody)
    (reason : PayEnrolClaim.PendingReason) : PendingPlan :=
  { claim := originClaim o memo (some reason)
    ownerAllocation := custody.allocation }

def enrolPlan (store : PayStore) (tariff : Tariff) (tip : ChainTip) (o : Observation)
    (memo : Memo) (float : Nat) (quote : FixedQuote) : EnrolPlan :=
  ⟨memo, float, quote,
    if nextFree store < bookSize store then some (nextFree store) else none,
    tip.hour + 168 * memo.unsigned.weeks, originClaim o memo none,
    originalConsumption o memo tariff quote⟩

def renewPlan (tariff : Tariff) (tip : ChainTip) (o : Observation) (memo : Memo)
    (float : Nat) (record : EnrolRecord) (quote : FixedQuote) : RenewPlan :=
  let start := max tip.hour record.leaseUntil
  ⟨memo, float, record.account, quote, record, start, start + 168 * memo.unsigned.weeks,
    originClaim o memo none, originalConsumption o memo tariff quote⟩

/-- Pricing after possession/identity has been established. An observation under
changed terms or mode is pending, never silently priced as another purchase.
A changed journal floor is likewise a term change for this already-paid value. -/
def classifyTerms (store : PayStore) (pricing : Pricing) (tariff : Tariff)
    (tip : ChainTip) (o : Observation) (memo : Memo) (custody : Custody) (float : Nat) : Decision :=
  let pending := fun reason => Decision.pending (pendingPlan o memo custody reason)
  if custody.stale then pending .authStale
  else if memo.unsigned.expiresAtProcessingChainHour < tip.hour then pending .expired
  else if !custody.nextMatches then pending .termsStale
  else
    let record := enrolmentAt store memo.unsigned.enrollmentIdentityKey
    let currentMode : PayEnrolClaim.Mode := if record.isSome then .renew else .enroll
    if mode memo.unsigned ≠ currentMode then pending .termsStale
    else if o.amount < tariff.journalFloor then pending .termsStale
    else
      let birth := if record.isSome then 0 else pricing.birthFee
      match PayEnrolClaim.quoteFixed o.amount tariff birth memo.unsigned.weeks
          memo.unsigned.minimumStarterCredit with
      | .error _ => pending .termsStale
      | .ok quote =>
          if memo.unsigned.pricingCommitment ≠ PayEnrolPricing.pricingCommitment
              pricing.semantics tariff pricing.creation pricing.template currentMode quote then
            pending .termsStale
          else
            match record with
            | none => .enrol (enrolPlan store tariff tip o memo float quote)
            | some before => .renew (renewPlan tariff tip o memo float before quote)

/-- `Checked` is tied to THIS memo and THIS observed asset/recipient. Its private
constructor prevents a caller from substituting a guessed signature boolean. -/
def decide (store : PayStore) (authority : Authority) (pricing : Pricing)
    (tip : ChainTip) (o : Observation) (memo : Memo)
    (checked : PayEnrolSignatureV2IO.Checked (observationContext o) memo) :
    Except Reject Decision :=
  if ¬memo.WellFormed then .error .malformedMemo
  else if o.memo ≠ .present (PayEnrolMemoV2.encode memo) then .error .memoMismatch
  else if authority.domain ≠ pricing.domain then .error .authorityDomainMismatch
  else if ¬PayChainTip.advances (chainTipOf store) tip then .error .chainTipInvalid
  else
    match tariffOf store with
    | none => .error .tariffInvalid
    | some tariff =>
        if ¬tariff.valid then .error .tariffInvalid
        else if tariff.enrolIndex = none then .error .selfEnrolOff
        else if tariff.enrolIndex ≠ some o.index then .error .notEnrolIndex
        else
          match decideObservation store tariff tip o with
          | .error reason => .error (.observation reason)
          | .ok credit =>
              let original : PayEnrolClaim.Observation :=
                ⟨o.signature, o.address, o.slot, o.amount, o.mint, o.tokenProgram, o.index⟩
              if ¬original.valid then .error .malformedObservation
              else if o.amount ≠ memo.unsigned.amountAtomic then .error .amountMismatch
              else if memo.unsigned.deploymentCommitment ≠ PayEnrolPricing.deploymentCommitment
                  pricing.domain pricing.expectedSeed tariff o.address then .error .deploymentMismatch
              else if !checked.mini then .ok (.journal .miniSigInvalid)
              else if !checked.ssh then .ok (.journal .sshSigInvalid)
              else
                match resolveCustody store authority memo.unsigned with
                | .error reason => .error reason
                | .ok custody =>
                    let blob := PayEnrolMemo.sshBlobOf memo.unsigned.sshKey
                    match enrolmentAt store memo.unsigned.enrollmentIdentityKey with
                    | some record =>
                        if record.sshBlob ≠ blob then .error .sshKeyMismatch
                        else .ok (classifyTerms store pricing tariff tip o memo custody credit.payer)
                    | none =>
                        if (sshIndexAt store blob).isSome then .error .sshKeyTaken
                        else .ok (classifyTerms store pricing tariff tip o memo custody credit.payer)

/-! ## The exact pay-cell effects; authority and Book effects stay in receiver -/

def PendingPlan.patch (plan : PendingPlan) : Patch PayCell.layout :=
  [.allocate .claim plan.claim.id plan.claim] ++
    match plan.ownerAllocation with
    | none => []
    | some owner => [.allocate .pendingOwner owner.identityKey owner,
        .allocate .pendingOwnerHistory (owner.identityKey, owner.epoch) owner]

/-- The origin and consumption are in the same pay-cell patch as admission.
The durable receiver commits this WITH the one Book/birth effect, atomically. -/
def EnrolPlan.patch (plan : EnrolPlan) (account slot : Nat) : Patch PayCell.layout :=
  [.allocate .claim plan.origin.id plan.origin,
   .allocate .claimConsumption plan.origin.id plan.consumption,
   .allocate .enrolment plan.memo.unsigned.enrollmentIdentityKey
    ⟨PayEnrolMemo.sshBlobOf plan.memo.unsigned.sshKey, account, plan.index, plan.leaseUntil, slot⟩,
   .allocate .sshIndex (PayEnrolMemo.sshBlobOf plan.memo.unsigned.sshKey)
     plan.memo.unsigned.enrollmentIdentityKey] ++
   match plan.index with | none => [] | some index => [.allocate .assignment index account]

/-- Renewal changes only the paid lease, never keys, next-key commitments,
grants, or the stable identity that names the record. -/
def RenewPlan.patch (plan : RenewPlan) : Patch PayCell.layout :=
  [.allocate .claim plan.origin.id plan.origin,
   .allocate .claimConsumption plan.origin.id plan.consumption,
   .write .enrolment plan.memo.unsigned.enrollmentIdentityKey plan.before
    { plan.before with leaseUntil := plan.leaseUntil }]

def Decision.origin : Decision → Option PayEnrolClaim.Claim
  | .enrol plan => some plan.origin
  | .renew plan => some plan.origin
  | .pending plan => some plan.claim
  | .journal _ => none

def Decision.consumption : Decision → Option PayEnrolClaim.Consumption
  | .enrol plan => some plan.consumption
  | .renew plan => some plan.consumption
  | .pending _ | .journal _ => none

def Decision.mintedCredit : Decision → Nat
  | .enrol plan => plan.quote.credit
  | .renew plan => plan.quote.credit
  | .pending _ | .journal _ => 0

def Decision.quote : Decision → Option FixedQuote
  | .enrol plan => some plan.quote
  | .renew plan => some plan.quote
  | .pending _ | .journal _ => none

/-! ## Source obligations useful to the durable receiver -/

theorem original_consumption_matches_origin (o : Observation) (memo : Memo)
    (tariff : Tariff) (quote : FixedQuote) :
    (originalConsumption o memo tariff quote).matchesClaim (originClaim o memo none) :=
  ⟨rfl, rfl, rfl⟩

theorem original_authorization_is_the_memo (o : Observation) (memo : Memo)
    (tariff : Tariff) (quote : FixedQuote) :
    (originalConsumption o memo tariff quote).authorization = .originalMemo ∧
    (originClaim o memo none).reason = none ∧
    (originalConsumption o memo tariff quote).terms = termsOfMemo (nullifierBytes o) memo :=
  ⟨rfl, rfl, rfl⟩

theorem pending_retains_reason (o : Observation) (memo : Memo) (custody : Custody)
    (reason : PayEnrolClaim.PendingReason) :
    (pendingPlan o memo custody reason).claim.reason = some reason := rfl

theorem pending_has_no_consumption (plan : PendingPlan) :
    (Decision.pending plan).consumption = none := rfl

theorem pending_mints_zero (plan : PendingPlan) :
    (Decision.pending plan).mintedCredit = 0 := rfl

theorem pending_exact_provenance (o : Observation) (memo : Memo) (custody : Custody)
    (reason : PayEnrolClaim.PendingReason) :
    (pendingPlan o memo custody reason).claim.original.amountAtomic = o.amount ∧
    (pendingPlan o memo custody reason).claim.rawMemo = PayEnrolMemoV2.encode memo ∧
    (pendingPlan o memo custody reason).claim.ownerIdentityKey = memo.unsigned.enrollmentIdentityKey ∧
    (pendingPlan o memo custody reason).claim.originalPricingCommitment =
      memo.unsigned.pricingCommitment ∧
    (pendingPlan o memo custody reason).claim.id = nullifierBytes o := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem pending_existing_custody_unchanged (o : Observation) (memo : Memo) (custody : Custody)
    (reason : PayEnrolClaim.PendingReason) (existing : custody.source ≠ .fresh) :
    (pendingPlan o memo custody reason).ownerAllocation = none := by
  cases source : custody.source <;> simp_all [pendingPlan, Custody.allocation]

theorem initial_owner_exact (value : Unsigned) :
    (originalOwner value).identityKey = value.enrollmentIdentityKey ∧
    (originalOwner value).currentKey = value.enrollmentIdentityKey ∧
    (originalOwner value).epoch = 1 ∧
    (originalOwner value).nextKeyDigest = value.nextKeyDigest := ⟨rfl, rfl, rfl, rfl⟩

theorem stale_authority_is_pending (store : PayStore) (pricing : Pricing) (tariff : Tariff)
    (tip : ChainTip) (o : Observation) (memo : Memo) (custody : Custody) (float : Nat)
    (stale : custody.stale = true) :
    classifyTerms store pricing tariff tip o memo custody float =
      .pending (pendingPlan o memo custody .authStale) := by
  simp [classifyTerms, stale]

theorem expired_is_pending (store : PayStore) (pricing : Pricing) (tariff : Tariff)
    (tip : ChainTip) (o : Observation) (memo : Memo) (custody : Custody) (float : Nat)
    (current : custody.stale = false) (expired : memo.unsigned.expiresAtProcessingChainHour < tip.hour) :
    classifyTerms store pricing tariff tip o memo custody float =
      .pending (pendingPlan o memo custody .expired) := by
  simp [classifyTerms, current, expired]

/-- Successful pricing uses exactly requested duration and leaves every other
credit spendable; this is the shared fixed-deposit theorem, not a v1 quotient. -/
theorem fixed_quote_partition (amount : Nat) (tariff : Tariff)
    (birth weeks starter : Nat) (quote : FixedQuote)
    (quoted : PayEnrolClaim.quoteFixed amount tariff birth weeks starter = .ok quote) :
    quote.requestedWeeks = weeks ∧
    quote.birthFee + quote.membershipCredit + quote.creditedRemainder = quote.credit ∧
    starter ≤ quote.creditedRemainder := by
  have split := PayEnrolClaim.quoteFixed_success_split amount tariff birth weeks starter quote quoted
  exact ⟨split.2.2.2.1, split.2.2.2.2.2.1, split.2.2.2.2.2.2⟩

/-- No registry key from an unrelated identity is admitted as a historical
signer merely because it verified a signature over a victim-naming memo. -/
theorem admitted_unknown_signer_refused (store : PayStore) (authority : Authority)
    (value : Unsigned) (record : EnrolRecord)
    (enrolled : enrolmentAt store value.enrollmentIdentityKey = some record)
    (unknown : knownRegistrySigner authority value = false)
    (unknownPending : knownPendingSigner store value = false) :
    resolveCustody store authority value = .error .unrelatedSigner := by
  simp [resolveCustody, enrolled, unknown, unknownPending]

/-- Any credit-bearing output of the ACTUAL classifier is backed by a
successful fixed-deposit source quote. Pending branches cannot satisfy this. -/
theorem classifyTerms_success_quote (store : PayStore) (pricing : Pricing) (tariff : Tariff)
    (tip : ChainTip) (o : Observation) (memo : Memo) (custody : Custody) (float : Nat)
    (quote : FixedQuote)
    (accepted : (classifyTerms store pricing tariff tip o memo custody float).quote = some quote) :
    ∃ birth, PayEnrolClaim.quoteFixed o.amount tariff birth memo.unsigned.weeks
      memo.unsigned.minimumStarterCredit = .ok quote := by
  unfold classifyTerms at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  next actual quoted =>
    split at accepted
    · cases accepted
    split at accepted
    · simp only [Decision.quote, enrolPlan, Option.some.injEq] at accepted
      subst quote
      exact ⟨_, quoted⟩
    · simp only [Decision.quote, renewPlan, Option.some.injEq] at accepted
      subst quote
      exact ⟨_, quoted⟩

theorem classifyTerms_success_partition (store : PayStore) (pricing : Pricing) (tariff : Tariff)
    (tip : ChainTip) (o : Observation) (memo : Memo) (custody : Custody) (float : Nat)
    (quote : FixedQuote)
    (accepted : (classifyTerms store pricing tariff tip o memo custody float).quote = some quote) :
    quote.amountAtomic = o.amount ∧ quote.credit = tariff.creditFor o.amount ∧
    quote.requestedWeeks = memo.unsigned.weeks ∧
    quote.birthFee + quote.membershipCredit + quote.creditedRemainder = quote.credit ∧
    memo.unsigned.minimumStarterCredit ≤ quote.creditedRemainder := by
  obtain ⟨birth, quoted⟩ := classifyTerms_success_quote store pricing tariff tip o memo custody float quote accepted
  have split := PayEnrolClaim.quoteFixed_success_split o.amount tariff birth memo.unsigned.weeks
    memo.unsigned.minimumStarterCredit quote quoted
  exact ⟨split.1, split.2.1, split.2.2.2.1, split.2.2.2.2.2.1, split.2.2.2.2.2.2⟩

/-! ## Explicit unprerotated renewal, with no invented custody commitment -/

theorem unprerotated_is_economic_renewal :
    mode PayEnrolMemoV2.unprerotatedRenewal.unsigned = .renew := rfl

theorem unprerotated_matches_only_none (value : Unsigned)
    (unprerotated : value.mode = .renewWithoutCommitment) (actual : Option Digest) :
    matchesNext value actual = true ↔ actual = none ∧ value.nextKeyDigest = ⟨0⟩ := by
  simp [matchesNext, unprerotated]

theorem committed_matches_only_some (value : Unsigned)
    (committed : value.mode = .renew) (actual : Option Digest) :
    matchesNext value actual = true ↔ actual = some value.nextKeyDigest := by
  simp [matchesNext, committed]

theorem none_and_some_zero_are_distinct :
    matchesNext PayEnrolMemoV2.unprerotatedRenewal.unsigned none = true ∧
    matchesNext PayEnrolMemoV2.unprerotatedRenewal.unsigned (some ⟨0⟩) = false ∧
    matchesNext PayEnrolMemoV2.zeroCommittedRenewal.unsigned none = false ∧
    matchesNext PayEnrolMemoV2.zeroCommittedRenewal.unsigned (some ⟨0⟩) = true := by decide

theorem registry_owner_preserves_optional_next (identity : List UInt8) (key : KeyRecord) :
    (CurrentOwner.ofRegistry identity key).nextKeyDigest = key.nextKeyDigest := rfl

theorem pending_owner_always_has_commitment (owner : Owner) :
    (CurrentOwner.ofPending owner).nextKeyDigest = some owner.nextKeyDigest := rfl

theorem admitted_custody_never_allocates (owner : CurrentOwner) (stale nextMatches : Bool) :
    (Custody.mk owner .admitted stale nextMatches).allocation = none := by
  simp [Custody.allocation]

/-- A valid known v1 key with None now resolves to CURRENT registry custody;
no pending-owner fallback and no manufactured commitment is involved. -/
theorem legacy_registry_custody_resolves (store : PayStore) (authority : Authority)
    (value : Unsigned) (record : EnrolRecord) (key : KeyRecord)
    (enrolled : enrolmentAt store value.enrollmentIdentityKey = some record)
    (known : knownRegistrySigner authority value = true)
    (selected : currentSigningKey authority.logical (stableSubject value) = some key)
    (valid : (CurrentOwner.ofRegistry value.enrollmentIdentityKey key).valid)
    (unprerotated : value.mode = .renewWithoutCommitment)
    (zero : value.nextKeyDigest = ⟨0⟩) (none : key.nextKeyDigest = none) :
    resolveCustody store authority value =
      .ok ⟨CurrentOwner.ofRegistry value.enrollmentIdentityKey key, .admitted,
        !(keyCurrent authority value key), true⟩ := by
  simp [resolveCustody, enrolled, known, selected, valid, matchesNext,
    unprerotated, zero, none]

#assert_axioms original_consumption_matches_origin
#assert_axioms original_authorization_is_the_memo
#assert_axioms pending_retains_reason
#assert_axioms pending_has_no_consumption
#assert_axioms CurrentOwner.toClaimOwner_valid
#assert_axioms pending_claim_projection
#assert_axioms registry_claim_projection
#assert_axioms unprerotated_is_economic_renewal
#assert_axioms unprerotated_matches_only_none
#assert_axioms committed_matches_only_some
#assert_axioms none_and_some_zero_are_distinct
#assert_axioms registry_owner_preserves_optional_next
#assert_axioms pending_owner_always_has_commitment
#assert_axioms admitted_custody_never_allocates
#assert_axioms legacy_registry_custody_resolves
#assert_axioms classifyTerms_success_quote
#assert_axioms classifyTerms_success_partition
#assert_axioms pending_mints_zero
#assert_axioms pending_exact_provenance
#assert_axioms pending_existing_custody_unchanged
#assert_axioms initial_owner_exact
#assert_axioms stale_authority_is_pending
#assert_axioms expired_is_pending
#assert_axioms fixed_quote_partition
#assert_axioms admitted_unknown_signer_refused

end Minidregg.Kernel.PayEnrolV2Decision
