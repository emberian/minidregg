/-
Exact paid-membership and payment status, without a journal scan.

The Host supplies a law-checked PayStore and authenticated deployment Clock.
The exact locator is signature plus original recipient, not a guessed current
deposit address. The source reads only enrollment, chain evidence, origin,
consumption and v1-negative journal at those exact keys. Replay/nullifier
markers never imply success. V1 successful payments were not indexed, so an
absent origin/journal cannot distinguish unobserved from a positive v1 payment.

This projection grants nothing and remains useful when chain evidence is stale
or the membership lease has expired. New quotes/acceptance separately require
fresh evidence. Summaries omit signatures of acceptance, raw memo and tariff.
-/
import Kernel.PayChainTip

namespace Minidregg.Kernel.PayClaimStatus

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

structure Locator where
  signature : List UInt8
  originalRecipient : List UInt8
  deriving DecidableEq, Repr

def locatorStream : StreamCodec Locator :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream bytesStream)
    (fun value => (value.signature, value.originalRecipient))
    (fun (signature, originalRecipient) => ⟨signature, originalRecipient⟩)
    (by intro value; cases value; rfl)

structure Request where
  identityKey : List UInt8
  payment : Option Locator
  deriving DecidableEq, Repr

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.option locatorStream))
    (fun value => (value.identityKey, value.payment))
    (fun (identityKey, payment) => ⟨identityKey, payment⟩)
    (by intro value; cases value; rfl)

def Locator.id (locator : Locator) : List UInt8 :=
  PayEnrolClaim.soltxPrefix ++ locator.signature ++ locator.originalRecipient

def Request.valid (request : Request) : Prop :=
  request.identityKey.length = 32 ∧ match request.payment with
    | none => True
    | some locator => locator.signature.length = 64 ∧ locator.originalRecipient.length = 32

instance (request : Request) : Decidable request.valid := by
  unfold Request.valid
  cases request.payment <;> infer_instance

def requestFrame : List UInt8 := "DREGG/PAY/CLAIM-STATUS/REQUEST/v1".toUTF8.toList
def requestCodec : LawfulCodec Request := framed requestFrame requestStream

inductive LeaseState where
  | active
  | expired
  | notEnrolled
  deriving DecidableEq, Repr

def LeaseState.code : LeaseState → Nat
  | .active => 0
  | .expired => 1
  | .notEnrolled => 2

def LeaseState.ofCode : Nat → Option LeaseState
  | 0 => some .active
  | 1 => some .expired
  | 2 => some .notEnrolled
  | _ => none

theorem LeaseState.ofCode_code (value : LeaseState) :
    LeaseState.ofCode value.code = some value := by cases value <;> rfl

def leaseStateStream : StreamCodec LeaseState where
  encode value := StreamCodec.nat.encode value.code
  decodePrefix bytes := do
    let (code, suffix) ← StreamCodec.nat.decodePrefix bytes
    let value ← LeaseState.ofCode code
    some (value, suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [StreamCodec.nat.decodePrefix_encode, LeaseState.ofCode_code]

structure Entry where
  subject : Nat
  account : Nat
  sshBlob : List UInt8
  index : Option Nat
  leaseUntil : Nat
  enrolledSlot : Nat
  deriving DecidableEq, Repr

def entryStream : StreamCodec Entry :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.option StreamCodec.nat) (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
    (fun value => (value.subject, value.account, value.sshBlob, value.index, value.leaseUntil, value.enrolledSlot))
    (fun (subject, account, sshBlob, index, leaseUntil, enrolledSlot) => ⟨subject, account, sshBlob, index, leaseUntil, enrolledSlot⟩)
    (by intro value; cases value; rfl)

structure Pending where
  amountAtomic : Nat
  slot : Nat
  index : Nat
  reason : PayEnrolClaim.PendingReason
  deriving DecidableEq, Repr

def pendingStream : StreamCodec Pending :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat PayEnrolClaim.pendingReasonStream)))
    (fun value => (value.amountAtomic, value.slot, value.index, value.reason))
    (fun (amountAtomic, slot, index, reason) => ⟨amountAtomic, slot, index, reason⟩)
    (by intro value; cases value; rfl)

inductive AuthorizationKind where
  | originalMemo
  | acceptCurrentQuote
  deriving DecidableEq, Repr

def AuthorizationKind.code : AuthorizationKind → Nat
  | .originalMemo => 0
  | .acceptCurrentQuote => 1

def AuthorizationKind.ofCode : Nat → Option AuthorizationKind
  | 0 => some .originalMemo
  | 1 => some .acceptCurrentQuote
  | _ => none

theorem AuthorizationKind.ofCode_code (value : AuthorizationKind) :
    AuthorizationKind.ofCode value.code = some value := by cases value <;> rfl

def authorizationKindStream : StreamCodec AuthorizationKind where
  encode value := StreamCodec.nat.encode value.code
  decodePrefix bytes := do
    let (code, suffix) ← StreamCodec.nat.decodePrefix bytes
    let value ← AuthorizationKind.ofCode code
    some (value, suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [StreamCodec.nat.decodePrefix_encode, AuthorizationKind.ofCode_code]

structure Consumed where
  amountAtomic : Nat
  slot : Nat
  index : Nat
  mode : PayEnrolClaim.Mode
  requestedWeeks : Nat
  mintedCredit : Nat
  birthFee : Nat
  membershipCredit : Nat
  creditedRemainder : Nat
  pricingCommitment : Digest
  authorization : AuthorizationKind
  deriving DecidableEq, Repr

def consumedStream : StreamCodec Consumed :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product PayEnrolClaim.modeStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream authorizationKindStream))))))))))
    (fun value => (value.amountAtomic, value.slot, value.index, value.mode, value.requestedWeeks, value.mintedCredit, value.birthFee, value.membershipCredit, value.creditedRemainder, value.pricingCommitment, value.authorization))
    (fun (amountAtomic, slot, index, mode, requestedWeeks, mintedCredit, birthFee, membershipCredit, creditedRemainder, pricingCommitment, authorization) => ⟨amountAtomic, slot, index, mode, requestedWeeks, mintedCredit, birthFee, membershipCredit, creditedRemainder, pricingCommitment, authorization⟩)
    (by intro value; cases value; rfl)

structure NegativeV1 where
  amountAtomic : Nat
  slot : Nat
  index : Nat
  reason : PayEnrolMemo.JournalReason
  deriving DecidableEq, Repr

def negativeV1Stream : StreamCodec NegativeV1 :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat PayEnrolMemo.journalReasonStream)))
    (fun value => (value.amountAtomic, value.slot, value.index, value.reason))
    (fun (amountAtomic, slot, index, reason) => ⟨amountAtomic, slot, index, reason⟩)
    (by intro value; cases value; rfl)

inductive Payment where
  | notRequested
  | unobservedOrUnknownPositiveV1
  | pendingV2 (summary : Pending)
  | consumedV2 (summary : Consumed)
  | journalV1Negative (summary : NegativeV1)
  deriving DecidableEq, Repr

def paymentStream : StreamCodec Payment :=
  StreamCodec.xmap
    (StreamCodec.sum unitStream (StreamCodec.sum unitStream
      (StreamCodec.sum pendingStream (StreamCodec.sum consumedStream negativeV1Stream))))
    (fun
      | .notRequested => .inl ()
      | .unobservedOrUnknownPositiveV1 => .inr (.inl ())
      | .pendingV2 value => .inr (.inr (.inl value))
      | .consumedV2 value => .inr (.inr (.inr (.inl value)))
      | .journalV1Negative value => .inr (.inr (.inr (.inr value))))
    (fun
      | .inl _ => .notRequested
      | .inr (.inl _) => .unobservedOrUnknownPositiveV1
      | .inr (.inr (.inl value)) => .pendingV2 value
      | .inr (.inr (.inr (.inl value))) => .consumedV2 value
      | .inr (.inr (.inr (.inr value))) => .journalV1Negative value)
    (by intro value; cases value <;> rfl)

/-- Absence means fresh, otherwise this is the source freshness refusal.
Status itself does not refuse on this diagnostic. -/
def freshnessStream : StreamCodec PayChainTip.FreshnessReject :=
  StreamCodec.xmap
    (StreamCodec.sum unitStream (StreamCodec.sum unitStream (StreamCodec.sum unitStream unitStream)))
    (fun
      | .missing => .inl ()
      | .malformed => .inr (.inl ())
      | .future => .inr (.inr (.inl ()))
      | .stale => .inr (.inr (.inr ())))
    (fun
      | .inl _ => .missing
      | .inr (.inl _) => .malformed
      | .inr (.inr (.inl _)) => .future
      | .inr (.inr (.inr _)) => .stale)
    (by intro value; cases value <;> rfl)

structure Response where
  request : Request
  clockHour : Nat
  asOfChainTip : Option ChainTip
  freshness : Option PayChainTip.FreshnessReject
  leaseState : LeaseState
  entry : Option Entry
  payment : Payment
  deriving DecidableEq, Repr

def responseStream : StreamCodec Response :=
  StreamCodec.xmap
    (StreamCodec.product requestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.option chainTipStream) (StreamCodec.product (StreamCodec.option freshnessStream) (StreamCodec.product leaseStateStream (StreamCodec.product (StreamCodec.option entryStream) paymentStream))))))
    (fun value => (value.request, value.clockHour, value.asOfChainTip, value.freshness, value.leaseState, value.entry, value.payment))
    (fun (request, clockHour, asOfChainTip, freshness, leaseState, entry, payment) => ⟨request, clockHour, asOfChainTip, freshness, leaseState, entry, payment⟩)
    (by intro value; cases value; rfl)

def responseFrame : List UInt8 := "DREGG/PAY/CLAIM-STATUS/RESPONSE/v1".toUTF8.toList
def responseCodec : LawfulCodec Response := framed responseFrame responseStream

inductive Reject where
  | malformedRequest
  | identityMismatch
  | inconsistentIndex
  | responseTooLarge
  deriving DecidableEq, Repr

def maxRequestBytes : Nat := 256
def maxResponseBytes : Nat := 8192

/-- Decode only the fixed bounded request; no unpaired signature/recipient. -/
def decodeRequest (bytes : List UInt8) : Except Reject Request :=
  if maxRequestBytes < bytes.length then .error .malformedRequest
  else match requestCodec.decode bytes with
    | none => .error .malformedRequest
    | some request =>
      if request.valid then .ok request else .error .malformedRequest

def leaseState (hour : Nat) : Option EnrolRecord → LeaseState
  | none => .notEnrolled
  | some record => if hour < record.leaseUntil then .active else .expired

def entryOf (identity : List UInt8) (record : EnrolRecord) : Entry :=
  ⟨PayEnrolMemo.subjectOf identity, record.account, record.sshBlob, record.index,
    record.leaseUntil, record.enrolledSlot⟩

def consumedOf (claim : PayEnrolClaim.Claim) (consumed : PayEnrolClaim.Consumption) : Consumed :=
  ⟨claim.original.amountAtomic, claim.original.slot, claim.original.index,
    consumed.terms.mode, consumed.terms.requestedWeeks, consumed.mintedCredit,
    consumed.birthFee, consumed.membershipCredit, consumed.creditedRemainder,
    consumed.pricingCommitment,
    match consumed.authorization with
      | .originalMemo => .originalMemo
      | .acceptCurrentQuote _ => .acceptCurrentQuote⟩

/-- Exact reads only. A v1 negative row identifies this payment locator, but
cannot prove which identity an invalid/missing memo intended to enroll.
A positive v1 payment has no success index: never infer one from enrollment. -/
def paymentAt (store : PayStore) (identity : List UInt8) (locator : Locator) : Except Reject Payment :=
  let id := locator.id
  match claimAt store id, claimConsumptionAt store id, journalAt store id with
  | none, none, none => .ok .unobservedOrUnknownPositiveV1
  | none, none, some negative =>
      .ok (.journalV1Negative ⟨negative.amount, negative.slot, negative.index, negative.reason⟩)
  | some origin, consumed, none =>
    if origin.id ≠ id then .error .inconsistentIndex
    else if origin.ownerIdentityKey ≠ identity then .error .identityMismatch
    else match consumed with
      | none =>
        match origin.reason with
        | none => .error .inconsistentIndex
        | some reason =>
          .ok (.pendingV2 ⟨origin.original.amountAtomic, origin.original.slot, origin.original.index, reason⟩)
      | some consumed =>
        if consumed.matchesClaim origin then .ok (.consumedV2 (consumedOf origin consumed))
        else .error .inconsistentIndex
  | _, _, _ => .error .inconsistentIndex

/-- This leaf projects exact stored outcomes even when later quote freshness
would refuse. Missing paid rows mean notEnrolled, including key-only members. -/
def project (store : PayStore) (clock : ClockCell.Clock) (request : Request) : Except Reject Response := do
  if ¬request.valid then throw .malformedRequest
  let payment ← match request.payment with
    | none => .ok .notRequested
    | some locator => paymentAt store request.identityKey locator
  let record := enrolmentAt store request.identityKey
  let tip := chainTipOf store
  let freshness := match PayChainTip.fresh clock tip with
    | .ok _ => none
    | .error reason => some reason
  pure ⟨request, hourOf clock.now, tip, freshness, leaseState (hourOf clock.now) record,
    record.map (entryOf request.identityKey), payment⟩

/-- Bound every variable-size summary component before serializing; the raw
memo and full tariff never enter a response. Refuse overflow, never truncate. -/
def Response.small (response : Response) : Prop :=
  response.request.valid ∧ response.clockHour < 2 ^ 256 ∧
  (match response.asOfChainTip with
    | none => True
    | some tip => tip.slot < 2 ^ 256 ∧ tip.blockTime < 2 ^ 256) ∧
  (match response.entry with
    | none => True
    | some entry => entry.subject < 2 ^ 256 ∧ entry.account < 2 ^ 256 ∧
        entry.sshBlob.length ≤ 51 ∧ (entry.index.getD 0) < 2 ^ 256 ∧
        entry.leaseUntil < 2 ^ 256 ∧ entry.enrolledSlot < 2 ^ 256) ∧
  (match response.payment with
    | .notRequested | .unobservedOrUnknownPositiveV1 => True
    | .pendingV2 row => row.amountAtomic < 2 ^ 256 ∧ row.slot < 2 ^ 256 ∧ row.index < 2 ^ 256
    | .journalV1Negative row => row.amountAtomic < 2 ^ 256 ∧ row.slot < 2 ^ 256 ∧ row.index < 2 ^ 256
    | .consumedV2 row => row.amountAtomic < 2 ^ 256 ∧ row.slot < 2 ^ 256 ∧ row.index < 2 ^ 256 ∧
        row.requestedWeeks < 2 ^ 256 ∧ row.mintedCredit < 2 ^ 256 ∧ row.birthFee < 2 ^ 256 ∧
        row.membershipCredit < 2 ^ 256 ∧ row.creditedRemainder < 2 ^ 256 ∧
        row.pricingCommitment.value < 2 ^ 256)

instance (response : Response) : Decidable response.small := by
  unfold Response.small
  cases response.asOfChainTip <;> cases response.entry <;> cases response.payment <;> infer_instance

def encodeResponse (response : Response) : Except Reject (List UInt8) :=
  if ¬response.small then .error .responseTooLarge
  else
    let bytes := responseCodec.encode response
    if bytes.length ≤ maxResponseBytes then .ok bytes else .error .responseTooLarge

def serve (store : PayStore) (clock : ClockCell.Clock) (bytes : List UInt8) :
    Except Reject (List UInt8) := do
  let request ← decodeRequest bytes
  let response ← project store clock request
  encodeResponse response

theorem request_roundtrip (request : Request) :
    requestCodec.decode (requestCodec.encode request) = some request :=
  requestCodec.decode_encode request

theorem request_canonical {bytes : List UInt8} {request : Request}
    (decoded : requestCodec.decode bytes = some request) :
    requestCodec.encode request = bytes :=
  framed_canonical requestFrame requestStream decoded

theorem response_roundtrip (response : Response) :
    responseCodec.decode (responseCodec.encode response) = some response :=
  responseCodec.decode_encode response

theorem response_canonical {bytes : List UInt8} {response : Response}
    (decoded : responseCodec.decode bytes = some response) :
    responseCodec.encode response = bytes :=
  framed_canonical responseFrame responseStream decoded

theorem encoded_response_bound (response : Response) (bytes : List UInt8)
    (accepted : encodeResponse response = .ok bytes) :
    bytes.length ≤ maxResponseBytes ∧ responseCodec.decode bytes = some response := by
  unfold encodeResponse at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  split at accepted
  · rename_i bounded
    injection accepted with same
    subst bytes
    exact ⟨bounded, response_roundtrip response⟩
  · cases accepted

theorem malformed_key_refuses (store : PayStore) (clock : ClockCell.Clock) (request : Request)
    (malformed : ¬request.valid) : project store clock request = .error .malformedRequest := by
  simp [project, malformed]

theorem exact_expiry_boundary (hour : Nat) (record : EnrolRecord) (expired : record.leaseUntil ≤ hour) :
    leaseState hour (some record) = .expired := by
  simp [leaseState, Nat.not_lt.mpr expired]

theorem no_paid_record_not_enrolled (hour : Nat) :
    leaseState hour none = .notEnrolled := rfl

theorem unindexed_v1_is_not_positive (store : PayStore) (identity : List UInt8) (locator : Locator)
    (origin : claimAt store locator.id = none)
    (consumption : claimConsumptionAt store locator.id = none)
    (journal : journalAt store locator.id = none) :
    paymentAt store identity locator = .ok .unobservedOrUnknownPositiveV1 := by
  simp [paymentAt, origin, consumption, journal]

theorem consumption_without_origin_refuses (store : PayStore) (identity : List UInt8)
    (locator : Locator) (consumed : PayEnrolClaim.Consumption)
    (origin : claimAt store locator.id = none)
    (consumption : claimConsumptionAt store locator.id = some consumed) :
    paymentAt store identity locator = .error .inconsistentIndex := by
  simp [paymentAt, origin, consumption]

/-- Changing any unrelated payment row cannot change this answer. This
statement covers precisely the three keyed reads, not a whole-store scan. -/
theorem paymentAt_only_exact_key (left right : PayStore) (identity : List UInt8) (locator : Locator)
    (origin : claimAt left locator.id = claimAt right locator.id)
    (consumption : claimConsumptionAt left locator.id = claimConsumptionAt right locator.id)
    (journal : journalAt left locator.id = journalAt right locator.id) :
    paymentAt left identity locator = paymentAt right identity locator := by
  simp only [paymentAt, origin, consumption, journal]

/-- One transaction's different recipients remain distinct payment locators. -/
theorem locator_binds_signature_recipient (left right : Locator)
    (leftShaped : left.signature.length = 64) (rightShaped : right.signature.length = 64)
    (same : left.id = right.id) :
    left.signature = right.signature ∧ left.originalRecipient = right.originalRecipient := by
  simp only [Locator.id, List.append_assoc, List.append_cancel_left_eq] at same
  exact List.append_inj same (leftShaped.trans rightShaped.symm)

theorem pending_requires_unconsumed_origin (store : PayStore) (identity : List UInt8)
    (locator : Locator) (claim : PayEnrolClaim.Claim) (reason : PayEnrolClaim.PendingReason)
    (origin : claimAt store locator.id = some claim)
    (consumption : claimConsumptionAt store locator.id = none)
    (journal : journalAt store locator.id = none)
    (idExact : claim.id = locator.id) (owner : claim.ownerIdentityKey = identity)
    (pending : claim.reason = some reason) :
    paymentAt store identity locator =
      .ok (.pendingV2 ⟨claim.original.amountAtomic, claim.original.slot, claim.original.index, reason⟩) := by
  simp [paymentAt, origin, consumption, journal, idExact, owner, pending]

theorem consumed_requires_exact_original_match (store : PayStore) (identity : List UInt8)
    (locator : Locator) (claim : PayEnrolClaim.Claim) (consumed : PayEnrolClaim.Consumption)
    (origin : claimAt store locator.id = some claim)
    (consumption : claimConsumptionAt store locator.id = some consumed)
    (journal : journalAt store locator.id = none)
    (idExact : claim.id = locator.id) (owner : claim.ownerIdentityKey = identity)
    (matches : consumed.matchesClaim claim) :
    paymentAt store identity locator = .ok (.consumedV2 (consumedOf claim consumed)) := by
  simp [paymentAt, origin, consumption, journal, idExact, owner, matches]

theorem direct_origin_without_atomic_consumption_refuses (store : PayStore) (identity : List UInt8)
    (locator : Locator) (claim : PayEnrolClaim.Claim)
    (origin : claimAt store locator.id = some claim)
    (consumption : claimConsumptionAt store locator.id = none)
    (journal : journalAt store locator.id = none)
    (idExact : claim.id = locator.id) (owner : claim.ownerIdentityKey = identity)
    (direct : claim.reason = none) :
    paymentAt store identity locator = .error .inconsistentIndex := by
  simp [paymentAt, origin, consumption, journal, idExact, owner, direct]

theorem requested_identity_must_match_origin (store : PayStore) (identity : List UInt8)
    (locator : Locator) (claim : PayEnrolClaim.Claim)
    (origin : claimAt store locator.id = some claim)
    (journal : journalAt store locator.id = none)
    (idExact : claim.id = locator.id) (other : claim.ownerIdentityKey ≠ identity) :
    paymentAt store identity locator = .error .identityMismatch := by
  cases consumption : claimConsumptionAt store locator.id <;>
    simp [paymentAt, origin, consumption, journal, idExact, other]

private def sampleRequest : Request :=
  ⟨List.replicate 32 1, some ⟨List.replicate 64 2, List.replicate 32 3⟩⟩

theorem sample_request_fits :
    (requestCodec.encode sampleRequest).length ≤ maxRequestBytes := by decide

theorem malformed_recipient_fixture :
    ¬(⟨List.replicate 32 1, some ⟨List.replicate 64 2, [3]⟩⟩ : Request).valid := by decide

private def sampleResponse : Response :=
  ⟨sampleRequest, 42, some ⟨1000, 150000⟩, some .stale, .expired,
    some ⟨101, 102, List.replicate 51 4, some 7, 41, 900⟩,
    .consumedV2 ⟨1000, 900, 7, .enroll, 2, 1000, 10, 336, 654, ⟨123⟩, .originalMemo⟩⟩

theorem sample_response_fits :
    encodeResponse sampleResponse = .ok (responseCodec.encode sampleResponse) := by decide

#assert_axioms paymentAt_only_exact_key
#assert_axioms locator_binds_signature_recipient
#assert_axioms pending_requires_unconsumed_origin
#assert_axioms consumed_requires_exact_original_match
#assert_axioms direct_origin_without_atomic_consumption_refuses
#assert_axioms requested_identity_must_match_origin
#assert_axioms sample_request_fits
#assert_axioms malformed_recipient_fixture
#assert_axioms sample_response_fits

#assert_axioms request_roundtrip
#assert_axioms request_canonical
#assert_axioms response_roundtrip
#assert_axioms response_canonical
#assert_axioms encoded_response_bound
#assert_axioms malformed_key_refuses
#assert_axioms exact_expiry_boundary
#assert_axioms no_paid_record_not_enrolled
#assert_axioms unindexed_v1_is_not_positive
#assert_axioms consumption_without_origin_refuses

end Minidregg.Kernel.PayClaimStatus
