/-
Source quotes for a new payment or explicit recovery of one retained deposit.
Uncompiled candidate for the integrator's authorized Lean pass. No reservation,
write, signature, RPC, or duplicated native pricing formula is performed here.
The Host supplies authenticated cells/Clock and the actual source birth pricing.
-/
import Kernel.PayClaimDecision

namespace Minidregg.Kernel.PayClaimQuote

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.CredentialAuthorityState (currentSigningKey)
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff

set_option autoImplicit false

abbrev Pricing := PayEnrolV2Decision.Pricing
abbrev Authority := CredentialAuthorityDomain.Snapshot
abbrev CurrentOwner := PayEnrolV2Decision.CurrentOwner
abbrev FixedQuote := PayEnrolClaim.FixedQuote

def maxRequestBytes : Nat := 1024
def maxResponseBytes : Nat := 8192
/-- Bounds processing-chain hours, not an elapsed wall-clock promise. -/
def maxQuoteLifetimeHours : Nat := 1

structure Terms where
  mode : PayEnrolClaim.Mode
  weeks : Nat
  starter : Nat
  expiryHour : Nat
  deriving DecidableEq, Repr

def termsStream : StreamCodec Terms :=
  StreamCodec.xmap
    (StreamCodec.product PayEnrolClaim.modeStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun v => (v.mode, v.weeks, v.starter, v.expiryHour))
    (fun (mode, weeks, starter, expiryHour) => ⟨mode, weeks, starter, expiryHour⟩)
    (by intro v; cases v; rfl)

structure Purchase where
  identityKey : List UInt8
  sshKey : List UInt8
  freshNext : Option Digest
  terms : Terms
  deriving DecidableEq, Repr

def purchaseStream : StreamCodec Purchase :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.option digestStream) termsStream)))
    (fun v => (v.identityKey, v.sshKey, v.freshNext, v.terms))
    (fun (identityKey, sshKey, freshNext, terms) => ⟨identityKey, sshKey, freshNext, terms⟩)
    (by intro v; cases v; rfl)

structure ClaimRequest where
  claimId : List UInt8
  terms : Terms
  nonce : Nat
  deriving DecidableEq, Repr

def claimRequestStream : StreamCodec ClaimRequest :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product termsStream StreamCodec.nat))
    (fun v => (v.claimId, v.terms, v.nonce))
    (fun (claimId, terms, nonce) => ⟨claimId, terms, nonce⟩)
    (by intro v; cases v; rfl)

abbrev Request := Sum Purchase ClaimRequest

def requestStream : StreamCodec Request := StreamCodec.sum purchaseStream claimRequestStream

def Terms.valid (terms : Terms) : Prop :=
  0 < terms.weeks ∧ terms.weeks < 2 ^ 32 ∧ terms.starter < 2 ^ 64 ∧ terms.expiryHour < 2 ^ 64
instance (terms : Terms) : Decidable terms.valid := by unfold Terms.valid; infer_instance

def Request.valid : Request → Prop
  | .inl purchase => purchase.identityKey.length = 32 ∧ purchase.sshKey.length = 32 ∧
      purchase.terms.valid ∧ (match purchase.freshNext with
        | none => True | some next => next.value < 2 ^ 256)
  | .inr claim => claim.claimId.length = 102 ∧ claim.terms.valid ∧ claim.nonce < 2 ^ 64
instance (request : Request) : Decidable request.valid := by
  cases request with
  | inl purchase => unfold Request.valid; cases purchase.freshNext <;> infer_instance
  | inr claim => unfold Request.valid; infer_instance

def requestFrame : List UInt8 := "DREGG/PAY/CLAIM-QUOTE/REQUEST/v1".toUTF8.toList
def requestCodec : LawfulCodec Request := framed requestFrame requestStream

/-- Total metadata encoding; purchase output additionally checks the exact fixed
wire Unsigned.WellFormed before returning it as signing material. -/
def wireModeStream : StreamCodec PayEnrolMemoV2.Mode where
  encode mode := StreamCodec.nat.encode mode.byte.toNat
  decodePrefix bytes := do
    let (tag, rest) ← StreamCodec.nat.decodePrefix bytes
    let mode ← match tag with
      | 1 => some PayEnrolMemoV2.Mode.enroll
      | 2 => some PayEnrolMemoV2.Mode.renew
      | 3 => some PayEnrolMemoV2.Mode.renewWithoutCommitment
      | _ => none
    pure (mode, rest)
  decodePrefix_encode := by
    intro mode rest
    cases mode <;> simp [StreamCodec.nat.decodePrefix_encode, PayEnrolMemoV2.Mode.byte]

def unsignedStream : StreamCodec PayEnrolMemoV2.Unsigned :=
  StreamCodec.xmap
    (StreamCodec.product wireModeStream (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))))
    (fun v => (v.mode, v.deploymentCommitment, v.pricingCommitment, v.enrollmentIdentityKey, v.authorizingKey, v.authorityEpoch, v.sshKey, v.nextKeyDigest, v.weeks, v.minimumStarterCredit, v.expiresAtProcessingChainHour, v.amountAtomic))
    (fun (mode, deploymentCommitment, pricingCommitment, enrollmentIdentityKey, authorizingKey, authorityEpoch, sshKey, nextKeyDigest, weeks, minimumStarterCredit, expiresAtProcessingChainHour, amountAtomic) => ⟨mode, deploymentCommitment, pricingCommitment, enrollmentIdentityKey, authorizingKey, authorityEpoch, sshKey, nextKeyDigest, weeks, minimumStarterCredit, expiresAtProcessingChainHour, amountAtomic⟩)
    (by intro v; cases v; rfl)

def ownerStream : StreamCodec CurrentOwner :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.option digestStream))))
    (fun v => (v.identityKey, v.currentKey, v.epoch, v.nextKeyDigest))
    (fun (identityKey, currentKey, epoch, nextKeyDigest) => ⟨identityKey, currentKey, epoch, nextKeyDigest⟩)
    (by intro v; cases v; rfl)

def quoteStream : StreamCodec FixedQuote :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun v => (v.amountAtomic, v.credit, v.birthFee, v.requestedWeeks, v.membershipCredit, v.creditedRemainder, v.minimumStarterCredit))
    (fun (amountAtomic, credit, birthFee, requestedWeeks, membershipCredit, creditedRemainder, minimumStarterCredit) => ⟨amountAtomic, credit, birthFee, requestedWeeks, membershipCredit, creditedRemainder, minimumStarterCredit⟩)
    (by intro v; cases v; rfl)

structure Settlement where
  index : Nat
  recipient : List UInt8
  mint : List UInt8
  tokenProgram : List UInt8
  deriving DecidableEq, Repr

def settlementStream : StreamCodec Settlement :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream)))
    (fun v => (v.index, v.recipient, v.mint, v.tokenProgram))
    (fun (index, recipient, mint, tokenProgram) => ⟨index, recipient, mint, tokenProgram⟩)
    (by intro v; cases v; rfl)

abbrev SigningMaterial := Sum PayEnrolMemoV2.Unsigned PayClaimCommand.Command

def signingMaterialStream : StreamCodec SigningMaterial :=
  StreamCodec.sum unsignedStream PayClaimCommand.commandStream

structure Response where
  authorityRoot : Digest
  payRoot : Digest
  asOfSlot : Nat
  asOfBlockTime : Nat
  settlement : Settlement
  owner : CurrentOwner
  split : FixedQuote
  signingMaterial : SigningMaterial
  deriving DecidableEq, Repr

def responseStream : StreamCodec Response :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product settlementStream (StreamCodec.product ownerStream (StreamCodec.product quoteStream signingMaterialStream)))))))
    (fun v => (v.authorityRoot, v.payRoot, v.asOfSlot, v.asOfBlockTime, v.settlement, v.owner, v.split, v.signingMaterial))
    (fun (authorityRoot, payRoot, asOfSlot, asOfBlockTime, settlement, owner, split, signingMaterial) => ⟨authorityRoot, payRoot, asOfSlot, asOfBlockTime, settlement, owner, split, signingMaterial⟩)
    (by intro v; cases v; rfl)

/-- A quote cannot reserve price, custody, a book index, or a lease. -/
def Response.priceReserved (_response : Response) : Bool := false

def responseFrame : List UInt8 := "DREGG/PAY/CLAIM-QUOTE/RESPONSE/v1".toUTF8.toList
def responseCodec : LawfulCodec Response := framed responseFrame responseStream

inductive Reject where
  | requestTooLarge | malformedRequest | responseTooLarge | malformedResponse
  | authorityDomainMismatch | tariffInvalid | selfEnrolOff | recipientUnavailable
  | floatUnavailable | assetMismatch | modeMismatch | freshNextRequired | unexpectedNext
  | pendingPurchaseRequiresClaim | subjectTaken | invalidOwner | missingClaim
  | malformedClaim | notPending | alreadyConsumed | deploymentMismatch | recipientMismatch
  | expired | expiryTooFar | sshKeyTaken | sshKeyMismatch
  | owner (reason : PayClaimDecision.Reject)
  | freshness (reason : PayChainTip.FreshnessReject)
  | economics (reason : PayEnrolClaim.QuoteReject)
  | acceptance (reason : PayEnrolClaim.Reject)
  deriving DecidableEq, Repr

def decodeRequest (bytes : List UInt8) : Except Reject Request := do
  if bytes.length > maxRequestBytes then throw .requestTooLarge
  let request ← match requestCodec.decode bytes with
    | none => .error .malformedRequest | some request => .ok request
  if ¬request.valid then throw .malformedRequest
  return request

/-- The Host uses this source selector to compute identity-specific ordinary
birth pricing before quote. A claim request cannot choose a different identity. -/
def requestIdentity (pay : PayStore) (request : Request) : Except Reject (List UInt8) :=
  match request with
  | .inl purchase =>
    if request.valid then .ok purchase.identityKey else .error .malformedRequest
  | .inr claim =>
    if ¬request.valid then .error .malformedRequest
    else match claimAt pay claim.claimId with
      | none => .error .missingClaim
      | some origin =>
        if origin.valid ∧ origin.id = claim.claimId ∧ claimMemoCoherent origin = true then
          .ok origin.ownerIdentityKey
        else .error .malformedClaim

/-- The signed literal expiry is preserved. Its inclusive upper bound is a
source policy, rather than an invented reservation or silently altered expiry. -/
def checkExpiry (tip : ChainTip) (terms : Terms) : Except Reject Unit :=
  if terms.expiryHour < tip.hour then .error .expired
  else if tip.hour + maxQuoteLifetimeHours < terms.expiryHour then .error .expiryTooFar
  else .ok ()

structure LoadedTerms where
  tariff : Tariff
  settlement : Settlement
  float : Nat

def loadTerms (pay : PayStore) : Except Reject LoadedTerms := do
  let tariff ← match tariffOf pay with
    | none => .error .tariffInvalid | some tariff => .ok tariff
  if ¬tariff.valid then throw .tariffInvalid
  let index ← match tariff.enrolIndex with
    | none => .error .selfEnrolOff | some index => .ok index
  let recipient ← match bookAt pay index with
    | none => .error .recipientUnavailable | some recipient => .ok recipient
  if recipient.length ≠ 32 ∨ recipient = zeroKey then throw .recipientUnavailable
  let float ← match assignmentAt pay index with
    | none => .error .floatUnavailable | some account => .ok account
  if float = tariff.asset then throw .floatUnavailable
  return ⟨tariff, ⟨index, recipient, tariff.mint, tariff.tokenProgram⟩, float⟩

structure Custody where
  owner : CurrentOwner
  record : Option EnrolRecord
  deriving DecidableEq, Repr

def Custody.mode (custody : Custody) : PayEnrolClaim.Mode :=
  if custody.record.isSome then .renew else .enroll

def Custody.birthFee (custody : Custody) (pricing : Pricing) : Nat :=
  if custody.record.isSome then 0 else pricing.birthFee

/-- Reuse the current-owner gate, then retain the actual optional NEXT from the
same immutable registry snapshot. None is never replaced by a fictitious digest. -/
def existingCustody (pay : PayStore) (authority : Authority) (identity : List UInt8) :
    Except Reject Custody := do
  let current ← (PayClaimDecision.resolveOwner pay authority identity).mapError Reject.owner
  match current with
  | .pending owner => return ⟨CurrentOwner.ofPending owner, none⟩
  | .admitted _ before =>
    match currentSigningKey authority.logical ⟨PayEnrolMemo.subjectOf identity⟩ with
    | none => throw .invalidOwner
    | some key =>
      let owner := CurrentOwner.ofRegistry identity key
      if ¬owner.valid then throw .invalidOwner
      return ⟨owner, some before⟩

/-- Only a new identity supplies NEXT. Pending and admitted custody derive it
from source. The frozen initial-enrollment grammar cannot sign at epoch > 1. -/
def checkInitialPurchase (owner : CurrentOwner) : Except Reject Unit :=
  if owner.currentKey ≠ owner.identityKey ∨ owner.epoch ≠ 1 then
    .error .pendingPurchaseRequiresClaim
  else .ok ()

def purchaseCustody (pay : PayStore) (authority : Authority) (purchase : Purchase) :
    Except Reject Custody := do
  if (enrolmentAt pay purchase.identityKey).isSome ||
      (pendingOwnerAt pay purchase.identityKey).isSome then
    if purchase.freshNext.isSome then throw .unexpectedNext
    let custody ← existingCustody pay authority purchase.identityKey
    if custody.record.isNone then
      checkInitialPurchase custody.owner
    return custody
  else
    if (authority.logical ⟨.subjectKeyEpoch, ⟨PayEnrolMemo.subjectOf purchase.identityKey⟩⟩).isSome then
      throw .subjectTaken
    let next ← match purchase.freshNext with
      | none => .error .freshNextRequired | some next => .ok next
    let owner : CurrentOwner := ⟨purchase.identityKey, purchase.identityKey, 1, some next⟩
    if ¬owner.valid then throw .invalidOwner
    return ⟨owner, none⟩

/-- Some(0) is mode 2; absent NEXT is mode 3 with canonical zero. -/
def wireMode (custody : Custody) : PayEnrolMemoV2.Mode :=
  match custody.record, custody.owner.nextKeyDigest with
  | none, _ => .enroll
  | some _, some _ => .renew
  | some _, none => .renewWithoutCommitment

def unsignedPurchase (pricing : Pricing) (loaded : LoadedTerms) (custody : Custody)
    (purchase : Purchase) (split : FixedQuote) : PayEnrolMemoV2.Unsigned :=
  ⟨wireMode custody,
    PayEnrolPricing.deploymentCommitment pricing.domain pricing.expectedSeed loaded.tariff loaded.settlement.recipient,
    PayEnrolPricing.pricingCommitment pricing.semantics loaded.tariff pricing.creation pricing.template custody.mode split,
    custody.owner.identityKey, custody.owner.currentKey, custody.owner.epoch,
    purchase.sshKey, custody.owner.nextKeyDigest.getD ⟨0⟩,
    purchase.terms.weeks, purchase.terms.starter, purchase.terms.expiryHour, split.amountAtomic⟩

def response (pay : PayCell.Cell) (authority : Authority) (tip : ChainTip)
    (loaded : LoadedTerms) (owner : CurrentOwner) (split : FixedQuote)
    (material : SigningMaterial) : Response :=
  ⟨authority.cell.root, pay.root, tip.slot, tip.blockTime, loaded.settlement, owner, split, material⟩

private def quotePurchase (pay : PayCell.Cell) (authority : Authority) (pricing : Pricing)
    (tip : ChainTip) (loaded : LoadedTerms) (purchase : Purchase) : Except Reject Response := do
  let _ ← checkExpiry tip purchase.terms
  let custody ← purchaseCustody pay.logical authority purchase
  if purchase.terms.mode ≠ custody.mode then throw .modeMismatch
  let blob := PayEnrolMemo.sshBlobOf purchase.sshKey
  match custody.record with
  | none => if (sshIndexAt pay.logical blob).isSome then throw .sshKeyTaken
  | some before => if before.sshBlob ≠ blob then throw .sshKeyMismatch
  let split ← (PayEnrolPricing.quotePurchase loaded.tariff (custody.birthFee pricing)
    purchase.terms.weeks purchase.terms.starter).mapError Reject.economics
  let unsigned := unsignedPurchase pricing loaded custody purchase split
  if ¬unsigned.WellFormed then throw .malformedResponse
  return response pay authority tip loaded custody.owner split (.inl unsigned)

private def quoteClaim (pay : PayCell.Cell) (authority : Authority) (pricing : Pricing)
    (tip : ChainTip) (loaded : LoadedTerms) (request : ClaimRequest) : Except Reject Response := do
  let _ ← checkExpiry tip request.terms
  let origin ← match claimAt pay.logical request.claimId with
    | none => .error .missingClaim | some origin => .ok origin
  if ¬origin.valid ∨ origin.id ≠ request.claimId ∨ claimMemoCoherent origin ≠ true then
    throw .malformedClaim
  if origin.reason.isNone then throw .notPending
  if (claimConsumptionAt pay.logical origin.id).isSome then throw .alreadyConsumed
  if origin.original.recipient ≠ loaded.settlement.recipient then throw .recipientMismatch
  if origin.original.mint ≠ loaded.tariff.mint ∨ origin.original.tokenProgram ≠ loaded.tariff.tokenProgram then
    throw .assetMismatch
  let memo ← match PayEnrolMemoV2.parse origin.rawMemo with
    | .error _ => .error .malformedClaim | .ok memo => .ok memo
  if memo.unsigned.deploymentCommitment ≠ PayEnrolPricing.deploymentCommitment
      pricing.domain pricing.expectedSeed loaded.tariff origin.original.recipient then
    throw .deploymentMismatch
  let custody ← existingCustody pay.logical authority origin.ownerIdentityKey
  if request.terms.mode ≠ custody.mode then throw .modeMismatch
  let blob := PayEnrolMemo.sshBlobOf memo.unsigned.sshKey
  match custody.record with
  | none => if (sshIndexAt pay.logical blob).isSome then throw .sshKeyTaken
  | some before => if before.sshBlob ≠ blob then throw .sshKeyMismatch
  let split ← (PayEnrolClaim.quoteFixed origin.original.amountAtomic loaded.tariff
    (custody.birthFee pricing) request.terms.weeks request.terms.starter).mapError Reject.economics
  let commitment := PayEnrolPricing.pricingCommitment pricing.semantics loaded.tariff
    pricing.creation pricing.template custody.mode split
  let acceptance : PayEnrolClaim.AcceptRequest :=
    ⟨custody.mode, origin.id, custody.owner.identityKey, custody.owner.currentKey,
      custody.owner.epoch, request.nonce, commitment, request.terms.weeks,
      request.terms.starter, request.terms.expiryHour⟩
  let _ ← (PayEnrolClaim.checkClaim origin custody.owner.toClaimOwner loaded.tariff
    (custody.birthFee pricing) custody.mode commitment tip.hour acceptance).mapError Reject.acceptance
  let command : PayClaimCommand.Command := ⟨authority.cell.root, pay.root, .inl acceptance⟩
  if ¬command.valid then throw .malformedResponse
  return response pay authority tip loaded custody.owner split (.inr command)

/-- Both quote paths are read-only and use fresh retained chain evidence. A
subsequent receiving transaction recomputes all ownership and economic terms. -/
def quote (pay : PayCell.Cell) (authority : Authority) (clock : ClockCell.Clock)
    (pricing : Pricing) (request : Request) : Except Reject Response := do
  if ¬request.valid then throw .malformedRequest
  if authority.domain ≠ pricing.domain then throw .authorityDomainMismatch
  let tip ← (PayChainTip.fresh clock (chainTipOf pay.logical)).mapError Reject.freshness
  let loaded ← loadTerms pay.logical
  match request with
  | .inl purchase => quotePurchase pay authority pricing tip loaded purchase
  | .inr claim => quoteClaim pay authority pricing tip loaded claim

/-- Bound scalar serialization before encoding the variable-width metadata.
The fixed memo and closed command are separately source-shape checked above. -/
def Response.small (value : Response) : Prop :=
  value.authorityRoot.value < 2 ^ 256 ∧ value.payRoot.value < 2 ^ 256 ∧
  value.asOfSlot < 2 ^ 64 ∧ value.asOfBlockTime < 2 ^ 64 ∧
  value.settlement.index < 2 ^ 64 ∧ value.settlement.recipient.length = 32 ∧
  value.settlement.mint.length = 32 ∧ value.settlement.tokenProgram.length = 32 ∧
  value.owner.valid ∧
  value.split.amountAtomic < 2 ^ 64 ∧ value.split.credit < 2 ^ 256 ∧
  value.split.birthFee < 2 ^ 256 ∧ value.split.requestedWeeks < 2 ^ 32 ∧
  value.split.membershipCredit < 2 ^ 256 ∧ value.split.creditedRemainder < 2 ^ 256 ∧
  value.split.minimumStarterCredit < 2 ^ 64 ∧
  match value.signingMaterial with
  | .inl unsigned => unsigned.WellFormed
  | .inr command => command.valid

instance (value : Response) : Decidable value.small := by
  unfold Response.small
  cases value.signingMaterial <;> infer_instance

def encodeResponse (value : Response) : Except Reject (List UInt8) :=
  if ¬value.small then .error .malformedResponse
  else
    let bytes := responseCodec.encode value
    if bytes.length ≤ maxResponseBytes then .ok bytes else .error .responseTooLarge

def serve (pay : PayCell.Cell) (authority : Authority) (clock : ClockCell.Clock)
    (pricing : Pricing) (bytes : List UInt8) : Except Reject (List UInt8) := do
  let request ← decodeRequest bytes
  let value ← quote pay authority clock pricing request
  encodeResponse value

theorem request_roundtrip (value : Request) :
    requestCodec.decode (requestCodec.encode value) = some value := requestCodec.decode_encode value

theorem request_canonical {bytes : List UInt8} {value : Request}
    (decoded : requestCodec.decode bytes = some value) : requestCodec.encode value = bytes :=
  framed_canonical requestFrame requestStream decoded

theorem response_roundtrip (value : Response) :
    responseCodec.decode (responseCodec.encode value) = some value := responseCodec.decode_encode value

theorem response_canonical {bytes : List UInt8} {value : Response}
    (decoded : responseCodec.decode bytes = some value) : responseCodec.encode value = bytes :=
  framed_canonical responseFrame responseStream decoded

theorem encoded_response_bound (value : Response) (bytes : List UInt8)
    (accepted : encodeResponse value = .ok bytes) :
    bytes.length ≤ maxResponseBytes ∧ responseCodec.decode bytes = some value := by
  unfold encodeResponse at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  split at accepted
  · rename_i bounded
    injection accepted with same
    subst bytes
    exact ⟨bounded, response_roundtrip value⟩
  · cases accepted

theorem oversized_request_refuses (bytes : List UInt8) (large : maxRequestBytes < bytes.length) :
    decodeRequest bytes = .error .requestTooLarge := by
  simp [decodeRequest, large]

theorem no_reservation (value : Response) : value.priceReserved = false := rfl

theorem rotated_pending_purchase_refuses (owner : CurrentOwner) (rotated : owner.epoch ≠ 1) :
    checkInitialPurchase owner = .error .pendingPurchaseRequiresClaim := by
  simp [checkInitialPurchase, rotated]

theorem initial_purchase_allowed (identity : List UInt8) (next : Digest) :
    checkInitialPurchase ⟨identity, identity, 1, some next⟩ = .ok () := by
  simp [checkInitialPurchase]

theorem renewal_without_next_mode (owner : CurrentOwner) (record : EnrolRecord)
    (absent : owner.nextKeyDigest = none) :
    wireMode ⟨owner, some record⟩ = .renewWithoutCommitment := by simp [wireMode, absent]

theorem renewal_some_zero_mode (owner : CurrentOwner) (record : EnrolRecord)
    (present : owner.nextKeyDigest = some ⟨0⟩) :
    wireMode ⟨owner, some record⟩ = .renew := by simp [wireMode, present]

theorem purchase_expiry_literal (pricing : Pricing) (loaded : LoadedTerms) (custody : Custody)
    (purchase : Purchase) (split : FixedQuote) :
    (unsignedPurchase pricing loaded custody purchase split).expiresAtProcessingChainHour =
      purchase.terms.expiryHour := rfl

theorem expiry_boundary_fixture :
    checkExpiry ⟨1, 3600⟩ ⟨.enroll, 1, 0, 2⟩ = .ok () := by decide

theorem expiry_too_far_fixture :
    checkExpiry ⟨1, 3600⟩ ⟨.enroll, 1, 0, 3⟩ = .error .expiryTooFar := by decide

#assert_axioms request_roundtrip
#assert_axioms request_canonical
#assert_axioms response_roundtrip
#assert_axioms response_canonical
#assert_axioms encoded_response_bound
#assert_axioms oversized_request_refuses
#assert_axioms no_reservation
#assert_axioms rotated_pending_purchase_refuses
#assert_axioms initial_purchase_allowed
#assert_axioms renewal_without_next_mode
#assert_axioms renewal_some_zero_mode
#assert_axioms purchase_expiry_literal
#assert_axioms expiry_boundary_fixture
#assert_axioms expiry_too_far_fixture

end Minidregg.Kernel.PayClaimQuote
