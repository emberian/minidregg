/-
Authenticated paid-entry origin index, pending custody and one-time consumption.

The observation receiver creates Claim only after its existing finalized-chain,
exact amount/asset/nullifier and Checked possession boundary. Malformed or
unsigned observations are not owned claims. The immutable row retains every
original fact for both immediate admission (reason=None) and pending value
(reason=Some). A stale quote is never silently replaced.

This module deliberately imports neither PayCell nor PayObservation. PayCell
owns append-only Claim/Consumption namespaces and RAM PendingOwner, and its law
must bind a Consumption to its original Claim. Raw memo coherence is checked
by the receiving codec/law; these internal codecs do not verify signatures.

An acceptance command is authenticated by the existing Checked native-signature
boundary. Here authorization compares concrete stable identity, current key and
epoch, and recomputes value from the retained deposit and current source tariff.
No caller-supplied boolean acts as a proof of possession or correct pricing.
-/
import Kernel.PayReceivingContract
import Kernel.PayTariff

namespace Minidregg.Kernel.PayEnrolClaim

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PayTariff

set_option autoImplicit false

/-- Only authenticated deposits may become owned pending value. authStale is
for a known identity whose formerly authorized key/epoch no longer matches;
it must not turn an unrelated signing key into that identity's owner. -/
inductive PendingReason where
  | termsStale
  | expired
  | authStale
  deriving DecidableEq, Repr

def PendingReason.code : PendingReason → Nat
  | .termsStale => 0 | .expired => 1 | .authStale => 2

def PendingReason.ofCode : Nat → Option PendingReason
  | 0 => some .termsStale | 1 => some .expired | 2 => some .authStale | _ => none

theorem PendingReason.ofCode_code (reason : PendingReason) :
    PendingReason.ofCode reason.code = some reason := by
  cases reason <;> rfl

def pendingReasonStream : StreamCodec PendingReason where
  encode reason := StreamCodec.nat.encode reason.code
  decodePrefix bytes := do
    let (code, suffix) ← StreamCodec.nat.decodePrefix bytes
    let reason ← PendingReason.ofCode code
    some (reason, suffix)
  decodePrefix_encode := by
    intro reason suffix
    simp [StreamCodec.nat.decodePrefix_encode, PendingReason.ofCode_code]

/-- Exact deposit provenance, independent of the observer's ingress type. -/
structure Observation where
  signature : List UInt8
  recipient : Address32
  slot : Nat
  amountAtomic : Nat
  mint : Address32
  tokenProgram : Address32
  index : Nat
  deriving DecidableEq, Repr

/-- Immutable: later quotes and custody transitions never rewrite this row. -/
structure Claim where
  original : Observation
  rawMemo : List UInt8
  ownerIdentityKey : List UInt8
  /-- None = original quoted admission; Some = retained pending cause. -/
  reason : Option PendingReason
  originalPricingCommitment : Digest
  deriving DecidableEq, Repr

/-- A not-yet-admitted identity's current custody. After enrollment the receiver
must resolve current registry authority instead of falling back to this row. -/
structure PendingOwner where
  identityKey : List UInt8
  currentKey : List UInt8
  epoch : Nat
  nextKeyDigest : Digest
  deriving DecidableEq, Repr

/-- Current acceptance authority, independent of pre-rotation availability.
The receiver derives these fields from either authenticated current registry
state or the existing pending-owner row. This is not a signature witness. -/
structure CurrentOwner where
  identityKey : List UInt8
  currentKey : List UInt8
  epoch : Nat
  deriving DecidableEq, Repr

/-- Pending custody keeps its real next-key commitment in storage; acceptance
needs only the current identity/key/epoch and does not rewrite that custody. -/
def PendingOwner.toCurrentOwner (owner : PendingOwner) : CurrentOwner :=
  ⟨owner.identityKey, owner.currentKey, owner.epoch⟩

/-- Chosen behavior is signed, never silently inferred from membership state. -/
inductive Mode where
  | enroll
  | renew
  deriving DecidableEq, Repr

def Mode.code : Mode → Nat
  | .enroll => 1 | .renew => 2

def Mode.ofCode : Nat → Option Mode
  | 1 => some .enroll | 2 => some .renew | _ => none

theorem Mode.ofCode_code (mode : Mode) : Mode.ofCode mode.code = some mode := by
  cases mode <;> rfl

def modeStream : StreamCodec Mode where
  encode mode := StreamCodec.nat.encode mode.code
  decodePrefix bytes := do
    let (code, suffix) ← StreamCodec.nat.decodePrefix bytes
    let mode ← Mode.ofCode code
    some (mode, suffix)
  decodePrefix_encode := by
    intro mode suffix
    simp [StreamCodec.nat.decodePrefix_encode, Mode.ofCode_code]

/-- Complete signed acceptance identity. claimId binds the original amount,
recipient and signature through immutable storage, not a new transfer. The
pricing commitment is recomputed from source inputs, including selected mode.
The nonce distinguishes deliberate commands; exact retries retain this record. -/
structure AcceptRequest where
  mode : Mode
  claimId : List UInt8
  ownerIdentityKey : List UInt8
  authorizingKey : List UInt8
  authorityEpoch : Nat
  nonce : Nat
  pricingCommitment : Digest
  requestedWeeks : Nat
  minimumStarterCredit : Nat
  expiresAtProcessingChainHour : Nat
  deriving DecidableEq, Repr

/-- Normalized economic terms, shared by original-memo admission and explicit
current-quote acceptance. This is not a detached signature or invented command. -/
structure Terms where
  mode : Mode
  claimId : List UInt8
  ownerIdentityKey : List UInt8
  pricingCommitment : Digest
  requestedWeeks : Nat
  minimumStarterCredit : Nat
  expiresAtProcessingChainHour : Nat
  deriving DecidableEq, Repr

def AcceptRequest.terms (request : AcceptRequest) : Terms :=
  ⟨request.mode, request.claimId, request.ownerIdentityKey, request.pricingCommitment,
    request.requestedWeeks, request.minimumStarterCredit, request.expiresAtProcessingChainHour⟩

/-- The originalMemo tag refers to the actual signed memo in the immutable
origin Claim. It does not manufacture an AcceptRequest, nonce or new signature. -/
inductive Authorization where
  | originalMemo
  | acceptCurrentQuote (request : AcceptRequest)
  deriving DecidableEq, Repr

/-- Append-only source index, installed in the SAME intent as origin, Book and
membership effects. It records the one economic outcome, never a second mint. -/
structure Consumption where
  authorization : Authorization
  terms : Terms
  originalAmountAtomic : Nat
  tariff : Tariff
  mintedCredit : Nat
  birthFee : Nat
  membershipCredit : Nat
  creditedRemainder : Nat
  deriving DecidableEq, Repr

/-- The existing observation-nullifier bytes, not a new hash identity. -/
def soltxPrefix : List UInt8 := [115, 111, 108, 116, 120, 58]

def Claim.id (claim : Claim) : List UInt8 :=
  soltxPrefix ++ claim.original.signature ++ claim.original.recipient

def Consumption.claimId (consumed : Consumption) : List UInt8 := consumed.terms.claimId
def Consumption.ownerIdentityKey (consumed : Consumption) : List UInt8 :=
  consumed.terms.ownerIdentityKey
def Consumption.pricingCommitment (consumed : Consumption) : Digest :=
  consumed.terms.pricingCommitment

def Observation.valid (original : Observation) : Prop :=
  original.signature.length = 64 ∧ original.recipient.length = 32 ∧
  original.mint.length = 32 ∧ original.tokenProgram.length = 32 ∧
  original.mint ≠ zeroKey ∧ original.tokenProgram ≠ zeroKey ∧
  0 < original.amountAtomic ∧ original.amountAtomic < 2 ^ 64 ∧
  original.slot < 2 ^ 64 ∧ original.index < 2 ^ 64

instance (original : Observation) : Decidable original.valid := by
  unfold Observation.valid
  infer_instance

/-- Full semantic memo coherence is a receiving-law obligation. This checks
the fixed transport shape without importing the v2 memo's receiver graph. -/
def Claim.valid (claim : Claim) : Prop :=
  claim.original.valid ∧ claim.ownerIdentityKey.length = 32 ∧
  claim.rawMemo.length = PayReceivingContract.textMemoBytes ∧
    claim.rawMemo.take PayReceivingContract.memoPrefix.length = PayReceivingContract.memoPrefix ∧
  claim.originalPricingCommitment.value < 2 ^ 256

instance (claim : Claim) : Decidable claim.valid := by
  unfold Claim.valid
  infer_instance

def PendingOwner.valid (owner : PendingOwner) : Prop :=
  owner.identityKey.length = 32 ∧ owner.currentKey.length = 32 ∧
  0 < owner.epoch ∧ owner.epoch < 2 ^ 64 ∧ owner.nextKeyDigest.value < 2 ^ 256

instance (owner : PendingOwner) : Decidable owner.valid := by
  unfold PendingOwner.valid
  infer_instance

def CurrentOwner.valid (owner : CurrentOwner) : Prop :=
  owner.identityKey.length = 32 ∧ owner.currentKey.length = 32 ∧
    0 < owner.epoch ∧ owner.epoch < 2 ^ 64

instance (owner : CurrentOwner) : Decidable owner.valid := by
  unfold CurrentOwner.valid
  infer_instance

theorem PendingOwner.toCurrentOwner_valid (owner : PendingOwner) (valid : owner.valid) :
    owner.toCurrentOwner.valid :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1⟩

theorem pending_projection_preserves_identity (owner : PendingOwner) :
    owner.toCurrentOwner.identityKey = owner.identityKey ∧
    owner.toCurrentOwner.currentKey = owner.currentKey ∧
    owner.toCurrentOwner.epoch = owner.epoch := ⟨rfl, rfl, rfl⟩

def AcceptRequest.valid (request : AcceptRequest) : Prop :=
  request.claimId.length = 102 ∧ request.claimId.take 6 = soltxPrefix ∧
  request.ownerIdentityKey.length = 32 ∧ request.authorizingKey.length = 32 ∧
  0 < request.authorityEpoch ∧ request.authorityEpoch < 2 ^ 64 ∧
  request.pricingCommitment.value < 2 ^ 256 ∧
  0 < request.requestedWeeks ∧ request.requestedWeeks < 2 ^ 32 ∧
  request.minimumStarterCredit < 2 ^ 64 ∧
  request.expiresAtProcessingChainHour < 2 ^ 64

instance (request : AcceptRequest) : Decidable request.valid := by
  unfold AcceptRequest.valid
  infer_instance

def Terms.valid (terms : Terms) : Prop :=
  terms.claimId.length = 102 ∧ terms.claimId.take 6 = soltxPrefix ∧
  terms.ownerIdentityKey.length = 32 ∧ terms.pricingCommitment.value < 2 ^ 256 ∧
  0 < terms.requestedWeeks ∧ terms.requestedWeeks < 2 ^ 32 ∧
  terms.minimumStarterCredit < 2 ^ 64 ∧ terms.expiresAtProcessingChainHour < 2 ^ 64

instance (terms : Terms) : Decidable terms.valid := by unfold Terms.valid; infer_instance

theorem AcceptRequest.terms_valid (request : AcceptRequest) (valid : request.valid) :
    request.terms.valid := by
  rcases valid with ⟨idLength, prefix, identity, key, epoch, epochBound, pricing,
    weeks, weeksBound, starter, expiry⟩
  exact ⟨idLength, prefix, identity, pricing, weeks, weeksBound, starter, expiry⟩

/-- Original memo/term coherence is checked against the retained origin by the
PayCell law. Current-quote coherence is fully local to this source index row. -/
def Authorization.matchesTerms (authorization : Authorization) (terms : Terms) : Prop :=
  match authorization with
  | .originalMemo => True
  | .acceptCurrentQuote request => request.valid ∧ terms = request.terms

instance (authorization : Authorization) (terms : Terms) :
    Decidable (authorization.matchesTerms terms) := by
  cases authorization <;> unfold Authorization.matchesTerms <;> infer_instance

/-- The local consumption invariant; the cell law additionally looks up the
original claim and checks id, stable owner and originalAmountAtomic equality. -/
def Consumption.valid (consumed : Consumption) : Prop :=
  consumed.terms.valid ∧ consumed.authorization.matchesTerms consumed.terms ∧
  consumed.tariff.valid ∧
  0 < consumed.originalAmountAtomic ∧ consumed.originalAmountAtomic < 2 ^ 64 ∧
  consumed.originalAmountAtomic ≤ consumed.tariff.maxPerObservation ∧
  consumed.mintedCredit = consumed.tariff.creditFor consumed.originalAmountAtomic ∧
  consumed.membershipCredit = consumed.terms.requestedWeeks * consumed.tariff.weekCredit ∧
  consumed.birthFee + consumed.membershipCredit + consumed.creditedRemainder = consumed.mintedCredit ∧
  consumed.terms.minimumStarterCredit ≤ consumed.creditedRemainder ∧
  (consumed.terms.mode = .renew → consumed.birthFee = 0)

instance (consumed : Consumption) : Decidable consumed.valid := by
  unfold Consumption.valid
  infer_instance

/-! ## Strict internal codecs -/

def observationStream : StreamCodec Observation :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream (StreamCodec.product bytesStream StreamCodec.nat))))))
    (fun value => (value.signature, value.recipient, value.slot, value.amountAtomic, value.mint, value.tokenProgram, value.index))
    (fun (signature, recipient, slot, amountAtomic, mint, tokenProgram, index) => ⟨signature, recipient, slot, amountAtomic, mint, tokenProgram, index⟩)
    (by intro value; cases value; rfl)

def observationFrame : List UInt8 := PayReceivingContract.observationFrame

def observationCodec : LawfulCodec Observation := framed observationFrame observationStream

theorem observation_roundtrip (value : Observation) :
    observationCodec.decode (observationCodec.encode value) = some value :=
  observationCodec.decode_encode value

theorem observation_canonical {bytes : List UInt8} {value : Observation}
    (decoded : observationCodec.decode bytes = some value) :
    observationCodec.encode value = bytes :=
  framed_canonical observationFrame observationStream decoded

def claimStream : StreamCodec Claim :=
  StreamCodec.xmap
    (StreamCodec.product observationStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.option pendingReasonStream) digestStream))))
    (fun value => (value.original, value.rawMemo, value.ownerIdentityKey, value.reason, value.originalPricingCommitment))
    (fun (original, rawMemo, ownerIdentityKey, reason, originalPricingCommitment) => ⟨original, rawMemo, ownerIdentityKey, reason, originalPricingCommitment⟩)
    (by intro value; cases value; rfl)

def claimFrame : List UInt8 := PayReceivingContract.claimFrame

def claimCodec : LawfulCodec Claim := framed claimFrame claimStream

theorem claim_roundtrip (value : Claim) :
    claimCodec.decode (claimCodec.encode value) = some value :=
  claimCodec.decode_encode value

theorem claim_canonical {bytes : List UInt8} {value : Claim}
    (decoded : claimCodec.decode bytes = some value) :
    claimCodec.encode value = bytes :=
  framed_canonical claimFrame claimStream decoded

def pendingOwnerStream : StreamCodec PendingOwner :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat digestStream)))
    (fun value => (value.identityKey, value.currentKey, value.epoch, value.nextKeyDigest))
    (fun (identityKey, currentKey, epoch, nextKeyDigest) => ⟨identityKey, currentKey, epoch, nextKeyDigest⟩)
    (by intro value; cases value; rfl)

def pendingOwnerFrame : List UInt8 := PayReceivingContract.pendingOwnerFrame

def pendingOwnerCodec : LawfulCodec PendingOwner := framed pendingOwnerFrame pendingOwnerStream

theorem pendingOwner_roundtrip (value : PendingOwner) :
    pendingOwnerCodec.decode (pendingOwnerCodec.encode value) = some value :=
  pendingOwnerCodec.decode_encode value

theorem pendingOwner_canonical {bytes : List UInt8} {value : PendingOwner}
    (decoded : pendingOwnerCodec.decode bytes = some value) :
    pendingOwnerCodec.encode value = bytes :=
  framed_canonical pendingOwnerFrame pendingOwnerStream decoded

def acceptRequestStream : StreamCodec AcceptRequest :=
  StreamCodec.xmap
    (StreamCodec.product modeStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))
    (fun value => (value.mode, value.claimId, value.ownerIdentityKey, value.authorizingKey, value.authorityEpoch, value.nonce, value.pricingCommitment, value.requestedWeeks, value.minimumStarterCredit, value.expiresAtProcessingChainHour))
    (fun (mode, claimId, ownerIdentityKey, authorizingKey, authorityEpoch, nonce, pricingCommitment, requestedWeeks, minimumStarterCredit, expiresAtProcessingChainHour) => ⟨mode, claimId, ownerIdentityKey, authorizingKey, authorityEpoch, nonce, pricingCommitment, requestedWeeks, minimumStarterCredit, expiresAtProcessingChainHour⟩)
    (by intro value; cases value; rfl)

def acceptRequestFrame : List UInt8 := PayReceivingContract.acceptRequestFrame

def acceptRequestCodec : LawfulCodec AcceptRequest := framed acceptRequestFrame acceptRequestStream

theorem acceptRequest_roundtrip (value : AcceptRequest) :
    acceptRequestCodec.decode (acceptRequestCodec.encode value) = some value :=
  acceptRequestCodec.decode_encode value

theorem acceptRequest_canonical {bytes : List UInt8} {value : AcceptRequest}
    (decoded : acceptRequestCodec.decode bytes = some value) :
    acceptRequestCodec.encode value = bytes :=
  framed_canonical acceptRequestFrame acceptRequestStream decoded

def termsStream : StreamCodec Terms :=
  StreamCodec.xmap
    (StreamCodec.product modeStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun value => (value.mode, value.claimId, value.ownerIdentityKey, value.pricingCommitment,
      value.requestedWeeks, value.minimumStarterCredit, value.expiresAtProcessingChainHour))
    (fun (mode, id, owner, pricing, weeks, starter, expiry) =>
      ⟨mode, id, owner, pricing, weeks, starter, expiry⟩)
    (by intro value; cases value; rfl)

/-- None tags original memo; Some carries the exact fresh acceptance command. -/
def authorizationStream : StreamCodec Authorization :=
  StreamCodec.xmap (StreamCodec.option acceptRequestStream)
    (fun authorization => match authorization with
      | .originalMemo => none | .acceptCurrentQuote request => some request)
    (fun encoded => match encoded with
      | none => .originalMemo | some request => .acceptCurrentQuote request)
    (by intro authorization; cases authorization <;> rfl)

def consumptionStream : StreamCodec Consumption :=
  StreamCodec.xmap
    (StreamCodec.product authorizationStream (StreamCodec.product termsStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product tariffStream
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun value => (value.authorization, value.terms, value.originalAmountAtomic,
      value.tariff, value.mintedCredit, value.birthFee, value.membershipCredit, value.creditedRemainder))
    (fun (authorization, terms, amount, tariff, credit, birth, membership, remainder) =>
      ⟨authorization, terms, amount, tariff, credit, birth, membership, remainder⟩)
    (by intro value; cases value; rfl)

def consumptionFrame : List UInt8 := PayReceivingContract.consumptionFrame

def consumptionCodec : LawfulCodec Consumption := framed consumptionFrame consumptionStream

theorem consumption_roundtrip (value : Consumption) :
    consumptionCodec.decode (consumptionCodec.encode value) = some value :=
  consumptionCodec.decode_encode value

theorem consumption_canonical {bytes : List UInt8} {value : Consumption}
    (decoded : consumptionCodec.decode bytes = some value) :
    consumptionCodec.encode value = bytes :=
  framed_canonical consumptionFrame consumptionStream decoded


/-- Includes the deposit id so two original-memo admissions never share an
identity merely because both use the originalMemo tag. -/
def Consumption.acceptanceIdentity (consumed : Consumption) : List UInt8 :=
  (StreamCodec.product bytesStream authorizationStream).encode
    (consumed.claimId, consumed.authorization)

/-- The cross-namespace law obligation, stated without importing the pay store. -/
def Consumption.matchesClaim (consumed : Consumption) (claim : Claim) : Prop :=
  consumed.claimId = claim.id ∧
  consumed.ownerIdentityKey = claim.ownerIdentityKey ∧
  consumed.originalAmountAtomic = claim.original.amountAtomic

instance (consumed : Consumption) (claim : Claim) :
    Decidable (consumed.matchesClaim claim) := by
  unfold Consumption.matchesClaim
  infer_instance

theorem claim_id_length (claim : Claim) (valid : claim.original.valid) :
    claim.id.length = 102 := by
  rcases valid with ⟨signature, recipient, rest⟩
  simp [Claim.id, soltxPrefix, signature, recipient]

/-! ## Explicit-duration fixed-deposit quote -/

inductive QuoteReject where
  | tariffInvalid
  | emptyDeposit
  | observationCapExceeded
  | weeksZero
  | insufficientCredit
  deriving DecidableEq, Repr

structure FixedQuote where
  amountAtomic : Nat
  credit : Nat
  birthFee : Nat
  requestedWeeks : Nat
  membershipCredit : Nat
  creditedRemainder : Nat
  minimumStarterCredit : Nat
  deriving DecidableEq, Repr

/-- V2 consumes only the signed requested number of weeks. Every remaining
credit is spendable, even if the remainder could buy another week. This does
not modify v1's floor-all-weeks admission arithmetic.

A retained amount above the current cap refuses: never discard part of an
already-paid claim to make a newer cap fit. Source quotes report the current
cap/rate and acceptance binds that exact pricing commitment. -/
def quoteFixed (amount : Nat) (tariff : Tariff)
    (birthFee requestedWeeks minimumStarterCredit : Nat) : Except QuoteReject FixedQuote :=
  if ¬tariff.valid then .error .tariffInvalid
  else if amount = 0 then .error .emptyDeposit
  else if tariff.maxPerObservation < amount then .error .observationCapExceeded
  else if requestedWeeks = 0 then .error .weeksZero
  else
    let credit := tariff.creditFor amount
    let membership := requestedWeeks * tariff.weekCredit
    if credit < birthFee + membership + minimumStarterCredit then .error .insufficientCredit
    else .ok {
      amountAtomic := amount
      credit := credit
      birthFee := birthFee
      requestedWeeks := requestedWeeks
      membershipCredit := membership
      creditedRemainder := credit - birthFee - membership
      minimumStarterCredit := minimumStarterCredit }

def quoteClaim (claim : Claim) (tariff : Tariff)
    (birthFee requestedWeeks minimumStarterCredit : Nat) : Except QuoteReject FixedQuote :=
  quoteFixed claim.original.amountAtomic tariff birthFee requestedWeeks minimumStarterCredit

/-- Successful fixed quotes partition the one credit and retain the chosen
duration/starter, as consequences of the actual implementation. -/
theorem quoteFixed_success_split (amount : Nat) (tariff : Tariff)
    (birthFee weeks starter : Nat) (quoted : FixedQuote)
    (accepted : quoteFixed amount tariff birthFee weeks starter = .ok quoted) :
    quoted.amountAtomic = amount ∧ quoted.credit = tariff.creditFor amount ∧
    quoted.birthFee = birthFee ∧ quoted.requestedWeeks = weeks ∧
    quoted.membershipCredit = weeks * tariff.weekCredit ∧
    quoted.birthFee + quoted.membershipCredit + quoted.creditedRemainder = quoted.credit ∧
    starter ≤ quoted.creditedRemainder := by
  unfold quoteFixed at accepted
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
  rename_i covered
  have coverage : birthFee + weeks * tariff.weekCredit + starter ≤ tariff.creditFor amount := by
    change ¬tariff.creditFor amount < birthFee + weeks * tariff.weekCredit + starter at covered
    omega
  injection accepted with same
  subst quoted
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, by omega⟩

theorem quoteFixed_over_cap (amount : Nat) (tariff : Tariff)
    (birthFee weeks starter : Nat) (valid : tariff.valid) (nonzero : amount ≠ 0)
    (over : tariff.maxPerObservation < amount) :
    quoteFixed amount tariff birthFee weeks starter = .error .observationCapExceeded := by
  simp [quoteFixed, valid, nonzero, over]

/-! ## Current-custody authorization and one-time acceptance -/

inductive Reject where
  | alreadyConsumed
  | notPending
  | ownerIdentityMismatch
  | authorityEpochMismatch
  | authorizingKeyMismatch
  | malformedClaim
  | malformedOwner
  | malformedRequest
  | claimIdMismatch
  | modeMismatch
  | renewalBirthFee
  | assetMismatch
  | termsStale
  | expired
  | quote (reason : QuoteReject)
  deriving DecidableEq, Repr

/-- These comparisons are necessary AFTER signature verification by Checked.
They cannot authenticate arbitrary unverified data by themselves. -/
def authorize (owner : CurrentOwner) (request : AcceptRequest) : Except Reject Unit :=
  if request.ownerIdentityKey ≠ owner.identityKey then .error .ownerIdentityMismatch
  else if request.authorityEpoch ≠ owner.epoch then .error .authorityEpochMismatch
  else if request.authorizingKey ≠ owner.currentKey then .error .authorizingKeyMismatch
  else .ok ()

theorem authorize_success (owner : CurrentOwner) (request : AcceptRequest)
    (accepted : authorize owner request = .ok ()) :
    request.ownerIdentityKey = owner.identityKey ∧
    request.authorityEpoch = owner.epoch ∧ request.authorizingKey = owner.currentKey := by
  unfold authorize at accepted
  split at accepted
  · cases accepted
  rename_i identity
  split at accepted
  · cases accepted
  rename_i epoch
  split at accepted
  · cases accepted
  rename_i key
  exact ⟨by simpa using identity, by simpa using epoch, by simpa using key⟩

/-- The receiver supplies current mode, birth fee and pricing commitment from
the loaded source recomputation. Processing hour is the authenticated finalized
tip hour, never native wall time. The signed expiry hour is inclusive. -/
def checkClaim (claim : Claim) (owner : CurrentOwner) (tariff : Tariff)
    (birthFee : Nat) (expectedMode : Mode) (expectedPricing : Digest)
    (processingHour : Nat) (request : AcceptRequest) : Except Reject Unit :=
  match authorize owner request with
  | .error reason => .error reason
  | .ok _ =>
    if ¬claim.valid then .error .malformedClaim
    else if claim.reason.isNone then .error .notPending
    else if ¬owner.valid then .error .malformedOwner
    else if ¬request.valid then .error .malformedRequest
    else if owner.identityKey ≠ claim.ownerIdentityKey then .error .ownerIdentityMismatch
    else if request.claimId ≠ claim.id then .error .claimIdMismatch
    else if request.mode ≠ expectedMode then .error .modeMismatch
    else if request.mode = .renew ∧ birthFee ≠ 0 then .error .renewalBirthFee
    else if claim.original.mint ≠ tariff.mint ∨ claim.original.tokenProgram ≠ tariff.tokenProgram then
      .error .assetMismatch
    else if request.pricingCommitment ≠ expectedPricing then .error .termsStale
    else if request.expiresAtProcessingChainHour < processingHour then .error .expired
    else .ok ()

/-- Successful source checks bind the request to this immutable claim and
preserve its stable identity even when current custody has rotated. -/
theorem checkClaim_success_identity (claim : Claim) (owner : CurrentOwner)
    (tariff : Tariff) (birthFee : Nat) (mode : Mode) (pricing : Digest)
    (hour : Nat) (request : AcceptRequest)
    (accepted : checkClaim claim owner tariff birthFee mode pricing hour request = .ok ()) :
    request.claimId = claim.id ∧ request.ownerIdentityKey = claim.ownerIdentityKey ∧
    request.mode = mode := by
  cases authorized : authorize owner request with
  | error reason => simp [checkClaim, authorized] at accepted
  | ok unit =>
    cases unit
    have authority := authorize_success owner request authorized
    simp only [checkClaim, authorized] at accepted
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
    rename_i ownerMatches
    split at accepted
    · cases accepted
    rename_i idMatches
    split at accepted
    · cases accepted
    rename_i modeMatches
    split at accepted
    · cases accepted
    split at accepted
    · cases accepted
    split at accepted
    · cases accepted
    split at accepted
    · cases accepted
    exact ⟨by simpa using idMatches,
      authority.1.trans (by simpa using ownerMatches), by simpa using modeMatches⟩

theorem checkClaim_success_pending (claim : Claim) (owner : CurrentOwner)
    (tariff : Tariff) (birth : Nat) (mode : Mode) (pricing : Digest) (hour : Nat)
    (request : AcceptRequest)
    (accepted : checkClaim claim owner tariff birth mode pricing hour request = .ok ()) :
    claim.reason.isSome = true := by
  cases reason : claim.reason with
  | some why => simp [reason]
  | none =>
    cases authorized : authorize owner request with
    | error why => simp [checkClaim, authorized] at accepted
    | ok unit =>
      simp only [checkClaim, authorized, reason, Option.isNone_none, if_true] at accepted
      split at accepted <;> cases accepted

private def consumptionOf (claim : Claim) (tariff : Tariff)
    (request : AcceptRequest) (quote : FixedQuote) : Consumption :=
  { authorization := .acceptCurrentQuote request
    terms := request.terms
    originalAmountAtomic := claim.original.amountAtomic
    tariff := tariff
    mintedCredit := quote.credit
    birthFee := quote.birthFee
    membershipCredit := quote.membershipCredit
    creditedRemainder := quote.creditedRemainder }

/-- Builds the single proposed append-only consumption row. The caller must
atomically install it WITH the Book mint and selected enrollment/renewal patch;
a standalone successful return is not a state transition or a credit.

Any stored consumption refuses, even when the new request is identical. Exact
retry lookup returns the immutable prior row before attempting this gate. -/
def accept (claim : Claim) (consumed : Option Consumption) (owner : CurrentOwner)
    (tariff : Tariff) (birthFee : Nat) (expectedMode : Mode)
    (expectedPricing : Digest) (processingHour : Nat) (request : AcceptRequest) :
    Except Reject Consumption :=
  match consumed with
  | some _ => .error .alreadyConsumed
  | none =>
    match checkClaim claim owner tariff birthFee expectedMode expectedPricing processingHour request with
    | .error reason => .error reason
    | .ok _ =>
      match quoteClaim claim tariff birthFee request.requestedWeeks request.minimumStarterCredit with
      | .error reason => .error (.quote reason)
      | .ok quote => .ok (consumptionOf claim tariff request quote)

theorem consumed_refuses (claim : Claim) (consumed : Consumption) (owner : CurrentOwner)
    (tariff : Tariff) (birthFee : Nat) (mode : Mode) (pricing : Digest)
    (hour : Nat) (request : AcceptRequest) :
    accept claim (some consumed) owner tariff birthFee mode pricing hour request =
      .error .alreadyConsumed := rfl

/-- A successful gate has exactly the retained deposit's credit, split once,
and keeps the complete signed acceptance identity unchanged. -/
theorem accept_success_split (claim : Claim) (prior : Option Consumption)
    (owner : CurrentOwner) (tariff : Tariff) (birthFee : Nat) (mode : Mode)
    (pricing : Digest) (hour : Nat) (request : AcceptRequest) (consumed : Consumption)
    (accepted : accept claim prior owner tariff birthFee mode pricing hour request = .ok consumed) :
    consumed.authorization = .acceptCurrentQuote request ∧ consumed.terms = request.terms ∧
    consumed.originalAmountAtomic = claim.original.amountAtomic ∧ consumed.tariff = tariff ∧
    consumed.mintedCredit = tariff.creditFor claim.original.amountAtomic ∧
    consumed.birthFee = birthFee ∧
    consumed.membershipCredit = request.requestedWeeks * tariff.weekCredit ∧
    consumed.birthFee + consumed.membershipCredit + consumed.creditedRemainder = consumed.mintedCredit ∧
    request.minimumStarterCredit ≤ consumed.creditedRemainder := by
  cases prior with
  | some previous => simp [accept] at accepted
  | none =>
    cases checked : checkClaim claim owner tariff birthFee mode pricing hour request with
    | error reason => simp [accept, checked] at accepted
    | ok unit =>
      cases quoted : quoteClaim claim tariff birthFee request.requestedWeeks request.minimumStarterCredit with
      | error reason => simp [accept, checked, quoted] at accepted
      | ok quote =>
        have facts := quoteFixed_success_split claim.original.amountAtomic tariff birthFee
          request.requestedWeeks request.minimumStarterCredit quote quoted
        simp only [accept, checked, quoted, Except.ok.injEq] at accepted
        subst consumed
        exact ⟨rfl, rfl, rfl, rfl, facts.2.1, facts.2.2.1,
          facts.2.2.2.2.1, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2⟩

theorem accept_success_matchesClaim (claim : Claim) (prior : Option Consumption)
    (owner : CurrentOwner) (tariff : Tariff) (birthFee : Nat) (mode : Mode)
    (pricing : Digest) (hour : Nat) (request : AcceptRequest) (consumed : Consumption)
    (accepted : accept claim prior owner tariff birthFee mode pricing hour request = .ok consumed) :
    consumed.matchesClaim claim := by
  cases prior with
  | some previous => simp [accept] at accepted
  | none =>
    cases checked : checkClaim claim owner tariff birthFee mode pricing hour request with
    | error reason => simp [accept, checked] at accepted
    | ok unit =>
      cases unit
      have identity := checkClaim_success_identity claim owner tariff birthFee mode pricing hour request checked
      cases quoted : quoteClaim claim tariff birthFee request.requestedWeeks request.minimumStarterCredit with
      | error reason => simp [accept, checked, quoted] at accepted
      | ok quote =>
        simp only [accept, checked, quoted, Except.ok.injEq] at accepted
        subst consumed
        exact ⟨identity.1, identity.2.1, rfl⟩

theorem old_epoch_refuses (claim : Claim) (owner : CurrentOwner) (tariff : Tariff)
    (birthFee : Nat) (mode : Mode) (pricing : Digest) (hour : Nat) (request : AcceptRequest)
    (identity : request.ownerIdentityKey = owner.identityKey)
    (stale : request.authorityEpoch ≠ owner.epoch) :
    accept claim none owner tariff birthFee mode pricing hour request =
      .error .authorityEpochMismatch := by
  simp [accept, checkClaim, authorize, identity, stale]

theorem wrong_key_refuses (claim : Claim) (owner : CurrentOwner) (tariff : Tariff)
    (birthFee : Nat) (mode : Mode) (pricing : Digest) (hour : Nat) (request : AcceptRequest)
    (identity : request.ownerIdentityKey = owner.identityKey)
    (epoch : request.authorityEpoch = owner.epoch)
    (wrong : request.authorizingKey ≠ owner.currentKey) :
    accept claim none owner tariff birthFee mode pricing hour request =
      .error .authorizingKeyMismatch := by
  simp [accept, checkClaim, authorize, identity, epoch, wrong]

/-- An original immediate-admission index row is never a fresh acceptance
opportunity, even if a caller supplies an invalid partial store with no consumption. -/
theorem original_origin_not_pending (claim : Claim) (owner : CurrentOwner) (tariff : Tariff)
    (birth : Nat) (mode : Mode) (pricing : Digest) (hour : Nat) (request : AcceptRequest)
    (authorized : authorize owner request = .ok ()) (valid : claim.valid)
    (original : claim.reason = none) :
    accept claim none owner tariff birth mode pricing hour request = .error .notPending := by
  simp [accept, checkClaim, authorized, valid, original]

/-- Only the patch constructor after the existing KeyPreRotation.gate accepted
the precommitted successor. This is NOT a parallel rotation authorization gate.
The receiver owns the exact transition nonce and new-key Checked signature. -/
def rotatedOwner (owner : PendingOwner) (newKey : List UInt8) (newNext : Digest) : PendingOwner :=
  { owner with currentKey := newKey, epoch := owner.epoch + 1, nextKeyDigest := newNext }

theorem rotation_preserves_identity (owner : PendingOwner) (newKey : List UInt8) (newNext : Digest) :
    (rotatedOwner owner newKey newNext).identityKey = owner.identityKey := rfl

theorem old_epoch_after_rotation_refuses (owner : PendingOwner) (newKey : List UInt8)
    (newNext : Digest) (request : AcceptRequest)
    (identity : request.ownerIdentityKey = owner.identityKey)
    (epoch : request.authorityEpoch = owner.epoch) :
    authorize (rotatedOwner owner newKey newNext).toCurrentOwner request = .error .authorityEpochMismatch := by
  simp [authorize, rotatedOwner, PendingOwner.toCurrentOwner, identity, epoch]

/-- Acceptance authority does not smuggle a NEXT commitment into a legacy
registry owner. Only these three fields participate in authorization. -/
theorem authorize_current_identity (owner : CurrentOwner) (request : AcceptRequest)
    (identity : request.ownerIdentityKey = owner.identityKey)
    (epoch : request.authorityEpoch = owner.epoch)
    (key : request.authorizingKey = owner.currentKey) :
    authorize owner request = .ok () := by
  simp [authorize, identity, epoch, key]

/-- Altering NEXT does not change the acceptance authority projection. Rotation
itself still has to pass the separate precommitted-successor gate. -/
theorem pending_next_not_acceptance_authority (owner : PendingOwner) (next : Digest) :
    ({ owner with nextKeyDigest := next }).toCurrentOwner = owner.toCurrentOwner := rfl

/-! ## Concrete quote poles: no signature oracle or invented admission witness -/

private def fixtureTariff : Tariff :=
  { exampleTariff with version := 3, creditPerAtomic := 1, maxPerObservation := 100000,
      nodeHourRate := 1, enrolIndex := some 0, journalFloor := 1 }

/-- 343 credits after a nonzero birth fee: one requested week leaves a full
175 credits spendable. V1 would have consumed two weeks. -/
theorem fixed_deposit_does_not_buy_unsolicited_weeks :
    quoteFixed 350 fixtureTariff 7 1 175 =
      .ok ⟨350, 350, 7, 1, 168, 175, 175⟩ := by decide

theorem fixed_deposit_can_choose_two_weeks :
    quoteFixed 350 fixtureTariff 7 2 7 =
      .ok ⟨350, 350, 7, 2, 336, 7, 7⟩ := by decide

theorem starter_above_one_week_is_not_silently_spent :
    quoteFixed 1000 fixtureTariff 7 1 800 =
      .ok ⟨1000, 1000, 7, 1, 168, 825, 800⟩ := by decide

theorem changed_cap_never_discards_claim_value :
    quoteFixed 350 { fixtureTariff with maxPerObservation := 349 } 7 1 0 =
      .error .observationCapExceeded := by decide

theorem insufficient_fixed_deposit_remains_unconsumed :
    quoteFixed 350 fixtureTariff 7 2 8 = .error .insufficientCredit := by decide

theorem fixed_quote_uses_current_rate_explicitly :
    quoteFixed 200 { fixtureTariff with creditPerAtomic := 2 } 7 1 225 =
      .ok ⟨200, 400, 7, 1, 168, 225, 225⟩ := by decide

theorem renewal_has_no_birth_charge :
    quoteFixed 350 fixtureTariff 0 2 14 =
      .ok ⟨350, 350, 0, 2, 336, 14, 14⟩ := by decide

#assert_axioms AcceptRequest.terms_valid
#assert_axioms checkClaim_success_pending
#assert_axioms original_origin_not_pending
#assert_axioms PendingOwner.toCurrentOwner_valid
#assert_axioms pending_projection_preserves_identity
#assert_axioms authorize_current_identity
#assert_axioms pending_next_not_acceptance_authority
#assert_axioms observation_roundtrip
#assert_axioms observation_canonical
#assert_axioms claim_roundtrip
#assert_axioms claim_canonical
#assert_axioms pendingOwner_roundtrip
#assert_axioms pendingOwner_canonical
#assert_axioms acceptRequest_roundtrip
#assert_axioms acceptRequest_canonical
#assert_axioms consumption_roundtrip
#assert_axioms consumption_canonical
#assert_axioms claim_id_length
#assert_axioms quoteFixed_success_split
#assert_axioms quoteFixed_over_cap
#assert_axioms authorize_success
#assert_axioms checkClaim_success_identity
#assert_axioms consumed_refuses
#assert_axioms accept_success_split
#assert_axioms accept_success_matchesClaim
#assert_axioms old_epoch_refuses
#assert_axioms wrong_key_refuses
#assert_axioms rotation_preserves_identity
#assert_axioms old_epoch_after_rotation_refuses
#assert_axioms fixed_deposit_does_not_buy_unsolicited_weeks
#assert_axioms fixed_deposit_can_choose_two_weeks
#assert_axioms starter_above_one_week_is_not_silently_spent
#assert_axioms changed_cap_never_discards_claim_value
#assert_axioms insufficient_fixed_deposit_remains_unconsumed
#assert_axioms fixed_quote_uses_current_rate_explicitly
#assert_axioms renewal_has_no_birth_charge

end Minidregg.Kernel.PayEnrolClaim
