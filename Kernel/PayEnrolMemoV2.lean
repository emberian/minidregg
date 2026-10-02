/-
# Quote-bound paid enrollment memo, version 2

The receiver migration is deliberately separate. This module owns the exact
357-byte / 485-ASCII codec and the bytes signed by BOTH possession keys.
Canonical integers are fixed-width little endian; unbounded source values must
pass WellFormed before encoding for transport. Nothing here reserves a price,
verifies a signature, or treats a digest as mathematically collision-free.
-/
import Kernel.PayEnrolMemo
import Compiler.SigningKeyCommitment

namespace Minidregg.Kernel.PayEnrolMemoV2

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest)
open PayEnrolMemo (b64Encode b64Decode cut cut_append)

set_option autoImplicit false

/-! ## Fixed-width scalars, shared with the source digest representation -/

def encodeLE (width value : Nat) : List UInt8 :=
  (Bignum.digitsLE 256 width value).map UInt8.ofNat

def decodeLE (bytes : List UInt8) : Nat :=
  Bignum.denoteNat 256 (bytes.map UInt8.toNat)

@[simp] theorem encodeLE_length (width value : Nat) :
    (encodeLE width value).length = width := by simp [encodeLE]

theorem decodeLE_encodeLE (width value : Nat) (bound : value < 256 ^ width) :
    decodeLE (encodeLE width value) = value := by
  unfold decodeLE encodeLE
  rw [List.map_map]
  have hmap :
      (Bignum.digitsLE 256 width value).map
        (fun digit => (UInt8.ofNat digit).toNat) = Bignum.digitsLE 256 width value := by
    have hcongr := List.map_congr_left
      (l := Bignum.digitsLE 256 width value)
      (f := fun digit => (UInt8.ofNat digit).toNat) (g := id)
      (fun digit member => UInt8.toNat_ofNat_of_lt
        (Bignum.digitsLE_ranged (by decide) width value digit member))
    simpa only [List.map_id, id_eq] using hcongr
  rw [hmap]
  exact Bignum.denoteNat_digitsLE (by decide) width value bound

/-- Fixed digest bytes are exactly the existing cSHAKE source representation.
The variable-width escape branch of its total codec is NOT legal in this memo. -/
theorem digest_representation (digest : Digest) (bound : digest.value < 256 ^ 32) :
    encodeLE 32 digest.value = Sp800185Cshake256.digestBytesLE digest := by
  simp [Sp800185Cshake256.digestBytesLE, bound,
    Sp800185Cshake256.fixedDigestBytesLE, encodeLE]

inductive Mode where
  | enroll | renew | renewWithoutCommitment
  deriving DecidableEq, Repr

/-- Mode 3 binds an existing unprerotated registry key. It never creates one. -/
def Mode.byte : Mode → UInt8
  | .enroll => 1 | .renew => 2 | .renewWithoutCommitment => 3

def Mode.parse : List UInt8 → Option Mode
  | [1] => some .enroll
  | [2] => some .renew
  | [3] => some .renewWithoutCommitment
  | _ => none

@[simp] theorem Mode.parse_byte (mode : Mode) : Mode.parse [mode.byte] = some mode := by
  cases mode <;> rfl

structure Unsigned where
  mode : Mode
  deploymentCommitment : Digest
  pricingCommitment : Digest
  enrollmentIdentityKey : List UInt8
  authorizingKey : List UInt8
  authorityEpoch : Nat
  sshKey : List UInt8
  nextKeyDigest : Digest
  weeks : Nat
  minimumStarterCredit : Nat
  expiresAtProcessingChainHour : Nat
  amountAtomic : Nat
  deriving DecidableEq, Repr

/-- These checks prevent truncation, including the source's unbounded Digest
carrier. Renewal ownership is a receiver check against the current registry. -/
def Unsigned.Shape (value : Unsigned) : Prop :=
  value.deploymentCommitment.value < 256 ^ 32 ∧
  value.pricingCommitment.value < 256 ^ 32 ∧
  value.enrollmentIdentityKey.length = 32 ∧
  value.authorizingKey.length = 32 ∧
  value.authorityEpoch < 256 ^ 8 ∧
  value.sshKey.length = 32 ∧
  value.nextKeyDigest.value < 256 ^ 32 ∧
  value.weeks < 256 ^ 4 ∧
  value.minimumStarterCredit < 256 ^ 8 ∧
  value.expiresAtProcessingChainHour < 256 ^ 8 ∧
  value.amountAtomic < 256 ^ 8

def Unsigned.WellFormed (value : Unsigned) : Prop :=
  value.Shape ∧ 0 < value.authorityEpoch ∧ 0 < value.weeks ∧
  (value.mode = .enroll →
    value.authorizingKey = value.enrollmentIdentityKey ∧ value.authorityEpoch = 1) ∧
  (value.mode = .renewWithoutCommitment → value.nextKeyDigest = ⟨0⟩)

/-- The optional state that the signed mode/digest pair declares. `None` and
`Some(0)` have different mode bytes; zero is not a reserved digest value. -/
def Unsigned.declaredNext (value : Unsigned) : Option Digest :=
  match value.mode with
  | .enroll | .renew => some value.nextKeyDigest
  | .renewWithoutCommitment => none

instance (value : Unsigned) : Decidable value.Shape := by
  unfold Unsigned.Shape; infer_instance
instance (value : Unsigned) : Decidable value.WellFormed := by
  unfold Unsigned.WellFormed; infer_instance

/-- Every field through amount, in the adopted contract's order. -/
def unsignedParts (value : Unsigned) : List (List UInt8) :=
  [[value.mode.byte], encodeLE 32 value.deploymentCommitment.value,
    encodeLE 32 value.pricingCommitment.value, value.enrollmentIdentityKey,
    value.authorizingKey, encodeLE 8 value.authorityEpoch, value.sshKey,
    encodeLE 32 value.nextKeyDigest.value, encodeLE 4 value.weeks,
    encodeLE 8 value.minimumStarterCredit, encodeLE 8 value.expiresAtProcessingChainHour]

def unsignedWidths : List Nat := [1, 32, 32, 32, 32, 8, 32, 32, 4, 8, 8]
def unsignedLength : Nat := 229

def unsignedBytes (value : Unsigned) : List UInt8 :=
  (unsignedParts value).flatten ++ encodeLE 8 value.amountAtomic

/-- Decoding alone does not admit a payment. `parse` checks shape, semantic
initial-enrollment constraints, and canonical spelling after this operation. -/
def decodeUnsigned (bytes : List UInt8) : Option Unsigned :=
  match cut unsignedWidths bytes with
  | [mode, deployment, pricing, identity, authorizing, epoch, ssh, next, weeks,
      starter, expiry, amount] => do
      let mode ← Mode.parse mode
      pure ⟨mode, ⟨decodeLE deployment⟩, ⟨decodeLE pricing⟩, identity,
        authorizing, decodeLE epoch, ssh, ⟨decodeLE next⟩, decodeLE weeks,
        decodeLE starter, decodeLE expiry, decodeLE amount⟩
  | _ => none

theorem unsignedParts_lengths {value : Unsigned} (shape : value.Shape) :
    (unsignedParts value).map List.length = unsignedWidths := by
  rcases shape with ⟨hd, hp, hi, ha, he, hs, hn, hw, hst, hex, ham⟩
  simp [unsignedParts, unsignedWidths, hi, ha, hs]

theorem unsignedBytes_length {value : Unsigned} (shape : value.Shape) :
    (unsignedBytes value).length = unsignedLength := by
  rcases shape with ⟨hd, hp, hi, ha, he, hs, hn, hw, hst, hex, ham⟩
  simp [unsignedBytes, unsignedParts, unsignedLength, hi, ha, hs]

theorem decodeUnsigned_unsignedBytes {value : Unsigned} (shape : value.Shape) :
    decodeUnsigned (unsignedBytes value) = some value := by
  have pieces := cut_append unsignedWidths (unsignedParts value)
    (encodeLE 8 value.amountAtomic) (unsignedParts_lengths shape)
  rcases shape with ⟨hd, hp, hi, ha, he, hs, hn, hw, hst, hex, ham⟩
  unfold decodeUnsigned unsignedBytes
  rw [pieces]
  simp only [unsignedParts, List.cons_append, List.nil_append,
    Mode.parse_byte, Option.bind_some, decodeLE_encodeLE _ _ hd,
    decodeLE_encodeLE _ _ hp, decodeLE_encodeLE _ _ he,
    decodeLE_encodeLE _ _ hn, decodeLE_encodeLE _ _ hw,
    decodeLE_encodeLE _ _ hst, decodeLE_encodeLE _ _ hex,
    decodeLE_encodeLE _ _ ham]
  cases value
  rfl

/-- An actual byte equality recovers every unsigned field, without any hash
collision assumption. In particular identity and authorizing key stay distinct. -/
theorem unsignedBytes_injective {left right : Unsigned}
    (hl : left.Shape) (hr : right.Shape)
    (same : unsignedBytes left = unsignedBytes right) : left = right := by
  have decoded := congrArg decodeUnsigned same
  rw [decodeUnsigned_unsignedBytes hl, decodeUnsigned_unsignedBytes hr] at decoded
  exact Option.some.inj decoded

structure Memo where
  unsigned : Unsigned
  miniSignature : List UInt8
  sshSignature : List UInt8
  deriving DecidableEq, Repr

def Memo.WellFormed (memo : Memo) : Prop :=
  memo.unsigned.WellFormed ∧ memo.miniSignature.length = 64 ∧ memo.sshSignature.length = 64

instance (memo : Memo) : Decidable memo.WellFormed := by
  unfold Memo.WellFormed; infer_instance

def binaryLength : Nat := 357
def memoLength : Nat := 485
def prefix : List UInt8 := "enrol:v2:".toUTF8.toList

def binary (memo : Memo) : List UInt8 :=
  [unsignedBytes memo.unsigned, memo.miniSignature].flatten ++ memo.sshSignature

def encode (memo : Memo) : List UInt8 := prefix ++ b64Encode (binary memo)

def decodeBinary (bytes : List UInt8) : Option Memo :=
  match cut [unsignedLength, 64] bytes with
  | [unsigned, miniSig, sshSig] => do
      let value ← decodeUnsigned unsigned
      pure ⟨value, miniSig, sshSig⟩
  | _ => none

def rawParse (bytes : List UInt8) : Option Memo :=
  match cut [prefix.length] bytes with
  | [tag, body] =>
      if tag = prefix then b64Decode body >>= decodeBinary else none
  | _ => none

inductive Refusal where
  | shape | invalidFields | noncanonical
  deriving DecidableEq, Repr

/-- No padding, whitespace, alternative alphabet, overflow, version alias or
extra field is admitted. The re-encode guard also makes strictness explicit to
all future callers; roundtrip is independently proved below. -/
def parse (bytes : List UInt8) : Except Refusal Memo :=
  match rawParse bytes with
  | none => .error .shape
  | some memo =>
      if memo.WellFormed then
        if encode memo = bytes then .ok memo else .error .noncanonical
      else .error .invalidFields

/-- The public construction seam refuses out-of-range source values before
encoding. In particular no caller should send a truncated Nat or Digest. -/
def encodeChecked (memo : Memo) : Except Refusal (List UInt8) :=
  if memo.WellFormed then .ok (encode memo) else .error .invalidFields

theorem binary_length {memo : Memo} (wf : memo.WellFormed) :
    (binary memo).length = binaryLength := by
  simp [binary, unsignedBytes_length wf.1.1, wf.2.1, wf.2.2,
    unsignedLength, binaryLength]

theorem encode_length {memo : Memo} (wf : memo.WellFormed) :
    (encode memo).length = memoLength := by
  have divisible : (binary memo).length % 3 = 0 := by rw [binary_length wf]; decide
  rw [encode, List.length_append, PayEnrolMemo.b64Encode_length _ divisible, binary_length wf]
  rfl

theorem decodeBinary_binary {memo : Memo} (wf : memo.WellFormed) :
    decodeBinary (binary memo) = some memo := by
  have pieces := cut_append [unsignedLength, 64]
    [unsignedBytes memo.unsigned, memo.miniSignature] memo.sshSignature
    (by simp [unsignedBytes_length wf.1.1, wf.2.1])
  unfold decodeBinary binary
  rw [pieces]
  simp only [decodeUnsigned_unsignedBytes wf.1.1, Option.bind_some]
  cases memo; rfl

theorem rawParse_encode {memo : Memo} (wf : memo.WellFormed) :
    rawParse (encode memo) = some memo := by
  have pieces := cut_append [prefix.length] [prefix] (b64Encode (binary memo)) (by simp)
  have divisible : (binary memo).length % 3 = 0 := by rw [binary_length wf]; decide
  unfold rawParse encode
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at pieces
  rw [pieces]
  simp [PayEnrolMemo.b64Decode_b64Encode _ divisible, decodeBinary_binary wf]

/-- Every well-formed source value is accepted with every field intact. -/
theorem parse_encode {memo : Memo} (wf : memo.WellFormed) :
    parse (encode memo) = .ok memo := by
  simp [parse, rawParse_encode wf, wf]

/-- Every accepted text is precisely the canonical spelling of a well-formed
value. This is not a promise that its two signatures have been verified. -/
theorem parse_canonical {bytes : List UInt8} {memo : Memo}
    (accepted : parse bytes = .ok memo) : encode memo = bytes ∧ memo.WellFormed := by
  unfold parse at accepted
  split at accepted
  · simp at accepted
  next candidate decoded =>
    split at accepted
    next wf =>
      split at accepted
      next canonical =>
        simp only [Except.ok.injEq] at accepted
        subst memo
        exact ⟨canonical, wf⟩
      · simp at accepted
    · simp at accepted

theorem parse_encodeChecked {memo : Memo} {bytes : List UInt8}
    (constructed : encodeChecked memo = .ok bytes) : parse bytes = .ok memo := by
  unfold encodeChecked at constructed
  split at constructed
  next wf =>
    simp only [Except.ok.injEq] at constructed
    rw [← constructed]
    exact parse_encode wf
  · simp at constructed

theorem accepted_length {bytes : List UInt8} {memo : Memo}
    (accepted : parse bytes = .ok memo) : bytes.length = memoLength := by
  obtain ⟨canonical, wf⟩ := parse_canonical accepted
  rw [← canonical]
  exact encode_length wf

/-! ## Same complete unsigned frame for both signatures -/

structure Context where
  mint : List UInt8
  tokenProgram : List UInt8
  enrollmentRecipient : List UInt8
  deriving DecidableEq, Repr

def Context.WellFormed (context : Context) : Prop :=
  context.mint.length = 32 ∧ context.tokenProgram.length = 32 ∧
    context.enrollmentRecipient.length = 32

/-- No cSHAKE prehash is inserted into Ed25519 or SSHSIG signing. The commitments
inside the value are source cSHAKE outputs; both signatures bind their exact bytes. -/
def possessionTag : List UInt8 := "DREGG/PAY/ENROL/POSSESSION/v2".toUTF8.toList

def unsignedFrame (context : Context) (value : Unsigned) : List UInt8 :=
  [possessionTag, unsignedBytes value, context.mint, context.tokenProgram].flatten ++
    context.enrollmentRecipient

def miniFrame (context : Context) (memo : Memo) : List UInt8 :=
  unsignedFrame context memo.unsigned

def sshsigNamespace : List UInt8 := "dregg-enrol@v2".toUTF8.toList

def sshsigMessage (context : Context) (memo : Memo) : List UInt8 :=
  unsignedFrame context memo.unsigned

def sshsigSignedData (sha512OfMessage : List UInt8) : List UInt8 :=
  PayEnrolMemo.sshsigSignedData sshsigNamespace sha512OfMessage

theorem both_sign_same_unsigned_frame (context : Context) (memo : Memo) :
    miniFrame context memo = sshsigMessage context memo := rfl

/-- A left inverse of the raw frame, used only to establish byte binding. -/
def decodeFrame (bytes : List UInt8) : Option (Context × Unsigned) :=
  match cut [possessionTag.length, unsignedLength, 32, 32] bytes with
  | [_, value, mint, program, recipient] => do
      let value ← decodeUnsigned value
      pure (⟨mint, program, recipient⟩, value)
  | _ => none

theorem decodeFrame_unsignedFrame {context : Context} {value : Unsigned}
    (hc : context.WellFormed) (hv : value.Shape) :
    decodeFrame (unsignedFrame context value) = some (context, value) := by
  have pieces := cut_append [possessionTag.length, unsignedLength, 32, 32]
    [possessionTag, unsignedBytes value, context.mint, context.tokenProgram]
    context.enrollmentRecipient
    (by simp [unsignedBytes_length hv, hc.1, hc.2.1])
  unfold decodeFrame unsignedFrame
  rw [pieces]
  simp only [decodeUnsigned_unsignedBytes hv, Option.bind_some]
  cases context; rfl

/-- Byte-level binding of ALL fields and all three asset/recipient identities.
Hash collision resistance and signature unforgeability are separate assumptions. -/
theorem unsignedFrame_injective {c₁ c₂ : Context} {v₁ v₂ : Unsigned}
    (hc₁ : c₁.WellFormed) (hc₂ : c₂.WellFormed) (hv₁ : v₁.Shape) (hv₂ : v₂.Shape)
    (same : unsignedFrame c₁ v₁ = unsignedFrame c₂ v₂) : c₁ = c₂ ∧ v₁ = v₂ := by
  have decoded := congrArg decodeFrame same
  rw [decodeFrame_unsignedFrame hc₁ hv₁, decodeFrame_unsignedFrame hc₂ hv₂] at decoded
  exact Prod.mk.inj (Option.some.inj decoded)

/-- Uses the existing source key-rotation commitment, never a native hash recipe.
It commits to a public next key; no secret key enters this wire representation. -/
def nextKeyCommitment (publicKey : List UInt8) : Digest :=
  SigningKeyCommitment.digest publicKey

/-! ## Decisive wire and semantic poles (not signature-verification fixtures) -/

def fixtureUnsigned : Unsigned :=
  ⟨.enroll, ⟨1⟩, ⟨2⟩, List.replicate 32 3, List.replicate 32 3, 1,
    List.replicate 32 4, ⟨5⟩, 1, 94, 497500, 269⟩
def fixture : Memo := ⟨fixtureUnsigned, List.replicate 64 6, List.replicate 64 7⟩

theorem fixture_wellFormed : fixture.WellFormed := by decide

theorem fixture_roundtrip : parse (encode fixture) = .ok fixture :=
  parse_encode fixture_wellFormed

theorem fixture_lengths : (binary fixture).length = 357 ∧ (encode fixture).length = 485 := by
  exact ⟨binary_length fixture_wellFormed, encode_length fixture_wellFormed⟩

/-- Independent literal wire vector: the full order, widths, integer endian,
alphabet and signature placement are pinned rather than merely roundtripped. -/
def fixtureText : List UInt8 :=
  "enrol:v2:AQEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAwMDAQAAAAAAAAAEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAUAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAF4AAAAAAAAAXJcHAAAAAAANAQAAAAAAAAYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcH".toUTF8.toList

theorem fixture_exact_wire : encode fixture = fixtureText := by decide

theorem fixture_literal_parses : parse fixtureText = .ok fixture := by
  rw [← fixture_exact_wire]
  exact fixture_roundtrip

theorem little_endian_not_network_order : encodeLE 8 72623859790382856 =
    [8, 7, 6, 5, 4, 3, 2, 1] := by decide

theorem unsupported_mode :
    decodeUnsigned (0 :: (unsignedBytes fixtureUnsigned).drop 1) = none := by decide

theorem zero_epoch_refused :
    parse (encode { fixture with unsigned := { fixtureUnsigned with authorityEpoch := 0 } }) =
      .error .invalidFields := by decide

theorem initial_rotated_authorizer_refused :
    parse (encode { fixture with unsigned :=
      { fixtureUnsigned with authorizingKey := List.replicate 32 9 } }) =
      .error .invalidFields := by decide

theorem initial_epoch_two_refused :
    parse (encode { fixture with unsigned := { fixtureUnsigned with authorityEpoch := 2 } }) =
      .error .invalidFields := by decide

def rotatedRenewal : Memo := { fixture with unsigned :=
  { fixtureUnsigned with mode := .renew, authorizingKey := List.replicate 32 9, authorityEpoch := 2 } }

theorem rotated_renewal_roundtrip : parse (encode rotatedRenewal) = .ok rotatedRenewal :=
  parse_encode (by decide)

theorem zero_weeks_refused :
    parse (encode { fixture with unsigned := { fixtureUnsigned with weeks := 0 } }) =
      .error .invalidFields := by decide

theorem digest_overflow_not_wellFormed :
    ¬ ({ fixtureUnsigned with nextKeyDigest := ⟨256 ^ 32⟩ }).WellFormed := by decide

theorem scalar_overflow_not_wellFormed :
    ¬ ({ fixtureUnsigned with amountAtomic := 256 ^ 8 }).WellFormed := by decide

theorem padding_refused : parse (encode fixture ++ [61]) = .error .shape := by decide

theorem old_version_refused :
    parse ("enrol:v1:".toUTF8.toList ++ b64Encode (binary fixture)) = .error .shape := by decide

def fixtureContext : Context :=
  ⟨List.replicate 32 8, List.replicate 32 9, List.replicate 32 10⟩

/-- Changing any unsigned field changes the signed bytes. These are parser/frame
poles; signature rejection itself belongs to the native verifier journey. -/
def unsignedMutations : List Unsigned :=
  [{ fixtureUnsigned with mode := .renew },
   { fixtureUnsigned with deploymentCommitment := ⟨11⟩ },
   { fixtureUnsigned with pricingCommitment := ⟨12⟩ },
   { fixtureUnsigned with enrollmentIdentityKey := List.replicate 32 13 },
   { fixtureUnsigned with authorizingKey := List.replicate 32 14 },
   { fixtureUnsigned with authorityEpoch := 2 },
   { fixtureUnsigned with sshKey := List.replicate 32 15 },
   { fixtureUnsigned with nextKeyDigest := ⟨16⟩ },
   { fixtureUnsigned with weeks := 2 },
   { fixtureUnsigned with minimumStarterCredit := 95 },
   { fixtureUnsigned with expiresAtProcessingChainHour := 497501 },
   { fixtureUnsigned with amountAtomic := 270 }]

theorem all_unsigned_mutations_change_frame :
    unsignedMutations.all (fun value =>
      unsignedFrame fixtureContext value != unsignedFrame fixtureContext fixtureUnsigned) = true := by
  decide

theorem both_signature_fields_are_encoded :
    encode { fixture with miniSignature := List.replicate 64 8 } ≠ encode fixture ∧
    encode { fixture with sshSignature := List.replicate 64 8 } ≠ encode fixture := by decide

theorem checked_digest_overflow_refused :
    encodeChecked { fixture with unsigned :=
      { fixtureUnsigned with nextKeyDigest := ⟨256 ^ 32⟩ } } = .error .invalidFields := by decide

theorem checked_scalar_overflow_refused :
    encodeChecked { fixture with unsigned :=
      { fixtureUnsigned with amountAtomic := 256 ^ 8 } } = .error .invalidFields := by decide

/-! ## Legacy renewal preserves absence of a pre-rotation commitment -/

def unprerotatedRenewal : Memo := { fixture with unsigned :=
  { fixtureUnsigned with mode := .renewWithoutCommitment, nextKeyDigest := ⟨0⟩ } }

def zeroCommittedRenewal : Memo := { fixture with unsigned :=
  { fixtureUnsigned with mode := .renew, nextKeyDigest := ⟨0⟩ } }

theorem unprerotated_renewal_roundtrip :
    parse (encode unprerotatedRenewal) = .ok unprerotatedRenewal :=
  parse_encode (by decide)

theorem zero_committed_renewal_roundtrip :
    parse (encode zeroCommittedRenewal) = .ok zeroCommittedRenewal :=
  parse_encode (by decide)

theorem unprerotated_renewal_lengths :
    (binary unprerotatedRenewal).length = 357 ∧ (encode unprerotatedRenewal).length = 485 := by
  exact ⟨binary_length (by decide), encode_length (by decide)⟩

theorem optional_next_states_have_distinct_wire :
    encode unprerotatedRenewal ≠ encode zeroCommittedRenewal := by decide

theorem optional_next_states_have_distinct_frames :
    miniFrame fixtureContext unprerotatedRenewal ≠
      miniFrame fixtureContext zeroCommittedRenewal := by decide

theorem unprerotated_nonzero_digest_refused :
    parse (encode { fixture with unsigned :=
      { fixtureUnsigned with mode := .renewWithoutCommitment } }) =
        .error .invalidFields := by decide

theorem mode_three_is_not_initial_enrollment :
    unprerotatedRenewal.unsigned.mode ≠ .enroll ∧
    unprerotatedRenewal.unsigned.declaredNext = none ∧
    zeroCommittedRenewal.unsigned.declaredNext = some ⟨0⟩ := by decide

theorem fresh_enrollment_always_declares_commitment (value : Unsigned)
    (initial : value.mode = .enroll) :
    value.declaredNext = some value.nextKeyDigest := by
  simp [Unsigned.declaredNext, initial]

#assert_axioms unprerotated_renewal_roundtrip
#assert_axioms zero_committed_renewal_roundtrip
#assert_axioms unprerotated_renewal_lengths
#assert_axioms optional_next_states_have_distinct_wire
#assert_axioms optional_next_states_have_distinct_frames
#assert_axioms unprerotated_nonzero_digest_refused
#assert_axioms mode_three_is_not_initial_enrollment
#assert_axioms fresh_enrollment_always_declares_commitment
#assert_axioms parse_encodeChecked
#assert_axioms fixture_exact_wire
#assert_axioms fixture_literal_parses
#assert_axioms all_unsigned_mutations_change_frame
#assert_axioms both_signature_fields_are_encoded
#assert_axioms checked_digest_overflow_refused
#assert_axioms checked_scalar_overflow_refused
#assert_axioms decodeLE_encodeLE
#assert_axioms decodeUnsigned_unsignedBytes
#assert_axioms unsignedBytes_injective
#assert_axioms parse_encode
#assert_axioms parse_canonical
#assert_axioms accepted_length
#assert_axioms unsignedFrame_injective
#assert_axioms little_endian_not_network_order
#assert_axioms unsupported_mode
#assert_axioms zero_epoch_refused
#assert_axioms initial_rotated_authorizer_refused
#assert_axioms initial_epoch_two_refused
#assert_axioms rotated_renewal_roundtrip
#assert_axioms zero_weeks_refused
#assert_axioms digest_overflow_not_wellFormed
#assert_axioms scalar_overflow_not_wellFormed
#assert_axioms padding_refused
#assert_axioms old_version_refused

end Minidregg.Kernel.PayEnrolMemoV2
