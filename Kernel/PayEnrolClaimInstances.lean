/-
# Both poles of `Claim.valid` and `Consumption.matchesClaim`, named

`Kernel/PayEnrolClaim.lean` states two receiving-law obligations as
predicates over data:

* `Claim.valid` — the fixed transport shape of an immutable deposit claim
  (a valid observation, a 32-byte owner identity, a full-length memo that
  carries the `enrol:v2:` prefix, an in-range pricing commitment); premise of
  `original_origin_not_pending`;
* `Consumption.matchesClaim` — a consumption row names the claim it consumed
  (claim id, owner identity, original amount); premise of
  `PayClaimStatus.consumed_requires_exact_original_match`.

Neither had a named refuting instance, and `Claim.valid` had no satisfying one,
so the hypothesis ledger (scripts/HypothesisLedger.lean) read both TOOTHLESS.
This file names both poles of each over one concrete deposit.
-/
import Kernel.PayEnrolClaim

namespace Minidregg.Kernel.PayEnrolClaim.Instances

open Minidregg.Kernel.PayEnrolClaim
open Minidregg.Kernel.PayTariff
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- One SPL deposit of 350 atomic units: a 64-byte signature, distinct named
recipient, mint and token program. -/
def observation : Observation where
  signature := List.replicate 64 3
  recipient := List.replicate 32 4
  slot := 1
  amountAtomic := 350
  mint := List.replicate 32 7
  tokenProgram := List.replicate 32 9
  index := 0

/-- A memo of the fixed text length that opens with the `enrol:v2:` prefix. -/
def memo : List UInt8 :=
  PayReceivingContract.memoPrefix ++
    List.replicate (PayReceivingContract.textMemoBytes - PayReceivingContract.memoPrefix.length) 0

def claim : Claim where
  original := observation
  rawMemo := memo
  ownerIdentityKey := List.replicate 32 5
  reason := none
  originalPricingCommitment := ⟨0⟩

/-- The prefix is a string literal; the elaborator does not unfold `String.toUTF8`,
so this is decided by kernel reduction (no compiler trust, see `#assert_axioms`). -/
theorem memoPrefix_length : PayReceivingContract.memoPrefix.length = 9 := by
  decide +kernel

/-- The satisfying pole of `Claim.valid`. -/
theorem claim_valid : claim.valid := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · simp only [claim, memo, List.length_append, List.length_replicate, memoPrefix_length]
    decide
  · simp only [claim, memo]
    exact List.take_left' rfl

/-- The refuting pole of `Claim.valid`: the same deposit with a 31-byte owner
identity is not a claim. -/
theorem short_owner_not_valid :
    ¬ ({ claim with ownerIdentityKey := List.replicate 31 5 } : Claim).valid := by
  intro valid
  exact absurd valid.2.1 (by decide)

/-- The refuting pole of `Claim.valid` on the memo: a zero memo of the full
length does not carry the `enrol:v2:` prefix. -/
theorem unprefixed_memo_not_valid :
    ¬ ({ claim with rawMemo := List.replicate PayReceivingContract.textMemoBytes 0 } : Claim).valid := by
  intro valid
  have prefixed := valid.2.2.2.1
  rw [memoPrefix_length] at prefixed
  exact absurd prefixed (by decide +kernel)

/-- The consumption the original memo admits for `claim`: one week at
`exampleTariff`, birth fee 7. -/
def consumption : Consumption where
  authorization := .originalMemo
  terms :=
    { mode := .enroll
      claimId := claim.id
      ownerIdentityKey := claim.ownerIdentityKey
      pricingCommitment := ⟨0⟩
      requestedWeeks := 1
      minimumStarterCredit := 0
      expiresAtProcessingChainHour := 0 }
  originalAmountAtomic := 350
  tariff := exampleTariff
  mintedCredit := 350
  birthFee := 7
  membershipCredit := 168
  creditedRemainder := 175

/-- The satisfying pole of `Consumption.matchesClaim`. -/
theorem consumption_matches : consumption.matchesClaim claim := ⟨rfl, rfl, rfl⟩

/-- The refuting pole on the amount: the same row recording one more atomic
unit than the deposit carried does not match it. -/
theorem overstated_amount_not_matches :
    ¬ ({ consumption with originalAmountAtomic := 351 } : Consumption).matchesClaim claim := by
  intro matched
  exact absurd matched.2.2 (by decide)

/-- The refuting pole on the claim: the row does not match another deposit
(a different signature, hence a different claim id). -/
theorem other_deposit_not_matches :
    ¬ consumption.matchesClaim
      { claim with original := { observation with signature := List.replicate 64 8 } } := by
  intro matched
  exact absurd matched.1 (by decide)

#assert_axioms memoPrefix_length
#assert_axioms claim_valid
#assert_axioms short_owner_not_valid
#assert_axioms unprefixed_memo_not_valid
#assert_axioms consumption_matches
#assert_axioms overstated_amount_not_matches
#assert_axioms other_deposit_not_matches

end Minidregg.Kernel.PayEnrolClaim.Instances
