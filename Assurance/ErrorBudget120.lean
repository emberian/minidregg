/-
# Assurance.ErrorBudget120 — a proved 120-bit parameterization

`Assurance.ErrorBudget` proves the deployed BabyBear⁴ budget is 55 bits and
identifies the dominant term:

  `(t + k) * k * (n + 1) / |F|`.

This file records the two deployment levers that move that term past 120 bits:

* challenges live in BabyBear⁶ rather than BabyBear⁴ (the trace/base field is
  unchanged); and
* a 20-bit transcript proof-of-work prices each usable grinding attempt at
  `2^20` hashes.

The result is stronger than the requested target: the resulting composed
budget lies in `(2^-138, 2^-137]`.  Both levers are load-bearing at the chosen
threat model: BabyBear⁴ + 20 PoW bits and BabyBear⁶ + 0 PoW bits each fail the
120-bit target.

## What is, and is not, proved

The arithmetic statement is a theorem over the four landed component bounds.
The PoW extension is deliberately a *resource-budget model*: `queries` is the
adversary's total hash-work budget and `powBits` divides the number of usable
transcript attempts.  A protocol theorem connecting a concrete nonce predicate
and one shared Fiat--Shamir execution to this discounted attempt count remains
`[BUDGET-PoW-compose]`, beside the already named `[BUDGET-compose]`.  We do not
silently call that deployment bridge proved.

Costs are explicit.  The trace remains over BabyBear and only challenges move
to the larger extension, but extension-field challenge arithmetic is dearer
and must be benchmarked in the new prover.  Twenty PoW bits mean roughly
`2^20` hash evaluations per honest proof.  The code term remains in the proved
unique-decoding regime.  The binary-tower/additive-FRI route
`[BTOWER-additive-fri]` is the native large-field trajectory; this file only
prices it.
-/
import Assurance.ErrorBudget
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Minidregg.Assurance

/-! ## The proof-of-work extension -/

/-- A soundness budget together with a transcript proof-of-work requirement.

This extends, rather than mutates, `SoundnessParams`: the original 55-bit
theorem continues to state exactly the deployed no-PoW budget it proved. -/
structure PoWSoundnessParams extends SoundnessParams where
  /-- A valid transcript nonce costs `2^powBits` hash trials. -/
  powBits : ℕ

/-- The grinding term after converting total hash work into usable transcript
attempts.  Every accepted nonce consumes `2^powBits` trials in the resource
model, so only the grinding term is discounted. -/
noncomputable def grindingTermPoW (P : PoWSoundnessParams) : ℝ :=
  grindingTerm P.toSoundnessParams / (2 ^ P.powBits : ℝ)

/-- The composed error with the PoW-priced grinding term.  Sumcheck,
collision-resistance, and proximity are unchanged. -/
noncomputable def soundnessErrorPoW (P : PoWSoundnessParams) : ℝ :=
  grindingTermPoW P + sumcheckTerm P.toSoundnessParams
    + crTerm P.toSoundnessParams + proximityTerm P.toSoundnessParams

/-- Replace only the PoW requirement. -/
def withPowBits (P : PoWSoundnessParams) (b : ℕ) : PoWSoundnessParams where
  toSoundnessParams := P.toSoundnessParams
  powBits := b

/-- Replace only the challenge-field cardinality. -/
def withFieldCard (P : PoWSoundnessParams) (q : ℕ) : PoWSoundnessParams where
  toSoundnessParams := { P.toSoundnessParams with fieldCard := q }
  powBits := P.powBits

/-- Zero PoW bits recovers the original composed expression exactly. -/
theorem pow_zero_recovers (P : SoundnessParams) :
    soundnessErrorPoW { toSoundnessParams := P, powBits := 0 }
      = soundnessError P := by
  simp [soundnessErrorPoW, grindingTermPoW, soundnessError]

/-- One more PoW bit halves the grinding contribution exactly. -/
theorem pow_gains (P : PoWSoundnessParams) (b : ℕ) :
    grindingTermPoW (withPowBits P (b + 1))
      = grindingTermPoW (withPowBits P b) / 2 := by
  simp [grindingTermPoW, withPowBits, pow_succ]
  ring

/-- Multiplying the challenge-field cardinality by `factor` divides the
grinding contribution by exactly `factor`: field bits buy grinding bits
one-for-one. -/
theorem field_bump_gains (P : PoWSoundnessParams) (factor : ℕ)
    (hcard : P.fieldCard ≠ 0) (hfactor : factor ≠ 0) :
    grindingTermPoW
        (withFieldCard P (P.fieldCard * factor))
      = grindingTermPoW P / factor := by
  have hcardR : (P.fieldCard : ℝ) ≠ 0 := by exact_mod_cast hcard
  have hfactorR : (factor : ℝ) ≠ 0 := by exact_mod_cast hfactor
  simp only [grindingTermPoW, withFieldCard, grindingTerm, errStarUD]
  push_cast
  field_simp

/-- The discounted expression never exceeds the original expression.  This is
an arithmetic comparison, not the still-owed nonce-protocol composition
`[BUDGET-PoW-compose]`. -/
theorem soundnessErrorPoW_le (P : PoWSoundnessParams) :
    soundnessErrorPoW P ≤ soundnessError P.toSoundnessParams := by
  have hgrind : 0 ≤ grindingTerm P.toSoundnessParams := by
    unfold grindingTerm errStarUD
    positivity
  have hpow : 1 ≤ (2 ^ P.powBits : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  have hdiv : grindingTerm P.toSoundnessParams / (2 ^ P.powBits : ℝ)
      ≤ grindingTerm P.toSoundnessParams := div_le_self hgrind hpow
  unfold soundnessErrorPoW grindingTermPoW soundnessError
  linarith

/-- The usual formula-level bit-security reading of the priced expression. -/
noncomputable def bitsSecurity (P : PoWSoundnessParams) : ℝ :=
  -Real.logb 2 (soundnessErrorPoW P)

theorem bitsSecurity_eq (P : PoWSoundnessParams) :
    bitsSecurity P = -Real.logb 2 (soundnessErrorPoW P) := rfl

/-! ## The 120-bit deployment point -/

/-- BabyBear⁶ challenges, BabyBear trace, 20 PoW bits, and the same explicit
`2^40` total-hash-work / `2^8`-depth threat model as `deployedBudget`.

The hash collision term retains a 248-bit range.  The target label is 120,
although the exact expression proves 137 bits. -/
noncomputable def secureBudget120 : PoWSoundnessParams where
  toSoundnessParams :=
    { fieldCard := 2013265921 ^ 6
      codeLen := 2 ^ 20
      degree := 2 ^ 19
      delta := 1 / 8
      queries := 2 ^ 40
      depth := 2 ^ 8
      scRounds := 20
      scDegree := 3
      hashQueries := 2 ^ 40
      hashBits := 248
      secparam := 120 }
  powBits := 20

/-- **Headline: the priced parameterization clears 120 bits.** Exact integer
arithmetic at the honest BabyBear prime, with no floating-point estimate. -/
theorem secureBudget120_secure :
    soundnessErrorPoW secureBudget120 ≤ 1 / 2 ^ 120 := by
  norm_num [soundnessErrorPoW, grindingTermPoW, grindingTerm, sumcheckTerm,
    crTerm, proximityTerm, errStarUD, secureBudget120]

/-- The same parameterization in fact clears 137 bits. -/
theorem secureBudget120_secure_137 :
    soundnessErrorPoW secureBudget120 ≤ 1 / 2 ^ 137 := by
  norm_num [soundnessErrorPoW, grindingTermPoW, grindingTerm, sumcheckTerm,
    crTerm, proximityTerm, errStarUD, secureBudget120]

/-- The 138th bit is refuted: the proved priced level is tight to 137 bits. -/
theorem secureBudget120_ceiling :
    1 / 2 ^ 138 < soundnessErrorPoW secureBudget120 := by
  norm_num [soundnessErrorPoW, grindingTermPoW, grindingTerm, sumcheckTerm,
    crTerm, proximityTerm, errStarUD, secureBudget120]

/-- The unique-decoding side condition is unchanged and still fires. -/
theorem secureBudget120_delta_admissible :
    0 < secureBudget120.delta ∧ secureBudget120.delta
      < 1 - (2 + (secureBudget120.degree : ℝ)
        / (secureBudget120.codeLen : ℝ)) / 3 := by
  constructor <;> norm_num [secureBudget120]

/-! ## Teeth: both levers are load-bearing -/

/-- Keep the 20-bit PoW but fall back to BabyBear⁴ challenges. -/
noncomputable def secureBudget120BabyBear4 : PoWSoundnessParams :=
  withFieldCard secureBudget120 (2013265921 ^ 4)

/-- BabyBear⁴ + 20 PoW bits does **not** reach 120 bits. -/
theorem babyBear4_fails_120 :
    1 / 2 ^ 120 < soundnessErrorPoW secureBudget120BabyBear4 := by
  norm_num [secureBudget120BabyBear4, withFieldCard, soundnessErrorPoW,
    grindingTermPoW, grindingTerm, sumcheckTerm, crTerm, proximityTerm,
    errStarUD, secureBudget120]

/-- Keep BabyBear⁶ but remove the proof of work. -/
noncomputable def secureBudget120NoPoW : PoWSoundnessParams :=
  withPowBits secureBudget120 0

/-- BabyBear⁶ without PoW is about 117 bits and therefore also fails 120. -/
theorem noPoW_fails_120 :
    1 / 2 ^ 120 < soundnessErrorPoW secureBudget120NoPoW := by
  norm_num [secureBudget120NoPoW, withPowBits, soundnessErrorPoW,
    grindingTermPoW, grindingTerm, sumcheckTerm, crTerm, proximityTerm,
    errStarUD, secureBudget120]

/-- In the chosen instance, each PoW bit is visible literally as a power-of-two
divisor on the old grinding term. -/
theorem secureBudget120_pow_price :
    grindingTermPoW secureBudget120
      = grindingTerm secureBudget120.toSoundnessParams / 2 ^ 20 := rfl

/-!
## Residual ledger

* **Proved:** the priced expression; zero-bit recovery; one-bit-per-PoW-bit
  scaling; a BabyBear⁶ + 20-bit-PoW parameterization in
  `(2^-138, 2^-137]`; both load-bearing counterfactuals; the UD side condition.
* **`[BUDGET-PoW-compose]`:** define the transcript nonce predicate, prove its
  success set has density `2^-powBits`, and compose it with the adaptive
  one-oracle execution.  Until then, 137 bits is a theorem about the stated
  resource budget, not a claim that the current prover already emits PoW.
* **Inherited:** `[BUDGET-compose]`, `[FS-ROM]`, the commitment and extraction
  bridges named by `Assurance.ErrorBudget`, and unique decoding.
* **Trajectory:** `[LC-grinding-native]` would remove the extra depth factor
  (eight further bits here); `[BTOWER-additive-fri]` supplies a native
  large-field implementation route rather than merely pricing BabyBear⁶.
-/

#check @secureBudget120_secure
#check @secureBudget120_secure_137
#check @babyBear4_fails_120
#check @noPoW_fails_120
#print axioms secureBudget120_secure
#print axioms secureBudget120_secure_137
#print axioms babyBear4_fails_120
#print axioms noPoW_fails_120

end Minidregg.Assurance
