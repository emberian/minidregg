/-
# Assurance.MixedFieldBudget — price the fields the runtime actually samples

`ErrorBudget120` deliberately records an ideal-coordinate target in which every
algebraic challenge is sampled from a field of cardinality `BabyBear^6`.  The
current executable layers are mixed instead: gate batching and sumcheck use the
base field, while multiplicative FRI uses the degree-four quotient.  A single
`fieldCard` therefore cannot describe that execution.

This file makes the separation explicit.  It also adds the exact-word gate
batching term `(constraints - 1) / |F_batch|`, which is the root-counting bound
proved by `Loom.card_batch_satisfying_le`.  Three exact parameter points give
the useful engineering answer:

* base-field gate batching + sumcheck has only 16 priced bits;
* moving only those two layers to BabyBear^6 leaves the Ext4 RBR/FRI term and
  reaches 75 bits, not 120;
* using BabyBear^6 for every algebraic challenge recovers the 137-bit point,
  even after the gate-batching term is included.

The statements here are arithmetic refinements of the already-landed bounds,
not a composition theorem for the Rust transcript.  The runtime bridges remain
`[PROVER-challenge-field-unification]`, `[BUDGET-PoW-compose]`, and
`[BUDGET-compose]`.
-/

import Assurance.ErrorBudget120

namespace Minidregg.Assurance

/-- The four algebraic challenge fields that the composed expression uses.

`rbrCard` prices the RBR/grinding term, `gateBatchCard` the one random linear
combination of gate defects, `sumcheckCard` every sumcheck round challenge, and
`proximityCard` the final proximity-generator draw. -/
structure ChallengeFieldProfile where
  rbrCard : ℕ
  gateBatchCard : ℕ
  sumcheckCard : ℕ
  proximityCard : ℕ
  gateConstraints : ℕ

/-- The RBR/grinding term at its own challenge cardinality, including PoW. -/
noncomputable def mixedGrindingTerm
    (P : PoWSoundnessParams) (C : ChallengeFieldProfile) : ℝ :=
  ((P.queries : ℝ) + (P.depth : ℝ)) *
      ((P.depth : ℝ) *
        ((P.codeLen : ℝ) / (C.rbrCard : ℝ) + 1 / (C.rbrCard : ℝ))) /
    (2 ^ P.powBits : ℝ)

/-- Exact-word γ-batching error: a nonzero defect polynomial of degree below
`gateConstraints` has at most `gateConstraints - 1` roots. -/
noncomputable def mixedGateBatchTerm (C : ChallengeFieldProfile) : ℝ :=
  ((C.gateConstraints - 1 : ℕ) : ℝ) / (C.gateBatchCard : ℝ)

/-- Sumcheck error at the field in which its round challenges actually live. -/
noncomputable def mixedSumcheckTerm
    (P : PoWSoundnessParams) (C : ChallengeFieldProfile) : ℝ :=
  (P.depth : ℝ) *
    ((P.scRounds : ℝ) * ((P.scDegree : ℝ) / (C.sumcheckCard : ℝ)))

/-- The final proximity term at its own generator-challenge cardinality. -/
noncomputable def mixedProximityTerm
    (P : PoWSoundnessParams) (C : ChallengeFieldProfile) : ℝ :=
  (P.codeLen : ℝ) / (C.proximityCard : ℝ)

/-- The collision term is field-independent and remains exactly the existing
ideal-ROM expression. -/
noncomputable def mixedCrTerm (P : PoWSoundnessParams) : ℝ :=
  crTerm P.toSoundnessParams

/-- The mixed-field composed arithmetic expression. -/
noncomputable def mixedFieldSoundness
    (P : PoWSoundnessParams) (C : ChallengeFieldProfile) : ℝ :=
  mixedGrindingTerm P C + mixedGateBatchTerm C + mixedSumcheckTerm P C +
    mixedCrTerm P + mixedProximityTerm P C

/-- Put every algebraic challenge in one field. -/
def uniformChallengeFields (q gateConstraints : ℕ) : ChallengeFieldProfile where
  rbrCard := q
  gateBatchCard := q
  sumcheckCard := q
  proximityCard := q
  gateConstraints := gateConstraints

/-- With a vacuous one-row batching channel and one shared field, the refined
expression is definitionally the old PoW expression.  This pins that the new
model changes only the field split and the newly explicit gate-batching term. -/
theorem uniform_one_gate_recovers (P : PoWSoundnessParams) :
    mixedFieldSoundness P (uniformChallengeFields P.fieldCard 1) =
      soundnessErrorPoW P := by
  simp [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm,
    uniformChallengeFields, soundnessErrorPoW, grindingTermPoW,
    grindingTerm, sumcheckTerm, proximityTerm, errStarUD]

private def babyBear : ℕ := 2013265921

/-- The current field split, priced as if the reference gate proof were the
soundness tooth: Ext4 for RBR/FRI, base BabyBear for γ and sumcheck.  The demo
descriptor has 23 gate/zero constraints.  The actual reference verifier now
checks the clear trace exactly, so this is the security of the *prospective
succinct replacement* if it retained the present challenge types. -/
def baseGateExt4Fri : ChallengeFieldProfile where
  rbrCard := babyBear ^ 4
  gateBatchCard := babyBear
  sumcheckCard := babyBear
  proximityCard := babyBear ^ 4
  gateConstraints := 23

/-- Minimal field fix: gate batching and sumcheck move to Ext6, but the
RBR/proximity side remains Ext4. -/
def ext6GateExt4Fri : ChallengeFieldProfile where
  rbrCard := babyBear ^ 4
  gateBatchCard := babyBear ^ 6
  sumcheckCard := babyBear ^ 6
  proximityCard := babyBear ^ 4
  gateConstraints := 23

/-- Full algebraic unification at Ext6. -/
def unifiedExt6 : ChallengeFieldProfile :=
  uniformChallengeFields (babyBear ^ 6) 23

/-- **Negative runtime tooth:** the base-field gate/sumcheck split does not even
clear 17 bits once the gate-batching root count is included. -/
theorem baseGateExt4Fri_ceiling :
    1 / 2 ^ 17 < mixedFieldSoundness secureBudget120 baseGateExt4Fri := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, baseGateExt4Fri,
    babyBear, secureBudget120, crTerm]

/-- The same mixed point does clear 16 bits: its exact priced interval is
`(2^-17, 2^-16]`. -/
theorem baseGateExt4Fri_secure_16 :
    mixedFieldSoundness secureBudget120 baseGateExt4Fri ≤ 1 / 2 ^ 16 := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, baseGateExt4Fri,
    babyBear, secureBudget120, crTerm]

/-- **Architecture tooth:** Ext6 gate batching and sumcheck alone still leave
the Ext4 RBR/FRI term dominant, so the system does not clear 76 bits. -/
theorem ext6GateExt4Fri_ceiling :
    1 / 2 ^ 76 < mixedFieldSoundness secureBudget120 ext6GateExt4Fri := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, ext6GateExt4Fri,
    babyBear, secureBudget120, crTerm]

/-- The partially upgraded point clears 75 bits exactly. -/
theorem ext6GateExt4Fri_secure_75 :
    mixedFieldSoundness secureBudget120 ext6GateExt4Fri ≤ 1 / 2 ^ 75 := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, ext6GateExt4Fri,
    babyBear, secureBudget120, crTerm]

/-- Full Ext6 algebraic unification retains the 137-bit upper bound even after
paying the explicit 22/|Ext6| demo gate-batching term. -/
theorem unifiedExt6_secure_137 :
    mixedFieldSoundness secureBudget120 unifiedExt6 ≤ 1 / 2 ^ 137 := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, unifiedExt6,
    uniformChallengeFields, babyBear, secureBudget120, crTerm]

/-- The 138th bit remains refuted at the fully unified point. -/
theorem unifiedExt6_ceiling :
    1 / 2 ^ 138 < mixedFieldSoundness secureBudget120 unifiedExt6 := by
  norm_num [mixedFieldSoundness, mixedGrindingTerm, mixedGateBatchTerm,
    mixedSumcheckTerm, mixedCrTerm, mixedProximityTerm, unifiedExt6,
    uniformChallengeFields, babyBear, secureBudget120, crTerm]

#check @uniform_one_gate_recovers
#check @baseGateExt4Fri_ceiling
#check @baseGateExt4Fri_secure_16
#check @ext6GateExt4Fri_ceiling
#check @ext6GateExt4Fri_secure_75
#check @unifiedExt6_secure_137
#check @unifiedExt6_ceiling

/-- info: 'Minidregg.Assurance.baseGateExt4Fri_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms baseGateExt4Fri_ceiling
/-- info: 'Minidregg.Assurance.ext6GateExt4Fri_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ext6GateExt4Fri_ceiling
/-- info: 'Minidregg.Assurance.unifiedExt6_secure_137' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unifiedExt6_secure_137

end Minidregg.Assurance
