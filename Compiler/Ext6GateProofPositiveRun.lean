/-
# Compiler.Ext6GateProofPositiveRun -- one exact accepted Ext6 transcript

This module constructs the positive control witness left open by
`Ext6GateProofDeployment`: an honest receipt for the deployed 23-residual,
five-round range statement, its canonical codec bytes, and an opaque runner
whose only authority is returning those bytes.

The Fiat--Shamir construction is causal.  Challenge `i` is computed from a
receipt whose challenge function contains exactly the already-computed prefix
and zero junk at `i` and beyond.  Prefix-measurability of the honest quadratic
round family and `roundInput_eq_of_same_current` then prove that the final
receipt hashes the identical round-`i` prefix.  No fixed-point or native
transcript oracle is assumed.

This is controller completeness only.  In particular it constructs none of
the eight-event `SecurityResidual` and states no sub-unit security bound.
-/

import Compiler.Ext6GateProofDeployment

namespace Minidregg.Compiler.Ext6GateProofPositiveRun

open Minidregg.Assurance
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.Ext6GateProofDeployment
open Minidregg.Compiler.GateFactoredExt6
open Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom Polynomial
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

/-! ## Satisfying trace and fixed transcript identities -/

theorem demoTrace_exists :
    ∃ trace : Nat → BabyBear,
      (∀ i : Fin 5, trace i.val = demoVals i) ∧
      descriptorHolds demoDescriptor trace :=
  (emit_accepts_iff_fin 5 1 demoVals demoSystem).mpr (by decide)

noncomputable def demoTrace : Nat → BabyBear :=
  Classical.choose demoTrace_exists

theorem demoTrace_prefix (i : Fin 5) : demoTrace i.val = demoVals i :=
  (Classical.choose_spec demoTrace_exists).1 i

theorem demoTrace_holds : descriptorHolds demoDescriptor demoTrace :=
  (Classical.choose_spec demoTrace_exists).2

@[simp] theorem demoTrace_public : demoTrace 0 = 13 := by
  simpa [demoVals] using demoTrace_prefix 0

def traceRoot : Digest := ⟨986030⟩

def operandRoot (j : Fin 7) : Digest := ⟨986040 + j.val⟩

theorem traceRoot_nonzero : traceRoot ≠ ⟨0⟩ := by decide

theorem operandRoot_injective : Function.Injective operandRoot := by
  intro left right equal
  apply Fin.ext
  simpa [operandRoot] using congrArg Digest.value equal

def zeroChallenges : Fin Rounds → Ext6Q := fun _ ↦ 0

/-! ## Honest round data and a causal Fiat--Shamir schedule -/

/-- A transcript shell used before gamma has been derived.  Fields absent from
the round challenge prefix carry inert zero/empty values. -/
noncomputable def roundReceipt (gamma : Ext6Q)
    (challenges : Fin Rounds → Ext6Q) : Receipt Rounds where
  traceRoot := traceRoot
  operandRoot := operandRoot
  gamma := gamma
  roundMessage := fun i ↦
    factoredRounds statement.descriptor demoTrace
      (statement.encodingFor demoTrace) gamma (chalOf challenges) i.val
  roundChallenge := challenges
  terminalValue := fun _ ↦ 0
  eta := 0
  aggregateValue := 0
  traceOpeningProof := []
  operandOpeningProof := fun _ ↦ []
  finalLdtProof := []

/-- Gamma is derived from the canonical statement preimage and fixed trace
root.  The seed's zero gamma is not part of `gammaInput`. -/
noncomputable def canonicalGamma : Ext6Q :=
  derivedGamma suite statement (roundReceipt 0 zeroChallenges)

@[simp] theorem roundReceipt_derivedGamma
    (challenges : Fin Rounds → Ext6Q) :
    derivedGamma suite statement (roundReceipt canonicalGamma challenges) =
      canonicalGamma := by
  rfl

/-- Challenge tuple with exactly the prefix below `i` populated. -/
def prefixChallenges (i : Nat) (prior : ∀ j : Nat, j < i → Ext6Q) :
    Fin Rounds → Ext6Q := fun j ↦
  if h : j.val < i then prior j.val h else 0

/-- The concrete FS challenge stream.  The recursive calls occur only at
strictly smaller coordinates, so every hash consumes an already-built prefix. -/
noncomputable def fsChallengeNat (i : Nat) : Ext6Q :=
  if hi : i < Rounds then
    derivedRoundChallenge suite statement
      (roundReceipt canonicalGamma
        (prefixChallenges i (fun j _ ↦ fsChallengeNat j))) ⟨i, hi⟩
  else 0
termination_by i
decreasing_by omega

noncomputable def fsChallenges : Fin Rounds → Ext6Q := fun i ↦
  fsChallengeNat i.val

@[simp] theorem prefixChallenges_fs_lt (i : Nat) (j : Fin Rounds)
    (h : j.val < i) :
    prefixChallenges i (fun k _ ↦ fsChallengeNat k) j = fsChallenges j := by
  simp [prefixChallenges, fsChallenges, h]

theorem chalOf_prefix_eq_below (i j : Nat) (hji : j < i) :
    chalOf (prefixChallenges i (fun k _ ↦ fsChallengeNat k)) j =
      chalOf fsChallenges j := by
  by_cases hj : j < Rounds
  · simp [chalOf, hj, prefixChallenges, fsChallenges, hji]
  · simp [chalOf, hj]

theorem honest_round_prefix_exact (i : Fin Rounds) :
    fsChallenges i =
      derivedRoundChallenge suite statement
        (roundReceipt canonicalGamma fsChallenges) i := by
  let staged := prefixChallenges i.val (fun j _ ↦ fsChallengeNat j)
  have sameMessages : ∀ k : Fin Rounds, k.val ≤ i.val →
      (roundReceipt canonicalGamma staged).roundMessage k =
        (roundReceipt canonicalGamma fsChallenges).roundMessage k := by
    intro k hki
    dsimp only [roundReceipt]
    apply quadHonest_prefixMeasurable
    intro j hjk
    exact chalOf_prefix_eq_below i.val j (lt_of_lt_of_le hjk hki)
  have samePrior : ∀ k : Fin Rounds, k.val < i.val →
      (roundReceipt canonicalGamma staged).roundChallenge k =
        (roundReceipt canonicalGamma fsChallenges).roundChallenge k := by
    intro k hki
    exact prefixChallenges_fs_lt i.val k hki
  have inputExact := roundInput_eq_of_same_current suite statement
    (roundReceipt canonicalGamma staged)
    (roundReceipt canonicalGamma fsChallenges) i
    (by exact ⟨rfl, rfl, rfl⟩) sameMessages samePrior
  rw [fsChallenges, fsChallengeNat]
  simp only [dif_pos i.isLt]
  unfold derivedRoundChallenge
  rw [inputExact]

/-! ## Exact terminal and eta-aggregate receipt -/

noncomputable def honestOpenings :
    TerminalOpenings statement.descriptor demoTrace
      (statement.encodingFor demoTrace) canonicalGamma fsChallenges where
  openLinear kind :=
    { value := Finsupp.linearCombination Ext6Q
        (liftWord (K := Ext6Q) demoTrace)
        (terminalFunctional kind statement.descriptor demoTrace
          (statement.encodingFor demoTrace) canonicalGamma fsChallenges).weights
      authenticates := rfl }

noncomputable def terminalValues (j : Fin 7) : Ext6Q :=
  honestOpenings.affineValue (terminalOrder j)

noncomputable def receiptWith (eta aggregate : Ext6Q) : Receipt Rounds where
  traceRoot := traceRoot
  operandRoot := operandRoot
  gamma := canonicalGamma
  roundMessage := fun i ↦
    factoredRounds statement.descriptor demoTrace
      (statement.encodingFor demoTrace) canonicalGamma (chalOf fsChallenges) i.val
  roundChallenge := fsChallenges
  terminalValue := terminalValues
  eta := eta
  aggregateValue := aggregate
  traceOpeningProof := []
  operandOpeningProof := fun _ ↦ []
  finalLdtProof := []

noncomputable def canonicalEta : Ext6Q :=
  derivedEta suite statement (receiptWith 0 0)

noncomputable def canonicalAggregate : Ext6Q :=
  etaAggregateLeft statement (receiptWith canonicalEta 0)

/-- The concrete proof-side receipt.  Empty opening/LDT byte strings are inert
at the controller layer; their authentication is precisely the separately
retained security residual. -/
noncomputable def receipt : Receipt Rounds :=
  receiptWith canonicalEta canonicalAggregate

theorem gamma_exact : receipt.gamma = derivedGamma suite statement receipt := by
  rfl

theorem every_round_challenge_exact (i : Fin Rounds) :
    receipt.roundChallenge i =
      derivedRoundChallenge suite statement receipt i := by
  exact honest_round_prefix_exact i

theorem eta_exact : receipt.eta = derivedEta suite statement receipt := by
  rfl

theorem roundMessages_exact : roundMessages receipt =
    factoredRounds statement.descriptor demoTrace
      (statement.encodingFor demoTrace) canonicalGamma (chalOf fsChallenges) := by
  funext i
  by_cases hi : i < Rounds
  · simp [roundMessages, receipt, receiptWith, hi]
  · simp [roundMessages, factoredRounds, quadHonest, hi]

theorem roundChallenges_exact : roundChallenges receipt = chalOf fsChallenges := by
  funext i
  by_cases hi : i < Rounds
  · simp [roundChallenges, receipt, receiptWith, chalOf, hi, fsChallenges]
  · simp [roundChallenges, chalOf, hi]

theorem every_round_degree (i : Fin Rounds) :
    (receipt.roundMessage i).degree < ((2 + 1 : Nat) : WithBot Nat) := by
  simpa [receipt, receiptWith, factoredRounds] using
    quadHonest_degree
      (mulAGamma statement.descriptor demoTrace
        (statement.encodingFor demoTrace) canonicalGamma)
      (mulB statement.descriptor demoTrace (statement.encodingFor demoTrace))
      (combinedC statement.descriptor demoTrace
        (statement.encodingFor demoTrace) canonicalGamma)
      (chalOf fsChallenges) i.val i.isLt

theorem every_round_chain (i : Fin Rounds) :
    (receipt.roundMessage i).eval 0 + (receipt.roundMessage i).eval 1 =
      scChain 0 (roundMessages receipt) (roundChallenges receipt) i := by
  rw [roundMessages_exact, roundChallenges_exact]
  exact factoredRounds_zero_boolean_sum statement.descriptor demoTrace
    (statement.encodingFor demoTrace) canonicalGamma demoTrace_holds
    fsChallenges i.val i.isLt

theorem terminal_exact :
    scChain 0 (roundMessages receipt) (roundChallenges receipt) Rounds =
      terminalExpression receipt.terminalValue := by
  rw [roundMessages_exact, roundChallenges_exact]
  have closed := factoredRounds_terminal_of_openings statement.descriptor demoTrace
    (statement.encodingFor demoTrace) canonicalGamma fsChallenges honestOpenings
  rw [gammaBatchedDescriptorResidual_zero_of_holds
    statement.descriptor demoTrace canonicalGamma demoTrace_holds] at closed
  simpa [receipt, receiptWith, terminalValues, terminalExpression, terminalOrder] using closed

theorem aggregate_exact :
    etaAggregateLeft statement receipt = receipt.aggregateValue := by
  rfl

/-- Non-vacuous controller completeness for the exact deployed statement. -/
theorem receipt_accepts : Accepts suite statement receipt := by
  exact ⟨gamma_exact, every_round_challenge_exact, eta_exact,
    every_round_degree, every_round_chain, terminal_exact, aggregate_exact⟩

/-! ## Canonical framing, accepted bytes, and rejection teeth -/

def request : List UInt8 :=
  envelope (encodeDigest suiteId) ++
    envelope (encodeDigest controllerId) ++
      envelope (canonicalStatementPreimage suite statement)

theorem request_exact : request =
    envelope (encodeDigest suiteId) ++
      envelope (encodeDigest controllerId) ++
        envelope (canonicalStatementPreimage suite statement) := rfl

noncomputable def proofBytes : List UInt8 :=
  verifier.receiptCodec.encode receipt

@[simp] theorem proofBytes_decode :
    verifier.receiptCodec.decode proofBytes = some receipt :=
  verifier.receiptCodec.decode_encode receipt

noncomputable def acceptedReceipt :
    AcceptedReceipt suite statement verifier request where
  proofBytes := proofBytes
  receipt := receipt
  decoded := proofBytes_decode
  accepted := receipt_accepts

def honestRunner : OpaqueProofRunner Unit := fun supplied ↦
  if supplied = request then .ok proofBytes else .error ()

theorem honest_run_succeeds :
    run suite statement verifier honestRunner request = .ok acceptedReceipt := by
  have checked : verifier.check receipt = true :=
    (verifier.check_iff receipt).mpr receipt_accepts
  simp only [run, honestRunner, if_pos]
  split
  next decodeFailed =>
    have impossible : some receipt = (none : Option (Receipt Rounds)) :=
      proofBytes_decode.symm.trans decodeFailed
    cases impossible
  next decodedReceipt decoded =>
    have receiptExact : decodedReceipt = receipt :=
      Option.some.inj (decoded.symm.trans proofBytes_decode)
    subst decodedReceipt
    simp only [checked]
    congr

def staleRequest : List UInt8 := request ++ [0xff]

theorem staleRequest_ne : staleRequest ≠ request := by
  intro equal
  have lengths := congrArg List.length equal
  simp [staleRequest] at lengths

theorem stale_request_rejected :
    run suite statement verifier honestRunner staleRequest =
      .error (.native ()) := by
  simp [run, honestRunner, staleRequest_ne]

theorem malformed_bytes_rejected :
    run suite statement verifier malformedRunner request =
      .error .invalidEncoding := by
  simp only [run, malformedRunner]
  split
  next => rfl
  next decodedReceipt decoded =>
    have impossible : (none : Option (Receipt Rounds)) = some decodedReceipt :=
      verifier_decode_empty.symm.trans decoded
    cases impossible

noncomputable def tamperedReceipt : Receipt Rounds :=
  { receipt with gamma := receipt.gamma + 1 }

theorem tamperedReceipt_not_accepts :
    ¬ Accepts suite statement tamperedReceipt := by
  intro accepted
  have hgamma := accepted.1
  have original := gamma_exact
  change receipt.gamma + 1 = derivedGamma suite statement tamperedReceipt at hgamma
  have sameDerived : derivedGamma suite statement tamperedReceipt =
      derivedGamma suite statement receipt := by rfl
  rw [sameDerived, ← original] at hgamma
  have impossible : (1 : Ext6Q) = 0 :=
    add_left_cancel (show receipt.gamma + 1 = receipt.gamma + 0 by simp at hgamma ⊢)
  exact one_ne_zero impossible

def tamperedRunner : OpaqueProofRunner Unit := fun _ ↦
  .ok (verifier.receiptCodec.encode tamperedReceipt)

theorem decoded_tamper_rejected :
    run suite statement verifier tamperedRunner request = .error .rejected := by
  have unchecked : verifier.check tamperedReceipt = false := by
    apply Bool.eq_false_iff.mpr
    intro checked
    exact tamperedReceipt_not_accepts
      ((verifier.check_iff tamperedReceipt).mp checked)
  simp only [run, tamperedRunner]
  split
  next decodeFailed =>
    have impossible : some tamperedReceipt = (none : Option (Receipt Rounds)) :=
      (verifier.receiptCodec.decode_encode tamperedReceipt).symm.trans decodeFailed
    cases impossible
  next decodedReceipt decoded =>
    have receiptExact : decodedReceipt = tamperedReceipt :=
      Option.some.inj
        (decoded.symm.trans (verifier.receiptCodec.decode_encode tamperedReceipt))
    subst decodedReceipt
    simp [unchecked]

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.Ext6GateProofPositiveRun.receipt_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_accepts
/-- info: 'Minidregg.Compiler.Ext6GateProofPositiveRun.honest_run_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_run_succeeds
/-- info: 'Minidregg.Compiler.Ext6GateProofPositiveRun.decoded_tamper_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_tamper_rejected

end

end Minidregg.Compiler.Ext6GateProofPositiveRun
