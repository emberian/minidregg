/-
# Assurance.PowGrinding — the honest proof-of-work counting bridge

`Assurance.ErrorBudget120` prices proof-of-work by dividing the Fiat--Shamir
grinding term by `2^powBits`.  This file proves the finite-counting core behind
that price, without claiming that a deployed sponge is a random oracle.

The experiment is deliberately explicit:

* a PoW response is a uniformly random `bits`-bit string;
* the nonce predicate requires every bit of that response to be zero;
* the PoW response and the soundness coin of one attempt are separate product
  coordinates (the domain-separation/independence premise);
* an attempt's bad predicate may depend on every *other* attempt, so the
  theorem is stronger than a fixed non-adaptive list of bad sets;
* a union bound over `work` independently sampled attempt coordinates gives
  `work * epsilon / 2^bits`.

What remains outside this file is exactly the cryptographic bridge
`[BUDGET-PoW-compose]`: show that the deployed transcript/nonce hash exposes
these fresh, domain-separated coordinates to an adaptive one-oracle
adversary, and connect its hash-query budget to `work`.  No theorem below
asserts that for Poseidon, or for any concrete hash function.
-/
import Assurance.ErrorBudget120

namespace Minidregg.Assurance

open Minidregg.Selvage

/-! ## The nonce predicate and its exact ideal-response density -/

/-- The `bits` response bits read by the transcript proof-of-work predicate.
At deployment these are a domain-separated prefix of a hash response; here
they are the ideal response coordinate whose density can be counted exactly. -/
abbrev PoWResponse (bits : ℕ) : Type := Fin bits → Bool

/-- A proof-of-work response passes precisely when its required prefix is all
zero.  A concrete nonce is accepted when its transcript-bound hash response
satisfies this predicate. -/
def powResponseAccept {bits : ℕ} (h : PoWResponse bits) : Prop :=
  ∀ i, h i = false

/-- The concrete-predicate shape, separated from any random-oracle claim. -/
def nonceValid {Transcript Nonce : Type} {bits : ℕ}
    (hash : Transcript → Nonce → PoWResponse bits)
    (transcript : Transcript) (nonce : Nonce) : Prop :=
  powResponseAccept (hash transcript nonce)

/-- The all-zero response is accepted, so the predicate is inhabited for every
bit length. -/
theorem powResponseAccept_zero (bits : ℕ) :
    powResponseAccept (fun _ : Fin bits => false) := by
  intro i
  rfl

/-- Teeth: as soon as one bit is required, the all-one response is rejected. -/
theorem powResponseAccept_one_rejected (bits : ℕ) :
    ¬ powResponseAccept (fun _ : Fin (bits + 1) => true) := by
  intro h
  have := h 0
  simp at this

/-- Exactly one `bits`-bit response passes the proof-of-work predicate. -/
theorem powResponseAccept_card (bits : ℕ) :
    Nat.card {h : PoWResponse bits // powResponseAccept h} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨fun _ => false, powResponseAccept_zero bits⟩, ?_⟩
  rintro ⟨h, hh⟩
  apply Subtype.ext
  funext i
  exact hh i

/-- **Exact PoW density.** A uniform ideal `bits`-bit response passes with
probability exactly `2^-bits`.  This is a counting theorem, not a statement
about the distribution of a concrete hash function. -/
theorem powResponseAccept_density (bits : ℕ) :
    uniformProb (PoWResponse bits) powResponseAccept = 1 / (2 ^ bits : ℝ) := by
  unfold uniformProb
  rw [powResponseAccept_card]
  simp [PoWResponse]

/-! ## Independent product factorization -/

private def andSubtypeEquiv {A B : Type} (p : A → Prop) (q : B → Prop) :
    {x : A × B // p x.1 ∧ q x.2} ≃ {a : A // p a} × {b : B // q b} where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Independent product events factor exactly under `uniformProb`. -/
theorem uniformProb_and_prod {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) (q : B → Prop) :
    uniformProb (A × B) (fun x => p x.1 ∧ q x.2)
      = uniformProb A p * uniformProb B q := by
  unfold uniformProb
  rw [Nat.card_congr (andSubtypeEquiv p q), Nat.card_prod, Fintype.card_prod]
  push_cast
  exact (div_mul_div_comm _ _ _ _).symm

/-- One domain-separated attempt pays exactly the PoW density on top of its
soundness event. -/
theorem powAttempt_factor {bits : ℕ} {C : Type} [Fintype C]
    (bad : C → Prop) :
    uniformProb (PoWResponse bits × C)
        (fun x => powResponseAccept x.1 ∧ bad x.2)
      = uniformProb C bad / (2 ^ bits : ℝ) := by
  rw [uniformProb_and_prod, powResponseAccept_density]
  ring

/-! ## A work-bounded, leave-one-out adaptive grind -/

/-- One ideal PoW attempt carries two separately sampled responses: the PoW
prefix and the soundness coin used by the proof-system check. -/
abbrev PoWAttempt (bits : ℕ) (C : Type) : Type := PoWResponse bits × C

/-- The bad event is allowed to inspect all *other* attempts.  For attempt
`i`, `bad i rest c` may depend arbitrarily on `rest`; the only coordinate it
does not receive is the current PoW response.  It receives the current
soundness coin `c` separately.  This makes the required domain separation
visible in the type. -/
def powGrindingWin {bits work : ℕ} {C : Type}
    (bad : (i : Fin work) →
      ({j : Fin work // j ≠ i} → PoWAttempt bits C) → C → Prop)
    (coins : Fin work → PoWAttempt bits C) : Prop :=
  ∃ i, powResponseAccept (coins i).1 ∧
    bad i (fun j => coins j.1) (coins i).2

set_option maxHeartbeats 800000 in
/-- **The PoW grinding bridge at independent ideal coordinates.** If every
attempt's soundness event has conditional probability at most `epsilon` after
fixing every other attempt, then `work` hash-response coordinates win with
probability at most

`work * epsilon / 2^bits`.

The bad predicate may depend on all other attempts, so no independence among
candidate transcripts is assumed.  The one independence assumption that is
used is explicit in `PoWAttempt`: the current PoW response is a product
coordinate separate from the current soundness coin. -/
theorem powGrindingWin_le {bits work : ℕ} {C : Type} [Fintype C]
    (bad : (i : Fin work) →
      ({j : Fin work // j ≠ i} → PoWAttempt bits C) → C → Prop)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hbad : ∀ i rest, uniformProb C (bad i rest) ≤ epsilon) :
    uniformProb (Fin work → PoWAttempt bits C) (powGrindingWin bad)
      ≤ (work : ℝ) * epsilon / (2 ^ bits : ℝ) := by
  classical
  have hslot : ∀ i : Fin work,
      uniformProb (Fin work → PoWAttempt bits C) (fun coins =>
        powResponseAccept (coins i).1 ∧
          bad i (fun j => coins j.1) (coins i).2)
        ≤ epsilon / (2 ^ bits : ℝ) := by
    intro i
    have hsplit :
        uniformProb (Fin work → PoWAttempt bits C) (fun coins =>
          powResponseAccept (coins i).1 ∧
            bad i (fun j => coins j.1) (coins i).2)
          = uniformProb
              (({j : Fin work // j ≠ i} → PoWAttempt bits C) ×
                PoWAttempt bits C)
              (fun x => powResponseAccept x.2.1 ∧ bad i x.1 x.2.2) := by
      exact uniformProb_equiv (splitCoord i)
        (fun x => powResponseAccept x.2.1 ∧ bad i x.1 x.2.2)
    rw [hsplit]
    refine uniformProb_prod_le (div_nonneg hepsilon (by positivity)) (fun rest => ?_)
    change uniformProb (PoWResponse bits × C)
      (fun b => powResponseAccept b.1 ∧ bad i rest b.2)
        ≤ epsilon / (2 ^ bits : ℝ)
    rw [powAttempt_factor]
    exact div_le_div_of_nonneg_right (hbad i rest) (by positivity)
  calc
    uniformProb (Fin work → PoWAttempt bits C) (powGrindingWin bad)
        ≤ ∑ i : Fin work,
            uniformProb (Fin work → PoWAttempt bits C) (fun coins =>
              powResponseAccept (coins i).1 ∧
                bad i (fun j => coins j.1) (coins i).2) := by
          exact uniformProb_exists_le _
    _ ≤ ∑ _i : Fin work, epsilon / (2 ^ bits : ℝ) :=
          Finset.sum_le_sum fun i _ => hslot i
    _ = (work : ℝ) * epsilon / (2 ^ bits : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-! ## Direct identification with `grindingTermPoW` -/

/-- The independent-coordinate theorem specializes exactly to the discounted
term used by `ErrorBudget120`: `work = queries + depth`, and each usable
attempt is priced by the fixed-chain error
`depth * (errStarUD + 1/|F|)`.

This closes the arithmetic/counting part of `[BUDGET-PoW-compose]`.  Its
hypothesis is the remaining cryptographic content: the deployed shared-oracle
execution must realize `bad` with the displayed leave-one-out conditional
bound and the two domain-separated response coordinates. -/
theorem powGrindingWin_le_grindingTermPoW (P : PoWSoundnessParams)
    {C : Type} [Fintype C]
    (bad : (i : Fin (P.queries + P.depth)) →
      ({j : Fin (P.queries + P.depth) // j ≠ i} →
        PoWAttempt P.powBits C) → C → Prop)
    (hbad : ∀ i rest, uniformProb C (bad i rest) ≤
      (P.depth : ℝ) *
        (errStarUD P.toSoundnessParams + 1 / (P.fieldCard : ℝ))) :
    uniformProb (Fin (P.queries + P.depth) → PoWAttempt P.powBits C)
        (powGrindingWin bad)
      ≤ grindingTermPoW P := by
  have hnonneg : 0 ≤ (P.depth : ℝ) *
      (errStarUD P.toSoundnessParams + 1 / (P.fieldCard : ℝ)) := by
    unfold errStarUD
    positivity
  refine le_trans (powGrindingWin_le bad hnonneg hbad) ?_
  unfold grindingTermPoW grindingTerm
  push_cast
  ring_nf
  exact le_rfl

/-!
## Residual boundary

Proved here:

* the all-zero-prefix nonce predicate is inhabited and has teeth;
* its exact ideal-response density is `2^-bits`;
* domain-separated PoW and soundness events factor exactly;
* even a leave-one-out adaptive family of candidate events costs at most
  `work * epsilon / 2^bits`;
* at the `ErrorBudget120` knobs this right-hand side is exactly
  `grindingTermPoW`.

Still named `[BUDGET-PoW-compose]`:

* instantiate `nonceValid` with the deployed transcript-bound hash;
* prove the PoW prefix and proof-system soundness coin behave as the separate
  fresh coordinates used above (domain separation in the one shared ROM);
* compile an adaptive oracle-query execution into `powGrindingWin` with
  `work` bounded by its total hash queries;
* outside the ROM, justify the concrete sponge/hash idealization `[FS-ROM]`.
-/

#check @powResponseAccept_density
#check @powAttempt_factor
#check @powGrindingWin_le
#check @powGrindingWin_le_grindingTermPoW
/-- info: 'Minidregg.Assurance.powGrindingWin_le_grindingTermPoW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powGrindingWin_le_grindingTermPoW

end Minidregg.Assurance
