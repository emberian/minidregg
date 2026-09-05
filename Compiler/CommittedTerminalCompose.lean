/-
# Compiler.CommittedTerminalCompose -- the full-word gate proof's ledger, in one theorem

`CommittedTerminalRealizer` authenticates the terminal (`realize_sound`: error
zero under the named `BindingCommitment`); `Selvage/MultilinearExtension`
prices the clear degree-one sumcheck (`mle_sumcheck_soundness`: `m · 1/|F|`
against any prefix-measurable degree-`≤ 1` prover).  Neither is a statement
about a PROOF being accepted.  This module composes them into the one ledger
theorem the full-word gate proof owes:

* **`GateProofAccepts`** -- what the verifier decides, read into the field:
  the realizer accepted `v` against the root, every round's Boolean check
  passed on the zero-anchored claim chain, and the chain closes at
  `readExt6 v`.  (`CommittedTerminalController` decides exactly this in lanes
  and proves the reflection.)
* **`gateProof_sound`** -- accepted against a root committing `w` ⇒
  `descriptorHolds d (traceOf w)` ∨ the gamma event ∨ the sumcheck event.
  Three summands, because a gate proof has three places to lose: the
  terminal (error `0`: `realize_sound`), the gamma batching (a failing trace
  whose `Σ_k γ^k res_k` happens to vanish), and the sumcheck rounds.
* **The prices, each the tree's own number:**
  `gammaZero_prob_le` -- `Pr_γ[gamma event] ≤ (N−1)/|Ext6Q|` (`card_bad_eta_le`,
  REUSED, at zero weights); `sumcheck_prob_le` -- `Pr_r[sumcheck event] ≤ m/|Ext6Q|`
  (`mle_sumcheck_soundness`, REUSED, `d = 1`); `sumcheck_prob_le_two` -- the
  `m · 2/|F| + 0` the unit was asked to carry, as a corollary (the `2` is the
  factored quadratic protocol's per-round price, which THIS verifier does not
  pay; the `+ 0` is the terminal's).  `card_ext6`: `|Ext6Q| = p^6` with
  `p = 2^31 − 2^27 + 1`, so the Stage-0 ledger reads
  `0 + 4147/p^6 + 13/p^6`.

**The finite challenge field.**  The tree's probability layer (`uniformProb`)
needs `Fintype`, and `Ext6Q = AdjoinRoot ext6Polynomial` had no instance --
`GateFactoredExt6` counts bad challenges in an arbitrary `Finset` for that
reason.  §1 builds it noncomputably from `Module.Finite BabyBear Ext6Q`
(`ext6Q_finrank = 6`); nothing computable depends on it.

**Regime, on the label.**  The ledger is for the FULL-WORD proof: the
verifier reads the whole trace, so there is no query/proximity/list-decoding
term -- those enter with `[CT-sampled]`.  The commitment premise stays the
named instance `S : BindingCommitment` (the `[COMMIT-CR]` price is `S`'s
ledger); the gamma and round challenges are inputs here, their derivation
(Fiat-Shamir) is the controller's transcript and is not priced in this file.

**ATLAS fields (law 2):** the gamma event is refuted on the demo by the
kernel -- `DemoInstance.laneZeroClaim_tampered_ne_zero`: at the demo gamma the
tampered trace's batched residual is NONZERO (the gamma leg catches it), and
`laneZeroClaim_honest_zero` for the satisfying trace.  `GateProofAccepts` is
inhabited by the honest run and refuted by the tampered one in
`CommittedTerminalController` (kernel-decided and Stage-0 exhibited there).
-/

import Compiler.CommittedTerminalFactored7
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality

namespace Minidregg.Compiler.CommittedTerminalCompose

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.GateFactoredExt6 Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.CommittedTerminalFactored7
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## §1. The challenge field is finite: `|Ext6Q| = p^6` -/

noncomputable instance ext6Finite : Finite Ext6Q := Module.finite_of_finite BabyBear

noncomputable instance ext6Fintype : Fintype Ext6Q := Fintype.ofFinite Ext6Q

theorem card_ext6 : Fintype.card Ext6Q = babyBearP ^ 6 := by
  rw [Module.card_eq_pow_finrank (K := BabyBear) (V := Ext6Q), ext6Q_finrank, ZMod.card]

/-! ### The lane carrier reads injectively: lane equality is field equality

`{1, u, …, u⁵}` is the power basis of `AdjoinRoot ext6Polynomial`
(`AdjoinRoot.powerBasis`, `natDegree = 6`), so `toExt6` is injective and a
lane-level decision (`Ext6L` equality) is exactly a field-level one.  This is
what lets the computable controller's lane checks carry field theorems. -/

theorem toExt6_eq_sum (v : Fin 6 → BabyBear) :
    toExt6 v = ∑ i : Fin 6, v i • ext6Root ^ (i : Nat) := by
  simp [toExt6, Fin.sum_univ_six, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem ext6Polynomial_natDegree : ext6Polynomial.natDegree = 6 := by
  rw [ext6Polynomial]
  exact natDegree_X_pow_sub_C

theorem ext6Root_pow_linearIndependent :
    LinearIndependent BabyBear (fun i : Fin 6 => ext6Root ^ (i : Nat)) := by
  have hne : ext6Polynomial ≠ 0 := ext6Polynomial_irreducible.ne_zero
  have hdim : (AdjoinRoot.powerBasis hne).dim = 6 := by
    rw [AdjoinRoot.powerBasis_dim, ext6Polynomial_natDegree]
  have hcomp := (AdjoinRoot.powerBasis hne).basis.linearIndependent.comp
    (fun i : Fin 6 => Fin.cast hdim.symm i) (Fin.cast_injective _)
  convert hcomp using 1
  funext i
  rw [Function.comp_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen, Fin.val_cast]
  rfl

theorem toExt6_injective : Function.Injective toExt6 := by
  intro v w h
  have hzero : ∑ i : Fin 6, (v i - w i) • ext6Root ^ (i : Nat) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← toExt6_eq_sum, h, sub_self]
  have hall := (linearIndependent_iff'.mp ext6Root_pow_linearIndependent) Finset.univ
    (fun i => v i - w i) hzero
  funext i
  exact sub_eq_zero.mp (hall i (Finset.mem_univ i))

theorem Ext6L.toFn_injective : Function.Injective Ext6L.toFn := by
  intro a b h
  cases a
  cases b
  simp only [Ext6L.mk.injEq]
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4, congrFun h 5⟩

/-- **Lane equality is field equality.** -/
theorem readExt6_injective : Function.Injective readExt6 :=
  fun _ _ h => Ext6L.toFn_injective (toExt6_injective h)

theorem lane_eq_of_read {a b : Ext6L} (h : readExt6 a = readExt6 b) : a = b :=
  readExt6_injective h

/-! ## §2. The gamma event and its price -/

section Gamma

variable {m : Nat}

/-- The zero claim of the gate sumcheck is the gamma-batched residual list:
`Σ_b gammaResidualTable b = Σ_k γ^k · res_k`. -/
theorem sum_gammaResidualTable (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (gamma : Ext6Q) :
    ∑ b, gammaResidualTable d wv enc gamma b =
      ∑ k : Fin (descriptorResiduals d wv).length,
        gamma ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k) := by
  have key : ∀ b : Fin m → Bool, gammaResidualTable d wv enc gamma b =
      ∑ k : Fin (descriptorResiduals d wv).length,
        if enc k = b then
          gamma ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k)
        else 0 := by
    intro b
    by_cases hb : ∃ k, enc k = b
    · obtain ⟨k0, rfl⟩ := hb
      rw [gammaResidualTable_read, sum_ite_enc enc _ k0]
    · have hb' : ∀ k, enc k ≠ b := fun k hk => hb ⟨k, hk⟩
      have h1 : gammaResidualTable d wv enc gamma b = 0 := by
        simp [gammaResidualTable, gammaMask, hb']
      rw [h1]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp [hb' k]
  simp_rw [key]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]
  simp

/-- **The gamma event counted.**  A failing trace has a nonzero residual, so
`Σ_k γ^k res_k` is a nonzero polynomial in `γ` of degree `< N`:
`card_bad_eta_le` (REUSED) at zero trace, zero constants, zero weights. -/
theorem card_gammaZero_le (challenges : Finset Ext6Q)
    (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (hfail : ¬ descriptorHolds d wv) :
    (challenges.filter fun gamma : Ext6Q =>
      (∑ b, gammaResidualTable d wv enc gamma b) = 0).card ≤
      (descriptorResiduals d wv).length - 1 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (descriptorResiduals d wv).length,
      (descriptorResiduals d wv).get k ≠ 0 := by
    by_contra hall
    apply hfail
    rw [descriptorHolds_iff_residuals_zero]
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hx
    by_contra hne
    exact hall ⟨k, hne⟩
  have hdef : ∀ j, openingDefect (fun _ => (0 : Ext6Q))
      (fun k => algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k))
      (fun _ => 0) (fun _ => 0) j =
        algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get j) := by
    intro j
    simp [openingDefect]
  have h := card_bad_eta_le challenges (fun _ => (0 : Ext6Q))
    (fun k => algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k))
    (fun _ => 0) (fun _ => 0)
    ⟨k, by
      rw [hdef]
      intro h0
      exact hk ((algebraMap BabyBear Ext6Q).injective (h0.trans (map_zero _).symm))⟩
  refine le_trans (le_of_eq ?_) h
  congr 1
  apply Finset.filter_congr
  intro gamma _
  rw [sum_gammaResidualTable]
  simp only [hdef]

/-- **The gamma price, probability form:** `≤ (N−1)/|Ext6Q|`. -/
theorem gammaZero_prob_le (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (hfail : ¬ descriptorHolds d wv) :
    uniformProb Ext6Q (fun gamma => (∑ b, gammaResidualTable d wv enc gamma b) = 0) ≤
      (((descriptorResiduals d wv).length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q := by
  have hconv : uniformProb Ext6Q (fun gamma => (∑ b, gammaResidualTable d wv enc gamma b) = 0) =
      uniformProb Ext6Q (fun gamma => gamma ∈ Finset.univ.filter fun g : Ext6Q =>
        (∑ b, gammaResidualTable d wv enc g b) = 0) :=
    uniformProb_congr fun gamma => by simp
  rw [hconv, uniformProb_mem_finset]
  gcongr
  exact_mod_cast card_gammaZero_le Finset.univ d wv enc hfail

/-- The zero claim in lanes: the walker with weight `1`. -/
def laneZeroClaim (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L) :
    Ext6L :=
  walk gamma (fun c gpow => ext6MulL gpow (ext6OfBase c)) (fun _ => ext6One)
    (descriptorResiduals d wv) 0 ext6One ext6Zero

theorem read_laneZeroClaim (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (gamma : Ext6L) :
    readExt6 (laneZeroClaim d wv gamma) = ∑ b, gammaResidualTable d wv enc (readExt6 gamma) b := by
  rw [sum_gammaResidualTable, laneZeroClaim,
    read_walk_fin gamma (fun c gpow => ext6MulL gpow (ext6OfBase c)) (fun _ => ext6One)
      (fun c p => p * algebraMap BabyBear Ext6Q c)
      (fun c p => by simp [read_mul, read_ofBase]) (fun _ => 1) (fun _ => read_one) 0]
  apply Finset.sum_congr rfl
  intro k _
  rw [read_one, one_mul, mul_one]

end Gamma

/-! ## §3. The acceptance predicate and the ledger theorem -/

section Ledger

variable {Root Op : Type} [DecidableEq Root] {n m : Nat}

/-- **What the full-word gate proof's verifier decides**, read into the field:
the realizer accepted `v` against the root; every round's Boolean check passed
on the zero-anchored claim chain; the chain closes at the realized terminal.
`CommittedTerminalController.check` decides this in lanes. -/
structure GateProofAccepts (S : BindingCommitment Root BabyBear (Fin n) Op)
    (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool))
    (gamma : Ext6L) (r : Fin m → Ext6L) (rt : Root) (op : Opening n) (v : Ext6L)
    (prover : ℕ → Polynomial Ext6Q) : Prop where
  terminal : realize S.commit d encNat gamma r rt op = .ok v
  rounds : ∀ i, i < m → (prover i).eval 0 + (prover i).eval 1 =
    scChain 0 prover (chalOf fun i => readExt6 (r i)) i
  closes : scChain 0 prover (chalOf fun i => readExt6 (r i)) m = readExt6 v

/-- **The ledger theorem.**  A proof accepted against a root committing `w`
under the named `BindingCommitment` `S`, with round messages drawn from any
strategy `P` (evaluated at the actual challenges), means one of three things:
the committed trace satisfies the descriptor; or the gamma event -- the
batched residual list vanished at this `gamma`; or the sumcheck event -- the
adaptive verifier accepted the false zero claim against the honest MLE family
(`AdaptiveAcceptsFalse`, the tree's own event).  The terminal contributes no
event: `realize_sound` is exact under `S`. -/
theorem gateProof_sound (S : BindingCommitment Root BabyBear (Fin n) Op)
    (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool))
    (gamma : Ext6L) (r : Fin m → Ext6L) (w : Fin n → BabyBear) (op : Opening n) (v : Ext6L)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q)
    (hacc : GateProofAccepts S d encNat gamma r (S.commit w) op v
      (P (chalOf fun i => readExt6 (r i)))) :
    descriptorHolds d (traceOf w) ∨
      (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0 ∨
      AdaptiveAcceptsFalse P (mleHonest (gammaResidualTable d (traceOf w) enc (readExt6 gamma)))
        0 (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b)
        (fun i => readExt6 (r i)) := by
  by_cases hd : descriptorHolds d (traceOf w)
  · exact Or.inl hd
  by_cases hz : (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0
  · exact Or.inr (Or.inl hz)
  refine Or.inr (Or.inr ⟨hacc.rounds, ?_, fun h => hz h.symm⟩)
  rw [hacc.closes, scChain_mleHonest_final]
  exact realize_sound S d encNat gamma r w op v hacc.terminal enc hEnc

/-- **The sumcheck price**: `mle_sumcheck_soundness` (REUSED) at the gate
table -- `m · 1/|Ext6Q|` against any prefix-measurable degree-`≤ 1` strategy. -/
theorem sumcheck_prob_le (table : (Fin m → Bool) → Ext6Q)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : PrefixMeasurable P)
    (hdeg : ∀ (χ : ℕ → Ext6Q) (i : ℕ), i < m →
      (P χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → Ext6Q) (AdaptiveAcceptsFalse P (mleHonest table) 0 (∑ b, table b)) ≤
      (m : ℝ) * (1 / Fintype.card Ext6Q) :=
  mle_sumcheck_soundness hpm hdeg

/-- The number the unit was asked to carry, `m · 2/|F| + 0`: a corollary, not
the sharp price.  The `2` is the per-round price of the factored quadratic
protocol (`basefoldSumcheckRbr_err`, `Accepts`' degree-`< 3` messages), which
this degree-one verifier does not pay; the `+ 0` is the terminal's error under
`S`. -/
theorem sumcheck_prob_le_two (table : (Fin m → Bool) → Ext6Q)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : PrefixMeasurable P)
    (hdeg : ∀ (χ : ℕ → Ext6Q) (i : ℕ), i < m →
      (P χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → Ext6Q) (AdaptiveAcceptsFalse P (mleHonest table) 0 (∑ b, table b)) ≤
      (m : ℝ) * (2 / Fintype.card Ext6Q) + 0 := by
  have h := sumcheck_prob_le table P hpm hdeg
  have hle : (m : ℝ) * (1 / Fintype.card Ext6Q) ≤ (m : ℝ) * (2 / Fintype.card Ext6Q) := by
    gcongr
    norm_num
  linarith

/-- The sharp price with the field size written out: `m / p^6`. -/
theorem sumcheck_prob_le_explicit (table : (Fin m → Bool) → Ext6Q)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : PrefixMeasurable P)
    (hdeg : ∀ (χ : ℕ → Ext6Q) (i : ℕ), i < m →
      (P χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → Ext6Q) (AdaptiveAcceptsFalse P (mleHonest table) 0 (∑ b, table b)) ≤
      (m : ℝ) * (1 / ((babyBearP : ℝ) ^ 6)) := by
  have h := sumcheck_prob_le table P hpm hdeg
  rw [card_ext6] at h
  exact_mod_cast h

end Ledger

/-! ## §4. The gamma leg on the emitted demo descriptor, decided -/

namespace DemoInstance

open CommittedTerminalRealizer.DemoInstance

/-- The satisfying trace's batched residual is `0` (the zero claim is true). -/
theorem laneZeroClaim_honest_zero :
    laneZeroClaim demoDescriptor (traceOf demoWord) gamma = ext6Zero := by
  decide +kernel

/-- **Teeth for the gamma leg, decided:** at the demo gamma the tampered
trace's batched residual is NONZERO -- the gamma event does not occur, and the
sumcheck's zero claim is false for it. -/
theorem laneZeroClaim_tampered_ne_zero :
    laneZeroClaim demoDescriptor (traceOf tamperedWord) gamma ≠ ext6Zero := by
  decide +kernel

/-- The same fact in the field, through the bridge: the tampered trace's
zero claim is false at `readExt6 gamma`. -/
theorem tampered_zeroClaim_false :
    (∑ b, gammaResidualTable demoDescriptor (traceOf tamperedWord)
      (residualEmbedding demoDescriptor (traceOf tamperedWord) demo_residuals_fit)
      (readExt6 gamma) b) ≠ 0 := by
  rw [← read_laneZeroClaim]
  intro h
  apply laneZeroClaim_tampered_ne_zero
  have h0 : readExt6 (laneZeroClaim demoDescriptor (traceOf tamperedWord) gamma) =
      readExt6 ext6Zero := by rw [h, read_zero]
  exact readExt6_injective h0

end DemoInstance

#check @gateProof_sound
#check @gammaZero_prob_le
#check @sumcheck_prob_le
#check @card_ext6

/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.card_ext6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_ext6
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.gateProof_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.gammaZero_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gammaZero_prob_le
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.sumcheck_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck_prob_le
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.sumcheck_prob_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck_prob_le_two
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.DemoInstance.laneZeroClaim_tampered_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.laneZeroClaim_tampered_ne_zero
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.readExt6_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readExt6_injective
/-- info: 'Minidregg.Compiler.CommittedTerminalCompose.DemoInstance.tampered_zeroClaim_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.tampered_zeroClaim_false

end Minidregg.Compiler.CommittedTerminalCompose
