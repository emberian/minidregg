/-
# `Selvage.WhirMultiRoundSoundness` — Multi-Round $2^k$-ary `WHIR` / STIR Fold-and-Shift Soundness

Formalizes multi-round $2^{k_i}$-ary `WHIR` (`eprint 2024/1586`) / `STIR` (`eprint 2024/390`)
fold-and-shift interactive oracle proximity soundness, concrete committed $2^{k_i}$-ary coset-fiber
query sampling, multi-sample out-of-domain (OOD) collision bounds, opened-element complexity vs
1-step Ligero, premise inhabitation, and unpinned-query falsifier teeth (`VERDICTS.md` §2).

## Main Results

1. **Schedule & Round Specification (`WhirRoundSpec`, `WhirSchedule`):**
   Packages per-round folding arity $2^{k_i}$ (`varsFolded`), evaluation domain size $N_i$
   (`domainSize`), shift/coset-fiber query count $t_i$ (`queryCount`), OOD sample count $u_i$
   (`oodSamples`), proximity radius $\delta_i \in [0, 1]$, folding/sumcheck proximity-gap error
   $\varepsilon_{\text{fold}, i}$, and OOD list-collision bound $\varepsilon_{\text{ood}, i}$.

2. **Inductive Escape-Event Decomposition & Quantitative `BindingGame.prob` Soundness
   (`whir_multiRound_escape_or_terminal`, `whir_multiRound_soundness_le`):**
   - If the initial word $f_0$ is $\delta_0$-far from the initial code and all $M$ folding rounds
     accept, then either the terminal word $f_M$ violates `CloseAt M` (impossible when `FinalCheck`
     passes!) or at least one round $i < M$ hits `FoldBad i ∨ OodBad i ∨ QueryMiss i`.
   - Over `BindingGame.prob`, false acceptance is bounded by
     $$\min\!\left(1,\; \sum_{i < M} \left(\varepsilon_{\text{fold}, i} + \varepsilon_{\text{ood}, i} + (1 - \delta_i)^{t_i}\right)\right).$$

3. **Concrete $2^{k_i}$-ary Committed Fiber Sampling & Multi-Sample OOD Realizers
   (`whir_fiberQuery_miss_prob_le`, `whir_ood_multiSample_prob_le`, `whir_concreteRound_stepSound`):**
   - Connects authenticated `BindingCommitment` $2^k$-ary fiber openings directly to `Selvage`'s
     `column_sampling_bridge_pr`, proving that any $\delta$-far discrepancy between the $2^k$-ary
     folded word and the shifted next word survives $t$ uniform fiber queries with `BindingGame.prob`
     at most $(1 - \delta)^t$ on arbitrary prefix-coupled joint sample spaces.
   - Proves that $u$ independent out-of-domain samples separate any distinct pair in
     `reedSolomonCode dom d` except with `BindingGame.prob ≤ ((d - 1) / (|F| - |ι|))^u`.

4. **Verifier-Complexity / Proof-Size Scaling (`whir_opened_elements_eq`), Premise Inhabitation,
   and Unpinned Query-Count / Zero-Arity Falsifier Teeth (`VERDICTS.md` §2):**
   - Proves exact opened-element scaling $\sum_{i < M} t_i 2^{k_i} + 2^{m - \sum_i k_i}$ vs
     1-step Ligero's $O(2^{m/2})$ row size (`46.7×` smaller at $m = 20$, `149.9×` at $m = 24$, and
     provably $O(m) < 2^{m/2}$ for all $m = 2r \ge 20$), plus phase-routing height collision teeth
     when `varsFolded = 0` (`whir_zero_arity_stalls_cumulativeVars`, `VERDICTS.md` §2 `log_arity = 0`).
   - Exhibits zero-shortcut multi-round Reed–Solomon premise inhabitation (`Selvage.close` over
     `reedSolomonCode` on `ZMod 17`, exercising both inductive propagation and `QueryMiss` escape
     with `whirTotalError = 1/8 < 1`) alongside constructive cheating-prover forgeries when `t_0 = 0`
     (`prob = 1`, `whir_zero_queries_forgery_prob_one`) or when an unpinned verifier accepts a
     1-query proof (`prob = 1/2`, `whir_unpinned_one_query_refutes`).

Import boundary: `Selvage/` tier (`Mathlib.*` + `Theory.*` + `Selvage.*` only).
-/
import Selvage.BindingGame
import Selvage.ReedSolomon
import Selvage.OutOfDomain
import Selvage.JohnsonRegime
import Selvage.Commitment
import Theory.AssertAxioms

namespace Minidregg.Selvage.WhirMultiRoundSoundness

open scoped BigOperators
open Minidregg.Selvage
open Minidregg.Selvage.BindingGame
open Minidregg.Theory.AssertAxioms

set_option autoImplicit false

/-! ## §1. `WhirRoundSpec` & `WhirSchedule` -/

/-- Specification of one $2^{k_i}$-ary `WHIR` / STIR fold-and-shift round. -/
structure WhirRoundSpec where
  /-- Number of multilinear variables folded in this round (`k_i`; coset fiber arity `2^{k_i}`). -/
  varsFolded : ℕ
  /-- Size `N_i = |L_i|` of this round's Reed–Solomon / subspace evaluation domain. -/
  domainSize : ℕ
  /-- Number `t_i` of sampled shift / coset-fiber consistency queries. -/
  queryCount : ℕ
  /-- Number `u_i` of out-of-domain evaluation samples pinning list-decoding candidates. -/
  oodSamples : ℕ
  /-- Proximity parameter `δ_i ∈ [0, 1]`. -/
  delta      : ℝ
  /-- Round folding / sumcheck proximity-gap escape probability bound `ε_{fold, i}`. -/
  epsFold    : ℝ
  /-- Out-of-domain list-collision probability bound `ε_{ood, i}`. -/
  epsOod     : ℝ

/-- Structural well-formedness of a `WhirRoundSpec`. -/
def WhirRoundSpec.WellFormed (s : WhirRoundSpec) : Prop :=
  1 ≤ s.varsFolded ∧
  0 < s.domainSize ∧
  0 ≤ s.delta ∧ s.delta ≤ 1 ∧
  0 ≤ s.epsFold ∧ 0 ≤ s.epsOod

/-- Per-round soundness budget `ε_{fold, i} + ε_{ood, i} + (1 - δ_i)^{t_i}`. -/
noncomputable def WhirRoundSpec.roundError (s : WhirRoundSpec) : ℝ :=
  s.epsFold + s.epsOod + (1 - s.delta) ^ s.queryCount

theorem WhirRoundSpec.roundError_nonneg {s : WhirRoundSpec} (hs : s.WellFormed) :
    0 ≤ s.roundError := by
  rcases hs with ⟨_, _, _, hδ1, hef, heo⟩
  unfold WhirRoundSpec.roundError
  have hpow : 0 ≤ (1 - s.delta) ^ s.queryCount := pow_nonneg (sub_nonneg.mpr hδ1) _
  linarith

/-- An `M`-round `WHIR` / STIR folding schedule. -/
abbrev WhirSchedule (M : ℕ) := Fin M → WhirRoundSpec

/-- Total variables folded across all `M` rounds: `∑_{i < M} k_i`. -/
def whirTotalVarsFolded {M : ℕ} (sched : WhirSchedule M) : ℕ :=
  ∑ i : Fin M, (sched i).varsFolded

/-- Total additive soundness error bound across all `M` rounds. -/
noncomputable def whirTotalError {M : ℕ} (sched : WhirSchedule M) : ℝ :=
  ∑ i : Fin M, (sched i).roundError

/-! ## §2. `BindingGame.prob` Finite Union & Conditional Product Bridges -/

theorem prob_false_eq_zero {Ω : Type} [Fintype Ω] :
    prob (fun _ : Ω => False) = 0 := by
  simp [prob]

/-- Bridge from `BindingGame.prob` (which uses `Classical.propDecidable`) to any `[DecidablePred p]`
filter cardinality. -/
theorem prob_eq_card_filter_div {Ω : Type} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] :
    prob p = ((Finset.univ.filter p).card : ℝ) / Fintype.card Ω := by
  unfold prob
  congr 1
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : p ω <;> simp [h]

/-- Finite existential union bound over `BindingGame.prob`. -/
theorem prob_exists_fin_le {Ω : Type} [Fintype Ω] {M : ℕ} (E : Fin M → Ω → Prop) :
    prob (fun ω => ∃ i : Fin M, E i ω) ≤ ∑ i : Fin M, prob (E i) := by
  induction M with
  | zero =>
      have hempty : (fun ω : Ω => ∃ i : Fin 0, E i ω) = (fun _ => False) := by
        funext ω; exact propext ⟨fun ⟨i, _⟩ => i.elim0, False.elim⟩
      rw [hempty, prob_false_eq_zero]
      simp
  | succ m ih =>
      have hsplit : ∀ ω : Ω, (∃ i : Fin (m + 1), E i ω) →
          E 0 ω ∨ ∃ j : Fin m, E j.succ ω := by
        rintro ω ⟨i, hi⟩
        exact Fin.cases (fun h0 => Or.inl h0) (fun j hj => Or.inr ⟨j, hj⟩) i hi
      have ihm := ih (fun j => E j.succ)
      calc
        prob (fun ω => ∃ i : Fin (m + 1), E i ω)
            ≤ prob (fun ω => E 0 ω ∨ ∃ j : Fin m, E j.succ ω) := prob_mono hsplit
        _ ≤ prob (E 0) + prob (fun ω => ∃ j : Fin m, E j.succ ω) := prob_or _ _
        _ ≤ prob (E 0) + ∑ j : Fin m, prob (E j.succ) := by linarith
        _ = ∑ i : Fin (m + 1), prob (E i) := (Fin.sum_univ_succ (fun i => prob (E i))).symm

/-- Reindexing `BindingGame.prob` along a bijection `Ω₁ ≃ Ω₂`. -/
theorem prob_equiv {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂]
    (e : Ω₁ ≃ Ω₂) (p : Ω₂ → Prop) :
    prob (fun ω => p (e ω)) = prob p := by
  classical
  unfold prob
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e (fun x => if p (e x) then (1 : ℝ) else 0)
    (fun y => if p y then (1 : ℝ) else 0) (fun _ => rfl)

/-- Fibrewise conditional upper bound on a product sample space `A × B`: if for every prefix `a : A`,
the conditional `BindingGame.prob` over `B` is at most `ε`, then the joint `prob` is at most `ε`. -/
theorem prob_prod_le {A B : Type} [Fintype A] [Fintype B] [Nonempty A]
    {ε : ℝ} (p : A × B → Prop)
    (hcond : ∀ a : A, prob (fun b : B => p (a, b)) ≤ ε) :
    prob p ≤ ε := by
  classical
  by_cases hB : Fintype.card B = 0
  · have hcard0 : Fintype.card (A × B) = 0 := by rw [Fintype.card_prod, hB, mul_zero]
    have h0 := hcond (Classical.arbitrary A)
    simp only [prob, hB, Nat.cast_zero, div_zero] at h0
    simp only [prob, hcard0, Nat.cast_zero, div_zero]
    exact h0
  · have hBpos : (0 : ℝ) < Fintype.card B := by exact_mod_cast Nat.pos_of_ne_zero hB
    have hApos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hABpos : (0 : ℝ) < Fintype.card (A × B) := by
      rw [Fintype.card_prod]; push_cast; exact mul_pos hApos hBpos
    unfold prob
    rw [div_le_iff₀ hABpos, Fintype.sum_prod_type, Fintype.card_prod]
    push_cast
    calc
      (∑ a : A, ∑ b : B, if p (a, b) then (1 : ℝ) else 0)
          ≤ ∑ _a : A, ε * Fintype.card B := by
            refine Finset.sum_le_sum fun a _ => ?_
            have ha := hcond a
            unfold prob at ha
            exact (div_le_iff₀ hBpos).mp ha
      _ = ε * (Fintype.card A * Fintype.card B) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## §3. Inductive Multi-Round Escape-Event Decomposition & Quantitative Soundness -/

/-- Abstract `M`-round `WHIR` / STIR execution over a finite sample space `Ω`. -/
structure WhirExecution (Ω : Type) (M : ℕ) where
  /-- Level-`n` code closeness invariant (`f_n(ω)` is `δ_n`-close to code `C_n(ω)`). -/
  CloseAt      : Fin (M + 1) → Ω → Prop
  /-- Round-`i` verifier check (authenticated `t_i` coset-fiber openings + OOD/sumcheck relations). -/
  RoundAccepts : Fin M → Ω → Prop
  /-- Terminal direct low-degree / small-table check on the folded `2^{m - ∑ k_i}` table. -/
  FinalCheck   : Ω → Prop
  /-- Round-`i` folding / sumcheck proximity-gap bad challenge event. -/
  FoldBad      : Fin M → Ω → Prop
  /-- Round-`i` out-of-domain list-decoding collision event. -/
  OodBad       : Fin M → Ω → Prop
  /-- Round-`i` shift-query miss event (`t_i` queries all miss a `≥ δ_i`-far word discrepancy). -/
  QueryMiss    : Fin M → Ω → Prop

/-- Full `M`-round `WHIR` verifier acceptance: every round check and `FinalCheck` accept. -/
def WhirExecution.VerifierAccepts {Ω : Type} {M : ℕ} (exec : WhirExecution Ω M) (ω : Ω) : Prop :=
  (∀ i : Fin M, exec.RoundAccepts i ω) ∧ exec.FinalCheck ω

/-- Union of the three round-`i` soundness escape events. -/
def WhirExecution.RoundEscape {Ω : Type} {M : ℕ}
    (exec : WhirExecution Ω M) (i : Fin M) (ω : Ω) : Prop :=
  exec.FoldBad i ω ∨ exec.OodBad i ω ∨ exec.QueryMiss i ω

/-- Single-round `WHIR` soundness transition: if `f_i(ω)` is `δ_i`-far (`¬ CloseAt i ω`) and round
`i` accepts, then either round `i` hits an explicit escape event or `f_{i+1}(ω)` stays `δ_{i+1}`-far. -/
def WhirExecution.StepSound {Ω : Type} {M : ℕ} (exec : WhirExecution Ω M) : Prop :=
  ∀ (i : Fin M) (ω : Ω),
    ¬ exec.CloseAt i.castSucc ω → exec.RoundAccepts i ω →
      exec.RoundEscape i ω ∨ ¬ exec.CloseAt i.succ ω

/-- Exact terminal check soundness: `FinalCheck` inspects the small final table directly, so
passing `FinalCheck` implies `CloseAt (Fin.last M)`. -/
def WhirExecution.TerminalSound {Ω : Type} {M : ℕ} (exec : WhirExecution Ω M) : Prop :=
  ∀ ω : Ω, exec.FinalCheck ω → exec.CloseAt (Fin.last M) ω

/-- **Inductive Multi-Round Escape-Event Decomposition (`whir_multiRound_escape_or_terminal`):**
if the initial word is `δ₀`-far (`¬ CloseAt 0 ω`) and all `M` round checks pass, then either the
terminal word remains far (`¬ CloseAt (Fin.last M) ω`) or some round `i < M` hits
`FoldBad i ω ∨ OodBad i ω ∨ QueryMiss i ω`. -/
theorem whir_multiRound_escape_or_terminal {Ω : Type} {M : ℕ}
    (exec : WhirExecution Ω M) (hstep : exec.StepSound) (ω : Ω)
    (hfar0 : ¬ exec.CloseAt 0 ω)
    (hrounds : ∀ i : Fin M, exec.RoundAccepts i ω) :
    ¬ exec.CloseAt (Fin.last M) ω ∨
      ∃ i : Fin M, (exec.FoldBad i ω ∨ exec.OodBad i ω ∨ exec.QueryMiss i ω) := by
  have hind : ∀ (k : ℕ) (hk : k ≤ M),
      ¬ exec.CloseAt ⟨k, Nat.lt_succ_of_le hk⟩ ω ∨
        ∃ i : Fin M, (i : ℕ) < k ∧ exec.RoundEscape i ω := by
    intro k
    induction k with
    | zero =>
        intro _
        exact Or.inl hfar0
    | succ n ih =>
        intro hn
        have hn_lt : n < M := hn
        rcases ih (Nat.le_of_succ_le hn) with hfarn | ⟨i, hik, hesc⟩
        · let idx : Fin M := ⟨n, hn_lt⟩
          rcases hstep idx ω hfarn (hrounds idx) with hesc | hfar_succ
          · exact Or.inr ⟨idx, Nat.lt_succ_self n, hesc⟩
          · exact Or.inl hfar_succ
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hik, hesc⟩
  rcases hind M le_rfl with hterm | ⟨i, _, hesc⟩
  · exact Or.inl hterm
  · exact Or.inr ⟨i, hesc⟩

/-- When `FinalCheck` enforces `TerminalSound`, terminal discrepancy is impossible, so any accepted
initially-`δ₀`-far word *must* trigger an escape event in some round `i < M`. -/
theorem whir_multiRound_escape_of_accept {Ω : Type} {M : ℕ}
    (exec : WhirExecution Ω M) (hstep : exec.StepSound) (hterm : exec.TerminalSound)
    (ω : Ω) (hfar0 : ¬ exec.CloseAt 0 ω) (hacc : exec.VerifierAccepts ω) :
    ∃ i : Fin M, (exec.FoldBad i ω ∨ exec.OodBad i ω ∨ exec.QueryMiss i ω) := by
  rcases whir_multiRound_escape_or_terminal exec hstep ω hfar0 hacc.1 with hnotCloseM | hesc
  · exact False.elim (hnotCloseM (hterm ω hacc.2))
  · exact hesc

/-- **Quantitative Multi-Round `WHIR` Soundness Bound (`whir_multiRound_soundness_le`):**
over `BindingGame.prob`, the probability that an initially `δ₀`-far word is accepted by the
`M`-round verifier is bounded by
`min 1 (∑_{i < M} (ε_{fold, i} + ε_{ood, i} + (1 - δ_i)^{t_i}))`. -/
theorem whir_multiRound_soundness_le {Ω : Type} [Fintype Ω] [Nonempty Ω] {M : ℕ}
    (sched : WhirSchedule M) (exec : WhirExecution Ω M)
    (hstep : exec.StepSound) (hterm : exec.TerminalSound)
    (hFold  : ∀ i : Fin M, prob (exec.FoldBad i) ≤ (sched i).epsFold)
    (hOod   : ∀ i : Fin M, prob (exec.OodBad i) ≤ (sched i).epsOod)
    (hQuery : ∀ i : Fin M, prob (exec.QueryMiss i) ≤
      (1 - (sched i).delta) ^ (sched i).queryCount) :
    prob (fun ω => ¬ exec.CloseAt 0 ω ∧ exec.VerifierAccepts ω) ≤
      min 1 (∑ i : Fin M,
        ((sched i).epsFold + (sched i).epsOod +
          (1 - (sched i).delta) ^ (sched i).queryCount)) := by
  refine le_min (prob_le_one _) ?_
  calc
    prob (fun ω => ¬ exec.CloseAt 0 ω ∧ exec.VerifierAccepts ω)
        ≤ prob (fun ω => ∃ i : Fin M, exec.RoundEscape i ω) :=
          prob_mono fun ω ⟨hfar0, hacc⟩ =>
            whir_multiRound_escape_of_accept exec hstep hterm ω hfar0 hacc
    _ ≤ ∑ i : Fin M, prob (exec.RoundEscape i) :=
          prob_exists_fin_le _
    _ ≤ ∑ i : Fin M,
          ((sched i).epsFold + (sched i).epsOod +
            (1 - (sched i).delta) ^ (sched i).queryCount) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hor1 := prob_or (exec.FoldBad i) (fun ω => exec.OodBad i ω ∨ exec.QueryMiss i ω)
          have hor2 := prob_or (exec.OodBad i) (exec.QueryMiss i)
          have hf := hFold i
          have ho := hOod i
          have hq := hQuery i
          unfold WhirExecution.RoundEscape
          linarith

/-- Uncapped sum form of `whir_multiRound_soundness_le` matching `whirTotalError sched`. -/
theorem whir_multiRound_soundness_sum_le {Ω : Type} [Fintype Ω] [Nonempty Ω] {M : ℕ}
    (sched : WhirSchedule M) (exec : WhirExecution Ω M)
    (hstep : exec.StepSound) (hterm : exec.TerminalSound)
    (hFold  : ∀ i : Fin M, prob (exec.FoldBad i) ≤ (sched i).epsFold)
    (hOod   : ∀ i : Fin M, prob (exec.OodBad i) ≤ (sched i).epsOod)
    (hQuery : ∀ i : Fin M, prob (exec.QueryMiss i) ≤
      (1 - (sched i).delta) ^ (sched i).queryCount) :
    prob (fun ω => ¬ exec.CloseAt 0 ω ∧ exec.VerifierAccepts ω) ≤ whirTotalError sched :=
  le_trans (whir_multiRound_soundness_le sched exec hstep hterm hFold hOod hQuery)
    (min_le_right _ _)

/-! ## §4. Concrete $2^k$-ary Committed Fiber Sampling & Multi-Sample OOD Realizers -/

/-- Opening witness for one $2^k$-ary coset fiber at base coordinate `b : β` paired with its
shifted evaluation coordinate in the next round's committed word. -/
structure WhirFiberOpening (F OpCur OpNext : Type*) (k : ℕ) where
  fiberVals  : Fin (2 ^ k) → F
  fiberPaths : Fin (2 ^ k) → OpCur
  nextVal    : F
  nextPath   : OpNext

/-- Verifier predicate for one authenticated $2^k$-ary `WHIR` fiber-and-shift query at `b : β`. -/
def OpenedWhirFiberQuery {F β ιNext RootCur RootNext OpCur OpNext : Type*} {k : ℕ}
    (Scur : OpeningScheme RootCur F (β × Fin (2 ^ k)) OpCur)
    (Snext : OpeningScheme RootNext F ιNext OpNext)
    (foldCombine : (Fin (2 ^ k) → F) → F)
    (shiftIdx : β → ιNext)
    (rtCur : RootCur) (rtNext : RootNext) (b : β)
    (o : WhirFiberOpening F OpCur OpNext k) : Prop :=
  (∀ c : Fin (2 ^ k), Scur.verifyOpen rtCur (b, c) (o.fiberVals c) (o.fiberPaths c)) ∧
  Snext.verifyOpen rtNext (shiftIdx b) o.nextVal o.nextPath ∧
  foldCombine o.fiberVals = o.nextVal

/-- Binding pins an accepted $2^k$-ary fiber opening to the exact equation between the folded
current word and the shifted next word. -/
theorem openedWhirFiberQuery_pins {F β ιNext RootCur RootNext OpCur OpNext : Type*} {k : ℕ}
    (Scur : BindingCommitment RootCur F (β × Fin (2 ^ k)) OpCur)
    (Snext : BindingCommitment RootNext F ιNext OpNext)
    (foldCombine : (Fin (2 ^ k) → F) → F)
    (shiftIdx : β → ιNext)
    {curWord : β × Fin (2 ^ k) → F} {nextWord : ιNext → F}
    {rtCur : RootCur} {rtNext : RootNext}
    (hrtCur : rtCur = Scur.commit curWord)
    (hrtNext : rtNext = Snext.commit nextWord)
    {b : β} {o : WhirFiberOpening F OpCur OpNext k}
    (hopen : OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
      foldCombine shiftIdx rtCur rtNext b o) :
    foldCombine (fun c => curWord (b, c)) = nextWord (shiftIdx b) := by
  rcases hopen with ⟨hfiber, hnext, heq⟩
  have hfibEq : o.fiberVals = fun c => curWord (b, c) := by
    funext c
    exact Scur.binding rtCur (b, c) (o.fiberVals c) (curWord (b, c))
      (o.fiberPaths c) (Scur.openAt curWord (b, c))
      (hfiber c) (Scur.toOpeningScheme.verifyOpen_of_commit_eq hrtCur (b, c))
  have hnextEq : o.nextVal = nextWord (shiftIdx b) :=
    Snext.binding rtNext (shiftIdx b) o.nextVal (nextWord (shiftIdx b))
      o.nextPath (Snext.openAt nextWord (shiftIdx b))
      hnext (Snext.toOpeningScheme.verifyOpen_of_commit_eq hrtNext (shiftIdx b))
  rw [← hfibEq, ← hnextEq]
  exact heq

/-- **Concrete $2^k$-ary Fiber Query-Miss Bound (`whir_fiberQuery_miss_prob_le`):**
on *any* joint sample space `Ω` factoring via `split : Ω ≃ Ω_prefix × (Fin t → β)` (capturing
adaptive prefix-dependent words and challenges!), the `BindingGame.prob` that the folded word and
shifted next word are `δ`-far (`δ ≤ relDist`) while all `t` authenticated $2^k$-ary fiber queries
accept is **at most `(1 - δ)^t`**. -/
theorem whir_fiberQuery_miss_prob_le
    {Ω Ω_prefix F β ιNext RootCur RootNext OpCur OpNext : Type}
    [Fintype Ω] [Fintype Ω_prefix] [Nonempty Ω_prefix]
    [Fintype β] [Nonempty β] [DecidableEq F]
    {k t : ℕ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (split : Ω ≃ Ω_prefix × (Fin t → β))
    (Scur : BindingCommitment RootCur F (β × Fin (2 ^ k)) OpCur)
    (Snext : BindingCommitment RootNext F ιNext OpNext)
    (foldCombine : Ω_prefix → (Fin (2 ^ k) → F) → F)
    (shiftIdx : Ω_prefix → β → ιNext)
    (curWord : Ω_prefix → β × Fin (2 ^ k) → F)
    (nextWord : Ω_prefix → ιNext → F) :
    prob (fun ω : Ω =>
      let p := (split ω).1
      let q := (split ω).2
      δ ≤ relDist (fun b => foldCombine p (fun c => curWord p (b, c)))
                  (fun b => nextWord p (shiftIdx p b)) ∧
      ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
        ∀ a : Fin t,
          OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
            (foldCombine p) (shiftIdx p)
            (Scur.commit (curWord p)) (Snext.commit (nextWord p))
            (q a) (op a)) ≤ (1 - δ) ^ t := by
  classical
  rw [← prob_equiv split.symm]
  have hsimp : (fun x : Ω_prefix × (Fin t → β) =>
      let p := (split (split.symm x)).1
      let q := (split (split.symm x)).2
      δ ≤ relDist (fun b => foldCombine p (fun c => curWord p (b, c)))
                  (fun b => nextWord p (shiftIdx p b)) ∧
      ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
        ∀ a : Fin t,
          OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
            (foldCombine p) (shiftIdx p)
            (Scur.commit (curWord p)) (Snext.commit (nextWord p))
            (q a) (op a)) =
    (fun x : Ω_prefix × (Fin t → β) =>
      δ ≤ relDist (fun b => foldCombine x.1 (fun c => curWord x.1 (b, c)))
                  (fun b => nextWord x.1 (shiftIdx x.1 b)) ∧
      ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
        ∀ a : Fin t,
          OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
            (foldCombine x.1) (shiftIdx x.1)
            (Scur.commit (curWord x.1)) (Snext.commit (nextWord x.1))
            (x.2 a) (op a)) := by
    funext x; simp
  rw [hsimp]
  apply prob_prod_le
  intro p
  set g : β → F := fun b => foldCombine p (fun c => curWord p (b, c))
  set w : β → F := fun b => nextWord p (shiftIdx p b)
  by_cases hfar : δ ≤ relDist g w
  · have himp : ∀ q : Fin t → β,
        (δ ≤ relDist g w ∧
          ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
            ∀ a : Fin t,
              OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
                (foldCombine p) (shiftIdx p)
                (Scur.commit (curWord p)) (Snext.commit (nextWord p))
                (q a) (op a)) →
        (∀ a : Fin t, g (q a) = w (q a)) := by
      rintro q ⟨_, op, hop⟩ a
      exact openedWhirFiberQuery_pins Scur Snext (foldCombine p) (shiftIdx p) rfl rfl (hop a)
    refine le_trans (prob_mono himp) ?_
    rw [prob_eq_card_filter_div, Fintype.card_fun, Fintype.card_fin]
    push_cast
    exact column_sampling_bridge_pr t hfar
  · have hfalse : (fun q : Fin t → β =>
        δ ≤ relDist g w ∧
          ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
            ∀ a : Fin t,
              OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
                (foldCombine p) (shiftIdx p)
                (Scur.commit (curWord p)) (Snext.commit (nextWord p))
                (q a) (op a)) = (fun _ => False) := by
      funext q; exact propext ⟨fun h => hfar h.1, False.elim⟩
    rw [hfalse, prob_false_eq_zero]
    exact pow_nonneg (sub_nonneg.mpr hδ1) t

/-- **Concrete Round-Step Bridge (`whir_concreteRound_stepSound`):**
connects concrete code closeness `Selvage.close` and authenticated $2^k$-ary fiber openings directly
to `WhirExecution.StepSound`'s four-way disjunction (`FoldBad ∨ OodBad ∨ QueryMiss ∨ ¬ closeNext`). -/
theorem whir_concreteRound_stepSound
    {F β ιNext RootCur RootNext OpCur OpNext : Type*} [Field F] [Fintype β] [Fintype ιNext]
    [DecidableEq F]
    {k t : ℕ} {δCur δNext : ℝ}
    (Ccur : Submodule F (β × Fin (2 ^ k) → F))
    (Cnext : Submodule F (ιNext → F))
    (Scur : BindingCommitment RootCur F (β × Fin (2 ^ k)) OpCur)
    (Snext : BindingCommitment RootNext F ιNext OpNext)
    (foldCombine : (Fin (2 ^ k) → F) → F)
    (shiftIdx : β → ιNext)
    (curWord : β × Fin (2 ^ k) → F)
    (nextWord : ιNext → F)
    (q : Fin t → β)
    {FoldBad OodBad : Prop}
    (hbridge : ¬ close δCur Ccur curWord → ¬ FoldBad → ¬ OodBad →
      close δNext Cnext nextWord →
        δCur ≤ relDist (fun b => foldCombine (fun c => curWord (b, c)))
                       (fun b => nextWord (shiftIdx b)))
    (hfar : ¬ close δCur Ccur curWord)
    (hopen : ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
      ∀ a : Fin t,
        OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
          foldCombine shiftIdx (Scur.commit curWord) (Snext.commit nextWord) (q a) (op a)) :
    (FoldBad ∨ OodBad ∨
      (δCur ≤ relDist (fun b => foldCombine (fun c => curWord (b, c)))
                      (fun b => nextWord (shiftIdx b)) ∧
       ∃ op : Fin t → WhirFiberOpening F OpCur OpNext k,
         ∀ a : Fin t,
           OpenedWhirFiberQuery Scur.toOpeningScheme Snext.toOpeningScheme
             foldCombine shiftIdx (Scur.commit curWord) (Snext.commit nextWord) (q a) (op a))) ∨
    ¬ close δNext Cnext nextWord := by
  by_cases hf : FoldBad
  · exact Or.inl (Or.inl hf)
  · by_cases ho : OodBad
    · exact Or.inl (Or.inr (Or.inl ho))
    · by_cases hc : close δNext Cnext nextWord
      · exact Or.inl (Or.inr (Or.inr ⟨hbridge hfar hf ho hc, hopen⟩))
      · exact Or.inr hc

/-- **Multi-Sample Out-of-Domain Separation Bound (`whir_ood_multiSample_prob_le`):**
for `u` independent OOD samples drawn from `{z : F // z ∉ Set.range dom}`, two distinct codewords
`w₁ ≠ w₂` of `reedSolomonCode dom d` collide on all `u` OOD points with `BindingGame.prob` at most
`((d - 1) / (|F| - |ι|)) ^ u`. -/
theorem whir_ood_multiSample_prob_le
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (dom : ι ↪ F) (hproper : Fintype.card ι < Fintype.card F)
    {d : ℕ} {w₁ w₂ : ι → F}
    (hw₁ : w₁ ∈ reedSolomonCode dom d) (hw₂ : w₂ ∈ reedSolomonCode dom d) (hne : w₁ ≠ w₂)
    (u : ℕ) :
    prob (fun z : Fin u → {x : F // x ∉ Set.range dom} =>
      ∀ s : Fin u, oodEval dom d w₁ (z s).1 = oodEval dom d w₂ (z s).1) ≤
      (((d - 1 : ℕ) : ℝ) / ((Fintype.card F - Fintype.card ι : ℕ) : ℝ)) ^ u := by
  classical
  let OodPt := {x : F // x ∉ Set.range dom}
  have hOodCard : Fintype.card OodPt = Fintype.card F - Fintype.card ι := by
    have hc := Fintype.card_subtype_compl (fun x : F => x ∈ Set.range dom)
    have hrange : Fintype.card {x : F // x ∈ Set.range dom} = Fintype.card ι := by
      rw [Fintype.card_of_bijective (Equiv.ofInjective dom dom.injective).bijective]
    rw [hrange] at hc
    exact hc
  set agreeOod : Finset OodPt :=
    Finset.univ.filter (fun z : OodPt => oodEval dom d w₁ z.1 = oodEval dom d w₂ z.1)
  set oodAmbient : Finset F :=
    Finset.univ.filter (fun z : F => z ∉ Set.range dom ∧ oodEval dom d w₁ z = oodEval dom d w₂ z)
  have hagreeLe : agreeOod.card ≤ d - 1 := by
    have hsub : agreeOod.map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ oodAmbient := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      have ha' := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2, ha'⟩
    calc agreeOod.card = (agreeOod.map ⟨Subtype.val, Subtype.val_injective⟩).card :=
          (Finset.card_map _).symm
      _ ≤ oodAmbient.card := Finset.card_le_card hsub
      _ ≤ d - 1 := card_oodAgree_codeword_le dom hw₁ hw₂ hne
  have hprodCard :
      (Finset.univ.filter fun z : Fin u → OodPt =>
        ∀ s : Fin u, oodEval dom d w₁ (z s).1 = oodEval dom d w₂ (z s).1).card =
      agreeOod.card ^ u := by
    have heq : (Finset.univ.filter fun z : Fin u → OodPt =>
        ∀ s : Fin u, oodEval dom d w₁ (z s).1 = oodEval dom d w₂ (z s).1) =
        Fintype.piFinset (fun _ : Fin u => agreeOod) := by
      ext z
      simp [Fintype.mem_piFinset, agreeOod]
    rw [heq, Fintype.card_piFinset_const]
  rw [prob_eq_card_filter_div, hprodCard, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← div_pow, hOodCard]
  refine pow_le_pow_left₀ (by positivity) ?_ u
  have hdenPos : (0 : ℝ) < ((Fintype.card F - Fintype.card ι : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hproper
  exact div_le_div_of_nonneg_right (by exact_mod_cast hagreeLe) (le_of_lt hdenPos)

/-- **`L`-List Multi-Sample Out-of-Domain Collision Bound (`whir_ood_list_multiSample_prob_le`,
`WHIR` Lemma 4.25):**
for any `L`-list `ws : Fin L → ι → F` of codewords in `reedSolomonCode dom d`, `u` independent OOD
samples fail to separate some distinct pair `ws i ≠ ws j` (`i < j`) with `BindingGame.prob` at most
`(L.choose 2) · ((d - 1) / (|F| - |ι|)) ^ u`. -/
theorem whir_ood_list_multiSample_prob_le
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (dom : ι ↪ F) (hproper : Fintype.card ι < Fintype.card F)
    {d L : ℕ} {ws : Fin L → ι → F}
    (hws : ∀ i : Fin L, ws i ∈ reedSolomonCode dom d) (u : ℕ) :
    prob (fun z : Fin u → {x : F // x ∉ Set.range dom} =>
      ∃ i j : Fin L, i < j ∧ ws i ≠ ws j ∧
        ∀ s : Fin u, oodEval dom d (ws i) (z s).1 = oodEval dom d (ws j) (z s).1) ≤
      (L.choose 2 : ℝ) *
        (((d - 1 : ℕ) : ℝ) / ((Fintype.card F - Fintype.card ι : ℕ) : ℝ)) ^ u := by
  classical
  let LtPair := {p : Fin L × Fin L // p.1 < p.2}
  have hcardPair : Fintype.card LtPair = L.choose 2 := by
    rw [Fintype.card_subtype, card_filter_lt_pairs]
  let ePair : Fin (L.choose 2) ≃ LtPair := (Fintype.equivFinOfCardEq hcardPair).symm
  let B : ℝ := (((d - 1 : ℕ) : ℝ) / ((Fintype.card F - Fintype.card ι : ℕ) : ℝ)) ^ u
  have hBnonneg : 0 ≤ B := by positivity
  let pairBad : Fin (L.choose 2) → (Fin u → {x : F // x ∉ Set.range dom}) → Prop :=
    fun k z => ws (ePair k).1.1 ≠ ws (ePair k).1.2 ∧
      ∀ s : Fin u, oodEval dom d (ws (ePair k).1.1) (z s).1 =
                   oodEval dom d (ws (ePair k).1.2) (z s).1
  have hcover : ∀ z : Fin u → {x : F // x ∉ Set.range dom},
      (∃ i j : Fin L, i < j ∧ ws i ≠ ws j ∧
        ∀ s : Fin u, oodEval dom d (ws i) (z s).1 = oodEval dom d (ws j) (z s).1) →
      ∃ k : Fin (L.choose 2), pairBad k z := by
    rintro z ⟨i, j, hij, hne, hall⟩
    let pt : LtPair := ⟨(i, j), hij⟩
    refine ⟨ePair.symm pt, ?_⟩
    simpa [pairBad, pt] using And.intro hne hall
  calc
    prob (fun z => ∃ i j : Fin L, i < j ∧ ws i ≠ ws j ∧
        ∀ s : Fin u, oodEval dom d (ws i) (z s).1 = oodEval dom d (ws j) (z s).1)
        ≤ prob (fun z => ∃ k : Fin (L.choose 2), pairBad k z) := prob_mono hcover
    _ ≤ ∑ k : Fin (L.choose 2), prob (pairBad k) := prob_exists_fin_le _
    _ ≤ ∑ _k : Fin (L.choose 2), B := by
          refine Finset.sum_le_sum fun k _ => ?_
          by_cases hne : ws (ePair k).1.1 = ws (ePair k).1.2
          · have hfalse : pairBad k = fun _ => False := by
              funext z; exact propext ⟨fun h => h.1 hne, False.elim⟩
            rw [hfalse, prob_false_eq_zero]
            exact hBnonneg
          · refine le_trans (prob_mono fun _ hz => hz.2) ?_
            exact whir_ood_multiSample_prob_le dom hproper (hws _) (hws _) hne u
    _ = (L.choose 2 : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Prefix-coupled `L`-list multi-sample OOD collision bound on any joint sample space
`Ω ≃ Ω_prefix × (Fin u → {x : F // x ∉ Set.range dom})`, directly discharging `hOod` in
`whir_multiRound_soundness_le`. -/
theorem whir_ood_list_multiSample_prob_le_prod
    {Ω Ω_prefix F ι : Type} [Fintype Ω] [Fintype Ω_prefix] [Nonempty Ω_prefix]
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (dom : ι ↪ F) (hproper : Fintype.card ι < Fintype.card F)
    {d L u : ℕ}
    (split : Ω ≃ Ω_prefix × (Fin u → {x : F // x ∉ Set.range dom}))
    (ws : Ω_prefix → Fin L → ι → F)
    (hws : ∀ (p : Ω_prefix) (i : Fin L), ws p i ∈ reedSolomonCode dom d) :
    prob (fun ω : Ω =>
      let p := (split ω).1
      let z := (split ω).2
      ∃ i j : Fin L, i < j ∧ ws p i ≠ ws p j ∧
        ∀ s : Fin u, oodEval dom d (ws p i) (z s).1 = oodEval dom d (ws p j) (z s).1) ≤
      (L.choose 2 : ℝ) *
        (((d - 1 : ℕ) : ℝ) / ((Fintype.card F - Fintype.card ι : ℕ) : ℝ)) ^ u := by
  rw [← prob_equiv split.symm]
  have hsimp : (fun x : Ω_prefix × (Fin u → {x : F // x ∉ Set.range dom}) =>
      let p := (split (split.symm x)).1
      let z := (split (split.symm x)).2
      ∃ i j : Fin L, i < j ∧ ws p i ≠ ws p j ∧
        ∀ s : Fin u, oodEval dom d (ws p i) (z s).1 = oodEval dom d (ws p j) (z s).1) =
    (fun x : Ω_prefix × (Fin u → {x : F // x ∉ Set.range dom}) =>
      ∃ i j : Fin L, i < j ∧ ws x.1 i ≠ ws x.1 j ∧
        ∀ s : Fin u, oodEval dom d (ws x.1 i) (x.2 s).1 = oodEval dom d (ws x.1 j) (x.2 s).1) := by
    funext x; simp
  rw [hsimp]
  apply prob_prod_le
  intro p
  exact whir_ood_list_multiSample_prob_le dom hproper (hws p) u

/-! ## §5. Proof-Size / Verifier-Complexity Scaling (`whir_opened_elements_eq`) -/

/-- Number of oracle/table field elements opened by an `M`-round `WHIR` schedule on an `m`-variable
multilinear witness: `∑_{i < M} t_i · 2^{k_i}` fiber elements plus `2^{m - ∑_{i < M} k_i}` final
table elements. -/
def whirOpenedElements (m : ℕ) {M : ℕ} (sched : WhirSchedule M) : ℕ :=
  (∑ i : Fin M, (sched i).queryCount * 2 ^ (sched i).varsFolded) +
    2 ^ (m - whirTotalVarsFolded sched)

/-- Constant-parameter `M`-round `WHIR` schedule (`varsFolded = k`, `queryCount = t`). -/
def uniformWhirSchedule (M k domainSz t u : ℕ) (δ ef eo : ℝ) : WhirSchedule M :=
  fun _ => ⟨k, domainSz, t, u, δ, ef, eo⟩

/-- **Opened-Element Scaling Formula (`whir_opened_elements_eq`):**
for an `M`-round uniform-$2^k$-ary `WHIR` schedule (`M * k ≤ m`), the verifier reads exactly
`M * (t * 2 ^ k) + 2 ^ (m - M * k)` field elements (`O(M · t · 2^k + 2^{m - M k})`). -/
theorem whir_opened_elements_eq (m M k domainSz t u : ℕ) (δ ef eo : ℝ) :
    whirOpenedElements m (uniformWhirSchedule M k domainSz t u δ ef eo) =
      M * (t * 2 ^ k) + 2 ^ (m - M * k) := by
  simp [whirOpenedElements, whirTotalVarsFolded, uniformWhirSchedule]

/-- Number of field elements transmitted in 1-step Ligero on an `m`-variable (`2^m`) witness:
one folded row of length `2^{m / 2}` plus `colQueries` columns of height `2^{m - m / 2}`. -/
def ligeroOpenedElements (m colQueries : ℕ) : ℕ :=
  2 ^ (m / 2) + colQueries * 2 ^ (m - m / 2)

/-- Lower-bound row length `2^{m / 2}` of 1-step Ligero even at `0` column openings. -/
def ligeroRowSize (m : ℕ) : ℕ := 2 ^ (m / 2)

theorem ligeroRowSize_le_ligeroOpenedElements (m colQueries : ℕ) :
    ligeroRowSize m ≤ ligeroOpenedElements m colQueries :=
  Nat.le_add_right _ _

/-- **Concrete zkML Scale Comparison (`m = 20` and `m = 24`):**
- At `m = 20` (`2^{20}` cells): 4-round 16-ary `WHIR` (`k = 4, t = 22`) opens `1,424` elements vs
  1-step Ligero (`q_col = 64`)'s `66,560` elements (`> 46×` smaller!).
- At `m = 24` (`2^{24}` cells): 5-round 16-ary `WHIR` (`k = 4, t = 22`) opens `1,776` elements vs
  1-step Ligero (`q_col = 64`)'s `266,240` elements (`> 149×` smaller!). -/
theorem whir_beats_ligero_zkml_scales :
    whirOpenedElements 20 (uniformWhirSchedule 4 4 (2 ^ 22) 22 2 (1 / 2) 0 0) = 1424 ∧
    ligeroOpenedElements 20 64 = 66560 ∧
    whirOpenedElements 24 (uniformWhirSchedule 5 4 (2 ^ 26) 22 2 (1 / 2) 0 0) = 1776 ∧
    ligeroOpenedElements 24 64 = 266240 := by
  norm_num [whir_opened_elements_eq, ligeroOpenedElements]

/-- **Parametric Exponential-vs-Linear Separation (`whir_fullFold_lt_ligeroRowSize`):**
for every half-dimension `r ≥ 10` (`m = 2 r ≥ 20`) and arbitrary domain size `domainSz`, `r` rounds
of 4-ary `WHIR` (`k = 2, t = 16`, opening `64 r + 1` elements) opens strictly fewer field elements
than 1-step Ligero's *single row* `2^r` (before even counting Ligero's column openings!). -/
theorem whir_fullFold_lt_ligeroRowSize {r domainSz : ℕ} (hr : 10 ≤ r) :
    whirOpenedElements (2 * r) (uniformWhirSchedule r 2 domainSz 16 1 (1 / 2) 0 0) <
      ligeroRowSize (2 * r) := by
  rw [whir_opened_elements_eq, ligeroRowSize]
  have hsub : 2 * r - r * 2 = 0 := by omega
  have hdiv : 2 * r / 2 = r := by omega
  rw [hsub, hdiv]
  have hind : ∀ n : ℕ, 10 ≤ n → n * 64 + 1 < 2 ^ n := by
    intro n hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction d with
    | zero => norm_num
    | succ k ih =>
        have hk10 : 10 ≤ 10 + k := Nat.le_add_right 10 k
        have ihk := ih hk10
        have hpow10 : 64 < 2 ^ (10 + k) := by
          calc 64 < 2 ^ 10 := by norm_num
            _ ≤ 2 ^ (10 + k) := Nat.pow_le_pow_right (by norm_num) hk10
        have hstep : (10 + (k + 1)) * 64 + 1 = ((10 + k) * 64 + 1) + 64 := by ring
        have hpow2 : 2 ^ (10 + (k + 1)) = 2 ^ (10 + k) + 2 ^ (10 + k) := by
          rw [show 10 + (k + 1) = (10 + k) + 1 by omega, pow_succ, mul_two]
        omega
  simpa using hind r hr

/-- Cumulative folded variable count `∑_{j < n} k_j` after `n` rounds (`folded_height_after` in
`VERDICTS.md` §2 `max_log_arity` audit). -/
def whirCumulativeVarsFolded {M : ℕ} (sched : WhirSchedule M) (n : ℕ) : ℕ :=
  ((List.ofFn fun i : Fin M => (sched i).varsFolded).take n).sum

theorem whirCumulativeVarsFolded_succ {M : ℕ} (sched : WhirSchedule M) (i : Fin M) :
    whirCumulativeVarsFolded sched ((i : ℕ) + 1) =
      whirCumulativeVarsFolded sched (i : ℕ) + (sched i).varsFolded := by
  unfold whirCumulativeVarsFolded
  have hlen : (i : ℕ) < (List.ofFn fun j : Fin M => (sched j).varsFolded).length := by
    simp [i.isLt]
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp

/-- Well-formed rounds (`1 ≤ varsFolded`) strictly advance cumulative folded bits at every step,
preventing phase-routing height collisions. -/
theorem whirCumulativeVarsFolded_strictMono_step {M : ℕ} (sched : WhirSchedule M)
    (i : Fin M) (hwf : (sched i).WellFormed) :
    whirCumulativeVarsFolded sched (i : ℕ) < whirCumulativeVarsFolded sched ((i : ℕ) + 1) := by
  rw [whirCumulativeVarsFolded_succ]
  exact Nat.lt_add_of_pos_right hwf.1

/-- **Zero-Arity Height-Collision Tooth (`whir_zero_arity_stalls_cumulativeVars`,
`VERDICTS.md` §2 `log_arity = 0` pin):**
if an unpinned verifier accepts `varsFolded = 0` (`2^0 = 1`-ary fold), cumulative folded bits fail
to advance (`cum (i + 1) = cum i`), repeating `folded_height_after` across distinct phases, and an
all-zero-arity schedule makes zero folding progress (`whirOpenedElements = M * t + 2^m ≥ 2^m`). -/
theorem whir_zero_arity_stalls_cumulativeVars {M : ℕ} (sched : WhirSchedule M)
    (i : Fin M) (hz : (sched i).varsFolded = 0) :
    whirCumulativeVarsFolded sched ((i : ℕ) + 1) = whirCumulativeVarsFolded sched (i : ℕ) := by
  rw [whirCumulativeVarsFolded_succ, hz, add_zero]

theorem whir_zero_arity_no_progress (m M domainSz t u : ℕ) (δ ef eo : ℝ) :
    whirOpenedElements m (uniformWhirSchedule M 0 domainSz t u δ ef eo) = M * t + 2 ^ m ∧
    2 ^ m ≤ whirOpenedElements m (uniformWhirSchedule M 0 domainSz t u δ ef eo) := by
  rw [whir_opened_elements_eq]
  simp

/-! ## §6. Zero-Shortcut Reed–Solomon Premise Inhabitation & Unpinned Query-Count Teeth -/

/-- Exact ideal `BindingCommitment` retaining the committed word (non-compressing ideal oracle
layer, matching `Selvage.Commitment`'s scope). -/
def exactWordCommitment (F ι : Type*) : BindingCommitment (ι → F) F ι Unit where
  commit w := w
  openAt _ _ := ()
  verifyOpen rt i v _ := rt i = v
  verifyOpen_commit _ _ := rfl
  binding _ _ _ _ _ _ h1 h2 := h1.symm.trans h2

section PremiseInhabitationAndTeeth

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Concrete 2-round `WHIR` schedule (`M = 2`):
- Round `0`: `k₀ = 2` (`4`-ary fold), `N₀ = 16`, `t₀ = 4` fiber queries, `u₀ = 1`, `δ₀ = 1/2`,
- Round `1`: `k₁ = 1` (`2`-ary fold), `N₁ = 4`,  `t₁ = 4` fiber queries, `u₁ = 1`, `δ₁ = 1/2`,
achieving strictly sub-unit soundness budget `(1/2)^4 + (1/2)^4 = 1/8 < 1`. -/
noncomputable def concreteTwoRoundSched : WhirSchedule 2 :=
  ![⟨2, 16, 4, 1, 1 / 2, 0, 0⟩, ⟨1, 4, 4, 1, 1 / 2, 0, 0⟩]

theorem concreteTwoRoundSched_wellFormed :
    ∀ i : Fin 2, (concreteTwoRoundSched i).WellFormed := by
  intro i
  fin_cases i <;>
    simp [concreteTwoRoundSched, WhirRoundSpec.WellFormed] <;> norm_num

theorem concreteTwoRoundSched_totalError :
    whirTotalError concreteTwoRoundSched = 1 / 8 := by
  simp [whirTotalError, concreteTwoRoundSched, WhirRoundSpec.roundError, Fin.sum_univ_two]
  norm_num

/-- Sample space of query schedules for the concrete 2-round `WHIR` instance:
4 fiber queries into `Fin 4` in round 0, and 4 fiber queries into `Fin 2` in round 1. -/
abbrev ConcreteWhirOmega := (Fin 4 → Fin 4) × (Fin 4 → Fin 2)

/-- Concrete injective Reed–Solomon evaluation domains over `ZMod 17` at levels `0, 1, 2`. -/
def domRS0 : (Fin 4 × Fin 4) ↪ ZMod 17 :=
  ⟨fun p => ((4 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ZMod 17), by decide⟩

def domRS1 : (Fin 2 × Fin 2) ↪ ZMod 17 :=
  ⟨fun p => ((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ZMod 17), by decide⟩

def domRS2 : Fin 2 ↪ ZMod 17 :=
  ⟨fun b => ((b : ℕ) : ZMod 17), by decide⟩

/-- Concrete words across the 2-round `ZMod 17` RS descent:
- `rsWord0(b, c) = b` on `Fin 4 × Fin 4` (`3/4 > 1/2`-far from `RS[ZMod 17, domRS0, 2]`),
- `rsWord1(b, c) = 4 · (2 b + c)` on `Fin 2 × Fin 2` (exact 4-ary sum-fold of `rsWord0`,
  still `3/4 > 1/2`-far from `RS[ZMod 17, domRS1, 1]`, exercising `StepSound`'s inductive
  propagation branch `Or.inr (¬ CloseAt 1)` in round 0!),
- `rsWord2(b) = 4` on `Fin 2` (genuine codeword in `RS[ZMod 17, domRS2, 1]`, at exact distance
  `1/2` from `rsWord1`'s 2-ary fold `[4, 3]`, exercising `QueryMiss 1` in round 1!). -/
def rsWord0 : Fin 4 × Fin 4 → ZMod 17 := fun p => ((p.1 : ℕ) : ZMod 17)

def rsWord1 : Fin 2 × Fin 2 → ZMod 17 :=
  fun p => (4 : ZMod 17) * ((2 * (p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ZMod 17)

def rsWord2 : Fin 2 → ZMod 17 := fun _ => 4

def rsShift0 : Fin 4 → Fin 2 × Fin 2 :=
  fun b => (⟨(b : ℕ) / 2, by have := b.isLt; omega⟩, ⟨(b : ℕ) % 2, Nat.mod_lt _ (by decide)⟩)

def concreteSumFold4 (vals : Fin 4 → ZMod 17) : ZMod 17 :=
  ∑ c : Fin 4, vals c

def concreteSumFold2 (vals : Fin 2 → ZMod 17) : ZMod 17 :=
  vals 0 + vals 1

private theorem eval_eq_affine_of_degree_lt_two {F : Type*} [Semiring F] {p : Polynomial F}
    (hp : p.degree < (2 : WithBot ℕ)) (z : F) :
    p.eval z = p.coeff 0 + p.coeff 1 * z := by
  have hn : p.natDegree < 2 := by
    by_cases hp0 : p = 0
    · subst hp0; simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [Polynomial.eval_eq_sum_range' hn, Finset.sum_range_succ, Finset.sum_range_one]
  simp

private theorem eval_eq_const_of_degree_lt_one {F : Type*} [Semiring F] {p : Polynomial F}
    (hp : p.degree < (1 : WithBot ℕ)) (z : F) :
    p.eval z = p.coeff 0 := by
  have hn : p.natDegree < 1 := by
    by_cases hp0 : p = 0
    · subst hp0; simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [Polynomial.eval_eq_sum_range' hn, Finset.sum_range_one]
  simp

private theorem rsWord0_hamming_ge_twelve :
    ∀ a₀ a₁ : ZMod 17, 12 ≤ hammingDist rsWord0 (fun x => a₀ + a₁ * domRS0 x) := by
  decide

private theorem rsWord1_hamming_ge_three :
    ∀ a₀ : ZMod 17, 3 ≤ hammingDist rsWord1 (fun _ => a₀) := by
  decide

/-- `rsWord0` is genuinely `(1/2)`-far from `reedSolomonCode domRS0 2` (`relDist ≥ 12/16 = 3/4`). -/
theorem not_close_rsWord0 : ¬ close (1 / 2) (reedSolomonCode domRS0 2) rsWord0 := by
  rintro ⟨u, hu, hdist⟩
  obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
  have hu_eq : u = fun x => p.coeff 0 + p.coeff 1 * domRS0 x :=
    funext fun x => (hpu x).trans (eval_eq_affine_of_degree_lt_two hp (domRS0 x))
  rw [hu_eq, relDist] at hdist
  have hcard : Fintype.card (Fin 4 × Fin 4) = 16 := by decide
  have hham : (12 : ℝ) ≤
      (hammingDist rsWord0 (fun x => p.coeff 0 + p.coeff 1 * domRS0 x) : ℝ) := by
    exact_mod_cast rsWord0_hamming_ge_twelve (p.coeff 0) (p.coeff 1)
  rw [hcard] at hdist
  push_cast at hdist
  linarith

/-- `rsWord1` is genuinely `(1/2)`-far from `reedSolomonCode domRS1 1` (`relDist ≥ 3/4`). -/
theorem not_close_rsWord1 : ¬ close (1 / 2) (reedSolomonCode domRS1 1) rsWord1 := by
  rintro ⟨u, hu, hdist⟩
  obtain ⟨p, hp, hpu⟩ := mem_reedSolomonCode_iff.mp hu
  have hu_eq : u = fun _ => p.coeff 0 :=
    funext fun x => (hpu x).trans (eval_eq_const_of_degree_lt_one hp (domRS1 x))
  rw [hu_eq, relDist] at hdist
  have hcard : Fintype.card (Fin 2 × Fin 2) = 4 := by decide
  have hham : (3 : ℝ) ≤ (hammingDist rsWord1 (fun _ => p.coeff 0) : ℝ) := by
    exact_mod_cast rsWord1_hamming_ge_three (p.coeff 0)
  rw [hcard] at hdist
  push_cast at hdist
  linarith

/-- `rsWord2` is a genuine codeword of `reedSolomonCode domRS2 1`. -/
theorem rsWord2_mem_reedSolomon : rsWord2 ∈ reedSolomonCode domRS2 1 :=
  mem_reedSolomonCode_iff.mpr ⟨Polynomial.C 4,
    lt_of_le_of_lt Polynomial.degree_C_le (WithBot.coe_lt_coe.mpr Nat.one_pos),
    fun _ => by simp [rsWord2]⟩

theorem rsWord1_fold_relDist_rsWord2 :
    (1 / 2 : ℝ) ≤ relDist (fun b : Fin 2 => concreteSumFold2 (fun c => rsWord1 (b, c))) rsWord2 := by
  have hham : hammingDist
      (fun b : Fin 2 => concreteSumFold2 (fun c => rsWord1 (b, c))) rsWord2 = 1 := by
    decide
  rw [relDist, hham, Fintype.card_fin]
  norm_num

/-- Concrete zero-shortcut 2-round `WhirExecution` whose `CloseAt` and `FinalCheck` predicates are
**genuine `Selvage.close` / `reedSolomonCode` predicates** over `ZMod 17`:
- Round `0` propagates `¬ CloseAt 0 → ¬ CloseAt 1` (`Or.inr`),
- Round `1` catches `rsWord1`'s 2-ary fold `[4, 3]` vs `rsWord2 = [4, 4]` via `QueryMiss 1`,
- `FinalCheck` checks `rsWord2 ∈ reedSolomonCode domRS2 1`! -/
def concreteTwoRoundExec : WhirExecution ConcreteWhirOmega 2 where
  CloseAt n _ :=
    match n with
    | ⟨0, _⟩ => close (1 / 2) (reedSolomonCode domRS0 2) rsWord0
    | ⟨1, _⟩ => close (1 / 2) (reedSolomonCode domRS1 1) rsWord1
    | ⟨2, _⟩ => close (1 / 2) (reedSolomonCode domRS2 1) rsWord2
  RoundAccepts i ω :=
    match i with
    | ⟨0, _⟩ =>
        ∃ op : Fin 4 → WhirFiberOpening (ZMod 17) Unit Unit 2,
          ∀ a : Fin 4,
            OpenedWhirFiberQuery
              (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
              (exactWordCommitment (ZMod 17) (Fin 2 × Fin 2)).toOpeningScheme
              concreteSumFold4 rsShift0 rsWord0 rsWord1 (ω.1 a) (op a)
    | ⟨1, _⟩ =>
        ∃ op : Fin 4 → WhirFiberOpening (ZMod 17) Unit Unit 1,
          ∀ a : Fin 4,
            OpenedWhirFiberQuery
              (exactWordCommitment (ZMod 17) (Fin 2 × Fin 2)).toOpeningScheme
              (exactWordCommitment (ZMod 17) (Fin 2)).toOpeningScheme
              concreteSumFold2 id rsWord1 rsWord2 (ω.2 a) (op a)
  FinalCheck _ := rsWord2 ∈ reedSolomonCode domRS2 1
  FoldBad _ _ := False
  OodBad _ _ := False
  QueryMiss i ω :=
    match i with
    | ⟨0, _⟩ => False
    | ⟨1, _⟩ =>
        (1 / 2 : ℝ) ≤ relDist (fun b : Fin 2 => concreteSumFold2 (fun c => rsWord1 (b, c)))
                              rsWord2 ∧
        ∃ op : Fin 4 → WhirFiberOpening (ZMod 17) Unit Unit 1,
          ∀ a : Fin 4,
            OpenedWhirFiberQuery
              (exactWordCommitment (ZMod 17) (Fin 2 × Fin 2)).toOpeningScheme
              (exactWordCommitment (ZMod 17) (Fin 2)).toOpeningScheme
              concreteSumFold2 id rsWord1 rsWord2 (ω.2 a) (op a)

/-- **Zero-Shortcut Reed–Solomon Premise Inhabitation (`whir_concrete_twoRound_inhabited`):**
every hypothesis of `whir_multiRound_soundness_le` holds simultaneously on genuine `reedSolomonCode`
proximity predicates, exercising both inductive farness propagation (round `0`) and authenticated
fiber-query escape (round `1`) with `prob (...) ≤ 1 / 8 < 1`. -/
theorem whir_concrete_twoRound_inhabited :
    (∀ i : Fin 2, (concreteTwoRoundSched i).WellFormed) ∧
    concreteTwoRoundExec.StepSound ∧
    concreteTwoRoundExec.TerminalSound ∧
    (∃ ω : ConcreteWhirOmega, ¬ concreteTwoRoundExec.CloseAt 0 ω) ∧
    prob (fun ω : ConcreteWhirOmega =>
      ¬ concreteTwoRoundExec.CloseAt 0 ω ∧ concreteTwoRoundExec.VerifierAccepts ω) ≤ 1 / 8 := by
  have hstep : concreteTwoRoundExec.StepSound := by
    intro i ω _hfar hacc
    fin_cases i
    · exact Or.inr not_close_rsWord1
    · exact Or.inl (Or.inr (Or.inr ⟨rsWord1_fold_relDist_rsWord2, hacc⟩))
  have hterm : concreteTwoRoundExec.TerminalSound := by
    intro _ hmem
    refine ⟨rsWord2, hmem, ?_⟩
    simp [relDist]
  have hFold : ∀ i : Fin 2, prob (concreteTwoRoundExec.FoldBad i) ≤ (concreteTwoRoundSched i).epsFold := by
    intro i; fin_cases i <;> simp [concreteTwoRoundExec, concreteTwoRoundSched, prob_false_eq_zero]
  have hOod : ∀ i : Fin 2, prob (concreteTwoRoundExec.OodBad i) ≤ (concreteTwoRoundSched i).epsOod := by
    intro i; fin_cases i <;> simp [concreteTwoRoundExec, concreteTwoRoundSched, prob_false_eq_zero]
  have hQuery : ∀ i : Fin 2, prob (concreteTwoRoundExec.QueryMiss i) ≤
      (1 - (concreteTwoRoundSched i).delta) ^ (concreteTwoRoundSched i).queryCount := by
    intro i
    fin_cases i
    · simp only [concreteTwoRoundExec, concreteTwoRoundSched, prob_false_eq_zero]
      norm_num
    · -- Round 1 discharged directly via `whir_fiberQuery_miss_prob_le`!
      let split1 : ConcreteWhirOmega ≃ (Fin 4 → Fin 4) × (Fin 4 → Fin 2) := Equiv.refl _
      have hmiss := whir_fiberQuery_miss_prob_le
        (Ω := ConcreteWhirOmega) (Ω_prefix := Fin 4 → Fin 4)
        (F := ZMod 17) (β := Fin 2) (ιNext := Fin 2)
        (k := 1) (t := 4) (δ := 1 / 2) (by norm_num)
        split1
        (exactWordCommitment (ZMod 17) (Fin 2 × Fin 2))
        (exactWordCommitment (ZMod 17) (Fin 2))
        (fun _ => concreteSumFold2)
        (fun _ => id)
        (fun _ => rsWord1)
        (fun _ => rsWord2)
      simpa [concreteTwoRoundExec, concreteTwoRoundSched, split1, exactWordCommitment] using hmiss
  refine ⟨concreteTwoRoundSched_wellFormed, hstep, hterm, ⟨default, not_close_rsWord0⟩, ?_⟩
  have hmain := whir_multiRound_soundness_sum_le concreteTwoRoundSched concreteTwoRoundExec
    hstep hterm hFold hOod hQuery
  rwa [concreteTwoRoundSched_totalError] at hmain

/-! ### Unpinned Query-Count / Zero-Shift Falsifier Teeth (`VERDICTS.md` §2 `num_queries` pin) -/

/-- **Zero-Shift Algebraic Tooth (`whir_zero_queries_term_eq_one`):**
whenever round `i` sets `queryCount = 0` (`t_i = 0`), the query-miss term `(1 - δ_i)^0` equals `1`
regardless of how large the proximity distance `δ_i` is! -/
theorem whir_zero_queries_term_eq_one (s : WhirRoundSpec) (ht : s.queryCount = 0) :
    (1 - s.delta) ^ s.queryCount = 1 := by
  rw [ht, pow_zero]

/-- If *any* round `i₀ : Fin M` in a well-formed schedule has `queryCount = 0`, the schedule's
total soundness bound `whirTotalError sched` is at least `1` (completely vacuous!). -/
theorem whir_zero_queries_vacuous_bound {M : ℕ} (sched : WhirSchedule M)
    (hwf : ∀ i : Fin M, (sched i).WellFormed)
    (i₀ : Fin M) (ht0 : (sched i₀).queryCount = 0) :
    1 ≤ whirTotalError sched := by
  have hi0 : 1 ≤ (sched i₀).roundError := by
    rcases hwf i₀ with ⟨_, _, _, _, hef, heo⟩
    unfold WhirRoundSpec.roundError
    rw [whir_zero_queries_term_eq_one (sched i₀) ht0]
    linarith
  have hle : (sched i₀).roundError ≤ ∑ i : Fin M, (sched i).roundError :=
    Finset.single_le_sum (fun i _ => WhirRoundSpec.roundError_nonneg (hwf i)) (Finset.mem_univ i₀)
  exact le_trans hi0 hle

/-- **Constructive Zero-Query Forgery (`whir_zero_queries_forgery_prob_one`):**
grounded in genuine `reedSolomonCode` closeness: when `t₀ = 0` (`Fin 0 → Fin 4`), a cheating prover
starting from the `(1/2)`-far word `rsWord0` switches to `0 ∈ reedSolomonCode domRS1 1` at round `1`
and passes *every* check (including `FinalCheck : 0 ∈ reedSolomonCode domRS1 1`) with
**`BindingGame.prob = 1`**! -/
def zeroQueryForgeryExec : WhirExecution (Fin 0 → Fin 4) 1 where
  CloseAt n _ :=
    match n with
    | ⟨0, _⟩ => close (1 / 2) (reedSolomonCode domRS0 2) rsWord0
    | ⟨1, _⟩ => close (1 / 2) (reedSolomonCode domRS1 1) 0
  RoundAccepts _ ω :=
    ∃ op : Fin 0 → WhirFiberOpening (ZMod 17) Unit Unit 2,
      ∀ a : Fin 0,
        OpenedWhirFiberQuery
          (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
          (exactWordCommitment (ZMod 17) (Fin 2 × Fin 2)).toOpeningScheme
          concreteSumFold4 rsShift0 rsWord0 0 (ω a) (op a)
  FinalCheck _ := (0 : Fin 2 × Fin 2 → ZMod 17) ∈ reedSolomonCode domRS1 1
  FoldBad _ _ := False
  OodBad _ _ := False
  QueryMiss _ _ := True

theorem whir_zero_queries_forgery_prob_one :
    zeroQueryForgeryExec.StepSound ∧
    zeroQueryForgeryExec.TerminalSound ∧
    prob (fun ω : Fin 0 → Fin 4 =>
      ¬ zeroQueryForgeryExec.CloseAt 0 ω ∧ zeroQueryForgeryExec.VerifierAccepts ω) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _ _ _
    fin_cases i
    exact Or.inl (Or.inr (Or.inr trivial))
  · intro _ hmem
    exact ⟨0, hmem, by simp [relDist]⟩
  · have hall : (fun ω : Fin 0 → Fin 4 =>
        ¬ zeroQueryForgeryExec.CloseAt 0 ω ∧ zeroQueryForgeryExec.VerifierAccepts ω) =
        (fun _ => True) := by
      funext ω
      simp only [zeroQueryForgeryExec, WhirExecution.VerifierAccepts, eq_iff_iff, iff_true]
      refine ⟨not_close_rsWord0, fun i => ?_, Submodule.zero_mem _⟩
      fin_cases i
      exact ⟨fun a => a.elim0, fun a => a.elim0⟩
    rw [hall]
    exact prob_true

/-- Concrete initial word on `Fin 4 × Fin 4` (`16` points over `ZMod 17`) with `2` nonzero fibers
and `2` zero fibers, exhibiting exact `(1 - δ₀)^1 = 1/2` 1-query acceptance probability. -/
def concreteHalfZeroWord0 : Fin 4 × Fin 4 → ZMod 17 :=
  fun p => if (p.1 : ℕ) < 2 then 1 else 0

/-- **Attacker-Chosen 1-Query Downgrade Tooth (`whir_unpinned_one_query_refutes`,
`VERDICTS.md` §2 `num_queries` pin `52e1fab`):**
even if `t ≥ 1` is enforced (`t = 0` rejected), reading `queryCount` from an untrusted proof
without pinning `queryCount = configuredQueries` lets an attacker submit `t = 1` on
`concreteHalfZeroWord0` (`δ₀ = 1/2`), succeeding on fibers `2, 3` with **exact probability `1 / 2`**
and refuting every target soundness budget `ε < 1 / 2`! -/
theorem whir_unpinned_one_query_exact_prob :
    prob (fun q : Fin 1 → Fin 4 =>
      ∃ op : Fin 1 → WhirFiberOpening (ZMod 17) Unit Unit 2,
        ∀ a : Fin 1,
          OpenedWhirFiberQuery
            (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
            (exactWordCommitment (ZMod 17) (Fin 4)).toOpeningScheme
            concreteSumFold4 id concreteHalfZeroWord0 (fun _ => 0) (q a) (op a)) = 1 / 2 := by
  have heq : ∀ q : Fin 1 → Fin 4,
      (∃ op : Fin 1 → WhirFiberOpening (ZMod 17) Unit Unit 2,
        ∀ a : Fin 1,
          OpenedWhirFiberQuery
            (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
            (exactWordCommitment (ZMod 17) (Fin 4)).toOpeningScheme
            concreteSumFold4 id concreteHalfZeroWord0 (fun _ => 0) (q a) (op a)) ↔
      2 ≤ (q 0 : ℕ) := by
    intro q
    constructor
    · rintro ⟨op, hop⟩
      have hpin := openedWhirFiberQuery_pins (k := 2)
        (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4))
        (exactWordCommitment (ZMod 17) (Fin 4))
        concreteSumFold4 id
        (curWord := concreteHalfZeroWord0) (nextWord := fun _ => 0)
        rfl rfl (hop 0)
      change concreteSumFold4 (fun c => concreteHalfZeroWord0 (q 0, c)) = 0 at hpin
      generalize q 0 = q0 at hpin ⊢
      revert hpin
      fin_cases q0 <;> decide
    · intro hge
      refine ⟨fun _ => ⟨fun c => concreteHalfZeroWord0 (q 0, c), fun _ => (), 0, ()⟩, fun a => ?_⟩
      fin_cases a
      refine ⟨fun _ => rfl, rfl, ?_⟩
      change concreteSumFold4 (fun c => concreteHalfZeroWord0 (q 0, c)) = 0
      have hlt : ¬ (q 0 : ℕ) < 2 := by omega
      simp [concreteSumFold4, concreteHalfZeroWord0, hlt]
  have hfn : (fun q : Fin 1 → Fin 4 =>
      ∃ op : Fin 1 → WhirFiberOpening (ZMod 17) Unit Unit 2,
        ∀ a : Fin 1,
          OpenedWhirFiberQuery
            (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
            (exactWordCommitment (ZMod 17) (Fin 4)).toOpeningScheme
            concreteSumFold4 id concreteHalfZeroWord0 (fun _ => 0) (q a) (op a)) =
      (fun q : Fin 1 → Fin 4 => 2 ≤ (q 0 : ℕ)) := by
    funext q; exact propext (heq q)
  rw [hfn]
  let e : (Fin 1 → Fin 4) ≃ Fin 4 := Equiv.funUnique (Fin 1) (Fin 4)
  have hprob := prob_equiv e (fun b : Fin 4 => 2 ≤ (b : ℕ))
  change prob (fun q : Fin 1 → Fin 4 => 2 ≤ (q 0 : ℕ)) = _ at hprob
  rw [hprob, prob_eq_card_filter_div, Fintype.card_fin]
  have hcard : (Finset.univ.filter (fun b : Fin 4 => 2 ≤ (b : ℕ))).card = 2 := by decide
  rw [hcard]
  norm_num

theorem whir_unpinned_one_query_refutes {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ (prob (fun q : Fin 1 → Fin 4 =>
        ∃ op : Fin 1 → WhirFiberOpening (ZMod 17) Unit Unit 2,
          ∀ a : Fin 1,
            OpenedWhirFiberQuery
              (exactWordCommitment (ZMod 17) (Fin 4 × Fin 4)).toOpeningScheme
              (exactWordCommitment (ZMod 17) (Fin 4)).toOpeningScheme
              concreteSumFold4 id concreteHalfZeroWord0 (fun _ => 0) (q a) (op a)) ≤ ε) := by
  rw [whir_unpinned_one_query_exact_prob]
  linarith

end PremiseInhabitationAndTeeth

/-! ## §7. Axiom Audit Pins -/

#assert_axioms whir_multiRound_escape_or_terminal
#assert_axioms whir_multiRound_escape_of_accept
#assert_axioms whir_multiRound_soundness_le
#assert_axioms whir_multiRound_soundness_sum_le
#assert_axioms openedWhirFiberQuery_pins
#assert_axioms whir_fiberQuery_miss_prob_le
#assert_axioms whir_concreteRound_stepSound
#assert_axioms whir_ood_multiSample_prob_le
#assert_axioms whir_ood_list_multiSample_prob_le
#assert_axioms whir_ood_list_multiSample_prob_le_prod
#assert_axioms whir_opened_elements_eq
#assert_axioms whir_beats_ligero_zkml_scales
#assert_axioms whir_fullFold_lt_ligeroRowSize
#assert_axioms whirCumulativeVarsFolded_strictMono_step
#assert_axioms whir_zero_arity_stalls_cumulativeVars
#assert_axioms whir_zero_arity_no_progress
#assert_axioms not_close_rsWord0
#assert_axioms not_close_rsWord1
#assert_axioms whir_concrete_twoRound_inhabited
#assert_axioms whir_zero_queries_term_eq_one
#assert_axioms whir_zero_queries_vacuous_bound
#assert_axioms whir_zero_queries_forgery_prob_one
#assert_axioms whir_unpinned_one_query_exact_prob
#assert_axioms whir_unpinned_one_query_refutes

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_multiRound_escape_or_terminal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms whir_multiRound_escape_or_terminal

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_multiRound_escape_of_accept' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms whir_multiRound_escape_of_accept

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_multiRound_soundness_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_multiRound_soundness_le

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_fiberQuery_miss_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_fiberQuery_miss_prob_le

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_concreteRound_stepSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_concreteRound_stepSound

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_ood_multiSample_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_ood_multiSample_prob_le

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_ood_list_multiSample_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_ood_list_multiSample_prob_le

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_ood_list_multiSample_prob_le_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_ood_list_multiSample_prob_le_prod

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_opened_elements_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_opened_elements_eq

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_beats_ligero_zkml_scales' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_beats_ligero_zkml_scales

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_fullFold_lt_ligeroRowSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_fullFold_lt_ligeroRowSize

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_zero_arity_stalls_cumulativeVars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_zero_arity_stalls_cumulativeVars

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.not_close_rsWord0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_close_rsWord0

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_concrete_twoRound_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_concrete_twoRound_inhabited

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_zero_queries_term_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_zero_queries_term_eq_one

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_zero_queries_vacuous_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_zero_queries_vacuous_bound

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_zero_queries_forgery_prob_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_zero_queries_forgery_prob_one

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_unpinned_one_query_exact_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_unpinned_one_query_exact_prob

/-- info: 'Minidregg.Selvage.WhirMultiRoundSoundness.whir_unpinned_one_query_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whir_unpinned_one_query_refutes

end Minidregg.Selvage.WhirMultiRoundSoundness
