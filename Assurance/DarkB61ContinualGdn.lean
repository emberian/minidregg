/- Stateful custody, coefficient packing and exact unlearning for GDN fast weights. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theory.ZkmlDeltaNet

namespace Minidregg.Assurance.DarkB61ContinualGdn

open Matrix Polynomial
open scoped BigOperators Polynomial
open Minidregg.Theory.ZkmlDeltaNet (IsStrictLowerTri neumannInv
  mul_neumannInv_eq_one neumannInv_mul_eq_one wyChunk_bilinear_iff_recurrence)

set_option autoImplicit false

/-! ## §1. Theorem 1 — Single-Provider Shadow-Branching Impossibility vs. `t`-of-`n` Threshold Custody -/

section CustodyImpossibilityAndThreshold

/-- A `1`-party (`NoSingleViewer = 1`) homomorphic evaluator holding `ct_S = enc S` and `evalHom`. -/
structure SingleProviderFheEval (State Query Ct Out : Type*) where
  enc : State → Ct
  decState : Ct → State
  decOut : Ct → Out
  stepPlain : State → Query → State × Out
  evalHom : Ct → Query → Ct × Ct
  decState_enc : ∀ S, decState (enc S) = S
  eval_state_correct : ∀ ct q, decState (evalHom ct q).1 = (stepPlain (decState ct) q).1
  eval_out_correct : ∀ ct q, decOut (evalHom ct q).2 = (stepPlain (decState ct) q).2

def runPlainTrajectory {State Query Out : Type*} (step : State → Query → State × Out) :
    State → List Query → List Out
  | _, [] => []
  | S, q :: qs => let res := step S q; res.2 :: runPlainTrajectory step res.1 qs

def runHomMainTranscript {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out) : Ct → List Query → List (Ct × Ct)
  | _, [] => []
  | ct, q :: qs => let stepCt := E.evalHom ct q; stepCt :: runHomMainTranscript E stepCt.1 qs

def evalShadowBranch {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out) : Ct → List Query → List Ct
  | _, [] => []
  | ct, q :: qs => let stepCt := E.evalHom ct q; stepCt.2 :: evalShadowBranch E stepCt.1 qs

theorem evalShadowBranch_length {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out) (ct : Ct) (qs : List Query) :
    (evalShadowBranch E ct qs).length = qs.length := by
  induction qs generalizing ct with
  | nil => rfl
  | cons _ _ ih => simp [evalShadowBranch, ih]

theorem evalShadowBranch_decOut_eq_plain {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out) :
    ∀ (ct : Ct) (qs : List Query),
      (evalShadowBranch E ct qs).map E.decOut = runPlainTrajectory E.stepPlain (E.decState ct) qs
  | _, [] => rfl
  | ct, q :: qs => by
      simp only [evalShadowBranch, List.map_cons, runPlainTrajectory, E.eval_out_correct]
      rw [evalShadowBranch_decOut_eq_plain E (E.evalHom ct q).1 qs, E.eval_state_correct]

def shadowBranchServer {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out)
    (ct₀ : Ct) (authQueries shadowQueries : List Query) : List (Ct × Ct) × List Ct :=
  (runHomMainTranscript E ct₀ authQueries, evalShadowBranch E ct₀ shadowQueries)

/-- **Theorem 1a (`single_provider_cannot_prevent_shadow_branching`, `DIRECTIVES-DIG` §2.11):**
Any `1`-party (`NoSingleViewer = 1`) homomorphic evaluator holding `ct_S = E.enc S` and `E.evalHom`
can snapshot `ct_S` and evaluate an arbitrary sequence `shadowQueries` (`x'_1, …, x'_B`) in the head
with **zero** observable deviation on the main transcript (`run.1 = honestMainTranscript`), passing
every complete verifier `verifyMain` while obtaining exact encrypted shadow outputs. -/
theorem single_provider_cannot_prevent_shadow_branching {State Query Ct Out : Type*}
    (E : SingleProviderFheEval State Query Ct Out)
    (verifyMain : Ct → List Query → List (Ct × Ct) → Prop)
    (S : State) (authQueries shadowQueries : List Query)
    (hComplete : verifyMain (E.enc S) authQueries (runHomMainTranscript E (E.enc S) authQueries)) :
    let run := shadowBranchServer E (E.enc S) authQueries shadowQueries
    run.1 = runHomMainTranscript E (E.enc S) authQueries ∧
    verifyMain (E.enc S) authQueries run.1 ∧
    run.2.length = shadowQueries.length ∧
    run.2.map E.decOut = runPlainTrajectory E.stepPlain S shadowQueries := by
  refine ⟨rfl, hComplete, evalShadowBranch_length E (E.enc S) shadowQueries, ?_⟩
  dsimp only [shadowBranchServer]
  rw [evalShadowBranch_decOut_eq_plain, E.decState_enc]

def zmod17ToyFhe : SingleProviderFheEval (ZMod 17) (ZMod 17) (ZMod 17) (ZMod 17) where
  enc s := s + 9
  decState ct := ct - 9
  decOut ct := ct - 9
  stepPlain s q := (2 * s + q, s * q)
  evalHom ct q := (2 * (ct - 9) + q + 9, (ct - 9) * q + 9)
  decState_enc s := by ring
  eval_state_correct ct q := by ring
  eval_out_correct ct q := by ring

theorem single_provider_shadow_witness :
    let authQueries : List (ZMod 17) := [2]
    let shadowQueries : List (ZMod 17) := [3, 5, 7, 11]
    let run := shadowBranchServer zmod17ToyFhe (zmod17ToyFhe.enc 4) authQueries shadowQueries
    authQueries.length = 1 ∧ shadowQueries.length = 4 ∧
    run.1 = runHomMainTranscript zmod17ToyFhe (zmod17ToyFhe.enc 4) authQueries ∧
    run.2.map zmod17ToyFhe.decOut = runPlainTrajectory zmod17ToyFhe.stepPlain 4 shadowQueries := by
  decide

structure CustodyCrossingEvent (n : ℕ) where
  epoch : ℕ
  signers : Finset (Fin n)
  queryDigest : ℕ
  deriving DecidableEq

/-- `t`-of-`n` threshold SPDZ/ddec crossing trace with monotonic honest custodian counters in `[1, B_auth]`. -/
structure ValidThresholdCrossingTrace (n t B_auth : ℕ) (corrupt : Finset (Fin n))
    (events : List (CustodyCrossingEvent n)) : Prop where
  quorum_size : ∀ ev ∈ events, t ≤ ev.signers.card
  honest_budget : ∀ ev ∈ events, ∀ h ∈ ev.signers, h ∉ corrupt → 1 ≤ ev.epoch ∧ ev.epoch ≤ B_auth
  honest_strict_mono :
    ∀ (i j : Fin events.length), i < j →
      ∀ h : Fin n, h ∉ corrupt →
        h ∈ (events.get i).signers → h ∈ (events.get j).signers →
        (events.get i).epoch < (events.get j).epoch

theorem quorum_has_honest_of_lt_threshold {n t : ℕ} {Q corrupt : Finset (Fin n)}
    (hQ : t ≤ Q.card) (hcorr : corrupt.card < t) :
    ∃ h ∈ Q, h ∉ corrupt := by
  by_contra hall; push Not at hall
  have hle : Q.card ≤ corrupt.card := Finset.card_le_card (fun x hx => hall x hx)
  omega

theorem corrupt_coalition_zero_unilateral_crossings {n t B_auth : ℕ} {corrupt : Finset (Fin n)}
    {events : List (CustodyCrossingEvent n)}
    (htrace : ValidThresholdCrossingTrace n t B_auth corrupt events)
    (hcorr : corrupt.card < t)
    (hunilateral : ∀ ev ∈ events, ev.signers ⊆ corrupt) :
    events = [] := by
  cases events with
  | nil => rfl
  | cons ev _ =>
      obtain ⟨h, hhQ, hhH⟩ :=
        quorum_has_honest_of_lt_threshold (htrace.quorum_size ev (List.mem_cons_self ..)) hcorr
      exact False.elim (hhH (hunilateral ev (List.mem_cons_self ..) hhQ))

theorem quorum_inter_has_honest {n t : ℕ} {Q₁ Q₂ corrupt : Finset (Fin n)}
    (hQ₁ : t ≤ Q₁.card) (hQ₂ : t ≤ Q₂.card) (hinter : n + corrupt.card < 2 * t) :
    ∃ h : Fin n, h ∈ Q₁ ∧ h ∈ Q₂ ∧ h ∉ corrupt := by
  have hunion : (Q₁ ∪ Q₂).card ≤ n := by simpa [Fintype.card_fin] using Finset.card_le_univ (Q₁ ∪ Q₂)
  have hsum := Finset.card_union_add_card_inter Q₁ Q₂
  have hcard_inter : corrupt.card < (Q₁ ∩ Q₂).card := by omega
  by_contra hall; push Not at hall
  have hsub : Q₁ ∩ Q₂ ⊆ corrupt := fun h hh =>
    hall h (Finset.mem_inter.mp hh).1 (Finset.mem_inter.mp hh).2
  have hle := Finset.card_le_card hsub; omega

/-- **Theorem 1b (`threshold_custody_prevents_shadow_branching`):**
In `t`-of-`n` threshold SPDZ/ddec custody (`t ≥ 2`) with `n + corrupt.card < 2 * t` (covering
`3`-of-`3` SPDZ with up to `2` corruptions, i.e. ≥ 1 honest custodian, and BFT `t`-of-`n`), honest
monotonic policy-counter checking bounds total evaluations to `events.length ≤ B_auth` (`0` shadow
branches when authorized traffic uses `B_auth`). -/
theorem threshold_custody_prevents_shadow_branching {n t B_auth : ℕ}
    {corrupt : Finset (Fin n)} {events : List (CustodyCrossingEvent n)}
    (ht : 2 ≤ t) (hinter : n + corrupt.card < 2 * t)
    (htrace : ValidThresholdCrossingTrace n t B_auth corrupt events) :
    events.length ≤ B_auth ∧
    ∀ authEvents shadowEvents : List (CustodyCrossingEvent n),
      events = authEvents ++ shadowEvents → B_auth ≤ authEvents.length → shadowEvents = [] := by
  have _ := ht
  have hinj : Function.Injective (fun i : Fin events.length =>
      (⟨(events.get i).epoch - 1, by
        have hmem := List.get_mem events i
        obtain ⟨h, hh1, _, hhH⟩ := quorum_inter_has_honest
          (htrace.quorum_size _ hmem) (htrace.quorum_size _ hmem) hinter
        have hb := htrace.honest_budget _ hmem h hh1 hhH; omega⟩ : Fin B_auth)) := by
    intro i j hij
    have heq : (events.get i).epoch - 1 = (events.get j).epoch - 1 := congrArg Fin.val hij
    have hi_mem := List.get_mem events i; have hj_mem := List.get_mem events j
    obtain ⟨h, hhi, hhj, hhH⟩ :=
      quorum_inter_has_honest (htrace.quorum_size _ hi_mem) (htrace.quorum_size _ hj_mem) hinter
    have hbi := htrace.honest_budget _ hi_mem h hhi hhH
    have hbj := htrace.honest_budget _ hj_mem h hhj hhH
    have hep : (events.get i).epoch = (events.get j).epoch := by omega
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact absurd hep (ne_of_lt (htrace.honest_strict_mono i j hlt h hhH hhi hhj))
    · rfl
    · exact absurd hep.symm (ne_of_lt (htrace.honest_strict_mono j i hgt h hhH hhj hhi))
  have hlen : events.length ≤ B_auth := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  refine ⟨hlen, fun authEvents shadowEvents hsplit hfull => ?_⟩
  have htot : authEvents.length + shadowEvents.length ≤ B_auth := by
    rw [← List.length_append, ← hsplit]; exact hlen
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem threshold_policy_token_prevents_shadow_branching {n t B_auth : ℕ}
    {corrupt : Finset (Fin n)} {events : List (CustodyCrossingEvent n)}
    (hcorr : corrupt.card < t)
    (htrace : ValidThresholdCrossingTrace n t B_auth corrupt events)
    (hpol : ∀ i j : Fin events.length, (events.get i).epoch = (events.get j).epoch → i = j) :
    events.length ≤ B_auth := by
  have hinj : Function.Injective (fun i : Fin events.length =>
      (⟨(events.get i).epoch - 1, by
        have hmem := List.get_mem events i
        obtain ⟨h, hhQ, hhH⟩ :=
          quorum_has_honest_of_lt_threshold (htrace.quorum_size _ hmem) hcorr
        have hb := htrace.honest_budget _ hmem h hhQ hhH; omega⟩ : Fin B_auth)) := by
    intro i j hij
    have heq : (events.get i).epoch - 1 = (events.get j).epoch - 1 := congrArg Fin.val hij
    obtain ⟨hi, hhiQ, hhiH⟩ :=
      quorum_has_honest_of_lt_threshold (htrace.quorum_size _ (List.get_mem events i)) hcorr
    obtain ⟨hj, hhjQ, hhjH⟩ :=
      quorum_has_honest_of_lt_threshold (htrace.quorum_size _ (List.get_mem events j)) hcorr
    have hbi := htrace.honest_budget _ (List.get_mem events i) hi hhiQ hhiH
    have hbj := htrace.honest_budget _ (List.get_mem events j) hj hhjQ hhjH
    exact hpol i j (by omega)
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

/-- `#tooth` (`tooth_split_quorum_without_intersection`): without `n + |corrupt| < 2t` or policy
binding, `corrupt = {0}` at `n = 3, t = 2` splits `{0,1}` and `{0,2}` at `epoch = 1` (`2 > B_auth`). -/
theorem tooth_split_quorum_without_intersection :
    let corrupt : Finset (Fin 3) := {0}
    let events : List (CustodyCrossingEvent 3) := [⟨1, {0, 1}, 101⟩, ⟨1, {0, 2}, 202⟩]
    ¬ (3 + corrupt.card < 2 * 2) ∧
    ValidThresholdCrossingTrace 3 2 1 corrupt events ∧ events.length > 1 := by
  refine ⟨by decide, ⟨by decide, by decide, ?_⟩, by decide⟩
  intro i j hij h hhcorr hhi hhj
  fin_cases i <;> fin_cases j <;> fin_cases h <;> simp_all

end CustodyImpossibilityAndThreshold

/-! ## §2. Theorem 2 — Stateful GDN WY Continual Update & Coefficient-Packed `B61` Ring Isomorphism -/

section StatefulWyAndB61Packing

@[instance_reducible]
def unitLowerTriInvertible {R : Type*} [CommRing R] {τ : ℕ}
    {L : Matrix (Fin τ) (Fin τ) R} (hL : IsStrictLowerTri L) : Invertible (1 + L) where
  invOf := neumannInv L
  invOf_mul_self := neumannInv_mul_eq_one hL
  mul_invOf_self := mul_neumannInv_eq_one hL

/-- **Theorem 2a (`unitLowerTri_invertible_ring`):** strictly lower-triangular `L` makes `1 + L`
two-sidedly invertible (`IsUnit (1 + L)`) over ANY `CommRing R` with zero divisions. -/
theorem unitLowerTri_invertible_ring {R : Type*} [CommRing R] {τ : ℕ}
    {L : Matrix (Fin τ) (Fin τ) R} (hL : IsStrictLowerTri L) :
    (1 + L) * neumannInv L = 1 ∧ neumannInv L * (1 + L) = 1 ∧ IsUnit (1 + L) :=
  ⟨mul_neumannInv_eq_one hL, neumannInv_mul_eq_one hL,
    ⟨⟨1 + L, neumannInv L, mul_neumannInv_eq_one hL, neumannInv_mul_eq_one hL⟩, rfl⟩⟩

structure FastWeightStepInput (R : Type*) (dv dk : ℕ) where
  γ : R
  β : R
  k : Fin dk → R
  v : Fin dv → R

/-- Sequential fast-weight step `S_{t+1} = γ_t S_t + β_t (v_t - S_t k_t) k_tᵀ`. -/
def fastWeightStep {R : Type*} [CommRing R] {dv dk : ℕ}
    (inp : FastWeightStepInput R dv dk) (S : Matrix (Fin dv) (Fin dk) R) :
    Matrix (Fin dv) (Fin dk) R :=
  inp.γ • S + inp.β • Matrix.vecMulVec (inp.v - S.mulVec inp.k) inp.k

def fastWeightSeq {R : Type*} [CommRing R] {dv dk : ℕ}
    (steps : List (FastWeightStepInput R dv dk)) (S₀ : Matrix (Fin dv) (Fin dk) R) :
    Matrix (Fin dv) (Fin dk) R :=
  steps.foldl (fun S inp => fastWeightStep inp S) S₀
@[simp] theorem fastWeightSeq_nil {R : Type*} [CommRing R] {dv dk : ℕ}
    (S₀ : Matrix (Fin dv) (Fin dk) R) : fastWeightSeq [] S₀ = S₀ := rfl
@[simp] theorem fastWeightSeq_cons {R : Type*} [CommRing R] {dv dk : ℕ}
    (inp : FastWeightStepInput R dv dk) (steps : List (FastWeightStepInput R dv dk))
    (S₀ : Matrix (Fin dv) (Fin dk) R) :
    fastWeightSeq (inp :: steps) S₀ = fastWeightSeq steps (fastWeightStep inp S₀) := rfl
theorem fastWeightSeq_append {R : Type*} [CommRing R] {dv dk : ℕ}
    (xs ys : List (FastWeightStepInput R dv dk)) (S₀ : Matrix (Fin dv) (Fin dk) R) :
    fastWeightSeq (xs ++ ys) S₀ = fastWeightSeq ys (fastWeightSeq xs S₀) := List.foldl_append
def chunkPrefixList {A : Type*} {τ : ℕ} (chunk : Fin τ → A) : (n : ℕ) → n ≤ τ → List A
  | 0, _ => []
  | n + 1, hn => chunkPrefixList chunk n (Nat.le_of_succ_le hn) ++ [chunk ⟨n, hn⟩]
theorem chunkPrefixList_length {A : Type*} {τ : ℕ} (chunk : Fin τ → A) :
    ∀ (n : ℕ) (hn : n ≤ τ), (chunkPrefixList chunk n hn).length = n
  | 0, _ => rfl
  | n + 1, hn => by simp [chunkPrefixList, chunkPrefixList_length chunk n (Nat.le_of_succ_le hn)]
theorem chunkPrefixList_getElem {A : Type*} {τ : ℕ} (chunk : Fin τ → A) :
    ∀ (n : ℕ) (hn : n ≤ τ) (i : ℕ) (hi : i < (chunkPrefixList chunk n hn).length),
      (chunkPrefixList chunk n hn)[i]'hi =
        chunk ⟨i, Nat.lt_of_lt_of_le (by simpa [chunkPrefixList_length] using hi) hn⟩
  | 0, _, i, hi => by simp [chunkPrefixList] at hi
  | n + 1, hn, i, hi => by
      have hi' : i < n + 1 := by simpa [chunkPrefixList_length] using hi
      simp only [chunkPrefixList]
      by_cases hlt : i < n
      · have hlt_len : i < (chunkPrefixList chunk n (Nat.le_of_succ_le hn)).length := by
          simpa [chunkPrefixList_length] using hlt
        rw [List.getElem_append_left hlt_len]
        exact chunkPrefixList_getElem chunk n (Nat.le_of_succ_le hn) i hlt_len
      · obtain rfl : i = n := by omega
        have hge : (chunkPrefixList chunk i (Nat.le_of_succ_le hn)).length ≤ i := by
          simp [chunkPrefixList_length]
        rw [List.getElem_append_right hge]; simp [chunkPrefixList_length]
theorem chunkPrefixList_full {A : Type*} {τ : ℕ} (chunk : Fin τ → A) :
    chunkPrefixList chunk τ (le_refl τ) = List.ofFn chunk := by
  apply List.ext_getElem
  · simp [chunkPrefixList_length]
  · intro i hi₁ _; rw [chunkPrefixList_getElem, List.getElem_ofFn]
def decayProd {R : Type*} [CommRing R] {τ : ℕ} (γ : Fin τ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | b + 1 => if a ≤ b then (if hb : b < τ then γ ⟨b, hb⟩ else 1) * decayProd γ a b else 1
@[simp] theorem decayProd_self {R : Type*} [CommRing R] {τ : ℕ} (γ : Fin τ → R) (a : ℕ) :
    decayProd γ a a = 1 := by
  cases a with
  | zero => rfl
  | succ k => unfold decayProd; simp [show ¬ (k + 1 ≤ k) by omega]
theorem decayProd_succ_of_le {R : Type*} [CommRing R] {τ : ℕ} (γ : Fin τ → R)
    {a n : ℕ} (han : a ≤ n) (hn : n < τ) :
    decayProd γ a (n + 1) = γ ⟨n, hn⟩ * decayProd γ a n := by
  conv_lhs => unfold decayProd; simp [han, hn]
def wyGamma {R : Type*} [CommRing R] {τ dv dk : ℕ} (chunk : Fin τ → FastWeightStepInput R dv dk) : R :=
  decayProd (fun m => (chunk m).γ) 0 τ
def wyCouplingL {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) : Matrix (Fin τ) (Fin τ) R :=
  fun i j => if j < i then
    (chunk i).β * decayProd (fun m => (chunk m).γ) (j.val + 1) i.val *
      dotProduct (chunk j).k (chunk i).k else 0
theorem wyCouplingL_isStrictLowerTri {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) : IsStrictLowerTri (wyCouplingL chunk) := by
  intro i j hij; simp [wyCouplingL, not_lt_of_ge hij]
def wyValueMat {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) : Matrix (Fin τ) (Fin dv) R :=
  fun i r => (chunk i).β * (chunk i).v r
def wyKeyInMat {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) : Matrix (Fin τ) (Fin dk) R :=
  fun i c => (chunk i).β * decayProd (fun m => (chunk m).γ) 0 i.val * (chunk i).k c
def wyKeyDecayed {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) : Matrix (Fin dk) (Fin τ) R :=
  fun c j => decayProd (fun m => (chunk m).γ) (j.val + 1) τ * (chunk j).k c

theorem fastWeightPrefix_eq_wy {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) (S₀ : Matrix (Fin dv) (Fin dk) R)
    (U : Matrix (Fin τ) (Fin dv) R)
    (hWY : (1 + wyCouplingL chunk) * U = wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ) :
    ∀ (n : ℕ) (hn : n ≤ τ),
      fastWeightSeq (chunkPrefixList chunk n hn) S₀ =
        decayProd (fun m => (chunk m).γ) 0 n • S₀ +
          ∑ j ∈ Finset.univ.filter (fun j : Fin τ => j.val < n),
            decayProd (fun m => (chunk m).γ) (j.val + 1) n •
              Matrix.vecMulVec (fun r => U j r) (chunk j).k := by
  have hRec :=
    ((wyChunk_bilinear_iff_recurrence (wyCouplingL_isStrictLowerTri chunk) U
        (wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ)).1.trans
      (wyChunk_bilinear_iff_recurrence (wyCouplingL_isStrictLowerTri chunk) U
        (wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ)).2).mp hWY
  intro n; induction n with
  | zero => intro _; simp [chunkPrefixList]
  | succ n ih =>
      intro hn; let i : Fin τ := ⟨n, hn⟩; have hn_le : n ≤ τ := Nat.le_of_succ_le hn
      simp only [chunkPrefixList, fastWeightSeq_append, fastWeightSeq_cons, fastWeightSeq_nil]
      rw [ih hn_le]
      set S_n := decayProd (fun m => (chunk m).γ) 0 n • S₀ +
        ∑ j ∈ Finset.univ.filter (fun j : Fin τ => j.val < n),
          decayProd (fun m => (chunk m).γ) (j.val + 1) n •
            Matrix.vecMulVec (fun r => U j r) (chunk j).k
      have hDec0 : (chunk i).γ • (decayProd (fun m => (chunk m).γ) 0 n • S₀) =
          decayProd (fun m => (chunk m).γ) 0 (n + 1) • S₀ := by
        rw [smul_smul, ← decayProd_succ_of_le (fun m => (chunk m).γ) (Nat.zero_le n) hn]
      have hDecSum : (chunk i).γ • (∑ j ∈ Finset.univ.filter (fun j : Fin τ => j.val < n),
            decayProd (fun m => (chunk m).γ) (j.val + 1) n •
              Matrix.vecMulVec (fun r => U j r) (chunk j).k) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin τ => j.val < n),
            decayProd (fun m => (chunk m).γ) (j.val + 1) (n + 1) •
              Matrix.vecMulVec (fun r => U j r) (chunk j).k := by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj => ?_
        have hj_lt : j.val < n := (Finset.mem_filter.mp hj).2
        rw [smul_smul, ← decayProd_succ_of_le (fun m => (chunk m).γ) (by omega) hn]
      have hU_eq : (chunk i).β • ((chunk i).v - S_n.mulVec (chunk i).k) = fun r => U i r := by
        funext r; have hUi := hRec i r
        have hFlt : Finset.univ.filter (· < i) = Finset.univ.filter (fun j : Fin τ => j.val < n) := by
          ext j; simp [i, Fin.lt_def]
        rw [hFlt] at hUi; let flt := Finset.univ.filter (fun j : Fin τ => j.val < n)
        have hMulVec : S_n.mulVec (chunk i).k r =
            decayProd (fun m => (chunk m).γ) 0 n * (∑ c : Fin dk, S₀ r c * (chunk i).k c) +
              ∑ j ∈ flt, decayProd (fun m => (chunk m).γ) (j.val + 1) n *
                dotProduct (chunk j).k (chunk i).k * U j r := by
          simp only [Matrix.mulVec, dotProduct, S_n, Matrix.add_apply, Matrix.smul_apply,
            Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
          trans (∑ c : Fin dk, decayProd (fun m => (chunk m).γ) 0 n * (S₀ r c * (chunk i).k c) +
              ∑ c : Fin dk, ∑ j ∈ flt, decayProd (fun m => (chunk m).γ) (j.val + 1) n *
                (U j r * (chunk j).k c) * (chunk i).k c)
          · rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [add_mul, Finset.sum_mul]; congr 1; ring
          · congr 1
            · rw [Finset.mul_sum]
            · rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        have hSub : (chunk i).β * ((chunk i).v r - S_n.mulVec (chunk i).k r) =
            (wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ) i r -
              ∑ j ∈ flt, wyCouplingL chunk i j * U j r := by
          rw [hMulVec, mul_sub, mul_add]
          have hK : (chunk i).β * (decayProd (fun m => (chunk m).γ) 0 n *
                ∑ c : Fin dk, S₀ r c * (chunk i).k c) =
              ∑ c : Fin dk, wyKeyInMat chunk i c * S₀ r c := by
            rw [← mul_assoc, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by dsimp [wyKeyInMat, i]; ring
          have hL : (chunk i).β * (∑ j ∈ flt, decayProd (fun m => (chunk m).γ) (j.val + 1) n *
                dotProduct (chunk j).k (chunk i).k * U j r) =
              ∑ j ∈ flt, wyCouplingL chunk i j * U j r := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j hj => ?_
            have hji : j < i := Fin.lt_def.mpr (Finset.mem_filter.mp hj).2
            simp only [wyCouplingL, hji, ↓reduceIte, i]; ring
          rw [hK, hL]
          simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, wyValueMat, i]; ring
        simpa [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, flt, hUi] using hSub
      have hRank1 : (chunk i).β • Matrix.vecMulVec ((chunk i).v - S_n.mulVec (chunk i).k) (chunk i).k =
          decayProd (fun m => (chunk m).γ) (i.val + 1) (n + 1) •
            Matrix.vecMulVec (fun r => U i r) (chunk i).k := by
        rw [decayProd_self _ (n + 1), one_smul, ← hU_eq]
        ext r c; simp [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
      have hSplit : Finset.univ.filter (fun j : Fin τ => j.val < n + 1) =
          insert i (Finset.univ.filter (fun j : Fin τ => j.val < n)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, i]; omega
      have hi_not : i ∉ Finset.univ.filter (fun j : Fin τ => j.val < n) := by simp [i]
      unfold fastWeightStep
      rw [smul_add, hDec0, hDecSum, hRank1, hSplit, Finset.sum_insert hi_not]; abel

/-- **Theorem 2b (`gdnFastWeight_wy_chunk_equiv`):** exact algebraic equivalence over ANY `CommRing R`
between sequential `τ`-step GDN fast-weight evolution and division-free WY chunk update. -/
theorem gdnFastWeight_wy_chunk_equiv {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) (S₀ : Matrix (Fin dv) (Fin dk) R)
    (U : Matrix (Fin τ) (Fin dv) R) :
    ((1 + wyCouplingL chunk) * U = wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ ↔
      U = neumannInv (wyCouplingL chunk) * (wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ)) ∧
    ((1 + wyCouplingL chunk) * U = wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ →
      fastWeightSeq (List.ofFn chunk) S₀ =
        wyGamma chunk • S₀ + Uᵀ * (wyKeyDecayed chunk)ᵀ) := by
  refine ⟨(wyChunk_bilinear_iff_recurrence (wyCouplingL_isStrictLowerTri chunk) U _).1, fun hWY => ?_⟩
  rw [← chunkPrefixList_full chunk, fastWeightPrefix_eq_wy chunk S₀ U hWY τ (le_refl τ)]
  have hUniv : Finset.univ.filter (fun j : Fin τ => j.val < τ) = Finset.univ := by ext j; simp
  rw [hUniv, wyGamma]; congr 1; ext r c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, wyKeyDecayed, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem gdnFastWeight_wy_chunk_zmod (t_spdz : ℕ) {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput (ZMod t_spdz) dv dk)
    (S₀ : Matrix (Fin dv) (Fin dk) (ZMod t_spdz)) :
    let U := neumannInv (wyCouplingL chunk) * (wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ)
    (1 + wyCouplingL chunk) * U = wyValueMat chunk - wyKeyInMat chunk * S₀ᵀ ∧
    fastWeightSeq (List.ofFn chunk) S₀ =
      wyGamma chunk • S₀ + Uᵀ * (wyKeyDecayed chunk)ᵀ := by
  intro U; have hEqv := gdnFastWeight_wy_chunk_equiv chunk S₀ U
  exact ⟨hEqv.1.mpr rfl, hEqv.2 (hEqv.1.mpr rfl)⟩

def b61N : ℕ := 8192
theorem b61N_val : b61N = 8192 := rfl

noncomputable def negacyclicModPoly (R : Type*) [CommRing R] (N : ℕ) : R[X] := X ^ N + C 1
noncomputable abbrev b61ModPoly (R : Type*) [CommRing R] : R[X] := negacyclicModPoly R b61N
abbrev B61PlainRing (t : ℕ) := AdjoinRoot (b61ModPoly (ZMod t))

theorem negacyclicModPoly_eq_add_one (R : Type*) [CommRing R] (N : ℕ) :
    negacyclicModPoly R N = X ^ N + 1 := by
  rw [negacyclicModPoly, map_one]

theorem negacyclicModPoly_monic (R : Type*) [CommRing R] {N : ℕ} (hN : N ≠ 0) :
    (negacyclicModPoly R N).Monic :=
  monic_X_pow_add_C 1 hN

theorem negacyclicModPoly_degree (R : Type*) [CommRing R] [Nontrivial R] {N : ℕ} (hN : 0 < N) :
    (negacyclicModPoly R N).degree = (N : WithBot ℕ) :=
  degree_X_pow_add_C hN 1

theorem b61ModPoly_monic (R : Type*) [CommRing R] : (b61ModPoly R).Monic :=
  negacyclicModPoly_monic R (by rw [b61N_val]; norm_num)

theorem b61ModPoly_degree (R : Type*) [CommRing R] [Nontrivial R] :
    (b61ModPoly R).degree = (b61N : WithBot ℕ) :=
  negacyclicModPoly_degree R (by rw [b61N_val]; norm_num)

noncomputable def tildeU {R : Type*} [CommRing R] (u : Fin 64 → R) : R[X] :=
  ∑ i : Fin 64, Polynomial.monomial (128 * i.val) (u i)

noncomputable def tildeK {R : Type*} [CommRing R] (k : Fin 128 → R) : R[X] :=
  ∑ j : Fin 128, Polynomial.monomial j.val (k j)

noncomputable def packSlicePoly {R : Type*} [CommRing R] (S : Matrix (Fin 64) (Fin 128) R) : R[X] :=
  ∑ i : Fin 64, ∑ j : Fin 128, Polynomial.monomial (128 * i.val + j.val) (S i j)

theorem tildeU_mul_tildeK_eq_packSlice {R : Type*} [CommRing R] (u : Fin 64 → R) (k : Fin 128 → R) :
    tildeU u * tildeK k = packSlicePoly (Matrix.vecMulVec u k) := by
  unfold tildeU tildeK packSlicePoly; rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.monomial_mul_monomial, Matrix.vecMulVec_apply]

theorem packSlicePoly_coeff_slot {R : Type*} [CommRing R] (S : Matrix (Fin 64) (Fin 128) R)
    (i : Fin 64) (j : Fin 128) :
    (packSlicePoly S).coeff (128 * i.val + j.val) = S i j := by
  unfold packSlicePoly; simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · exact ite_eq_left rfl
    · intro j' _ hj'
      exact ite_eq_right (fun h => hj' (Fin.ext (by omega)))
    · intro hj; exact False.elim (hj (Finset.mem_univ j))
  · intro i' _ hi'; apply Finset.sum_eq_zero; intro j' _
    have hi1 := i'.isLt; have hj1 := j'.isLt; have hi2 := i.isLt; have hj2 := j.isLt
    exact ite_eq_right (fun h => hi' (Fin.ext (by omega)))
  · intro hi; exact False.elim (hi (Finset.mem_univ i))

theorem packSlicePoly_coeff_of_ge_N {R : Type*} [CommRing R] (S : Matrix (Fin 64) (Fin 128) R)
    {N m : ℕ} (hN : 8192 ≤ N) (hm : N ≤ m) :
    (packSlicePoly S).coeff m = 0 := by
  unfold packSlicePoly; simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
  have hi := i.isLt; have hj := j.isLt
  exact ite_eq_right (by omega)

theorem packSlicePoly_degree_lt_negacyclic {R : Type*} [CommRing R] [Nontrivial R]
    (S : Matrix (Fin 64) (Fin 128) R) {N : ℕ} (hN : 8192 ≤ N) :
    (packSlicePoly S).degree < (negacyclicModPoly R N).degree := by
  rw [negacyclicModPoly_degree R (by omega)]
  by_cases hp : packSlicePoly S = 0
  · rw [hp, degree_zero]; exact WithBot.bot_lt_coe N
  · rw [degree_eq_natDegree hp, Nat.cast_lt]; by_contra hge
    exact leadingCoeff_ne_zero.mpr hp (packSlicePoly_coeff_of_ge_N S hN (Nat.le_of_not_lt hge))

/-- **Theorem 2c (`b61_coeff_outer_product_ring_identity`):**
In `R_t = (ℤ/tℤ)[X]/(X^{8192} + 1)`, `tildeU u * tildeK k` has degree `≤ 8191 < 8192` (**zero**
negacyclic wraparound) and `coeff ((tildeU u * tildeK k) %ₘ (X^{8192} + 1)) (128 * i + j) = u_i * k_j`. -/
theorem b61_coeff_outer_product_ring_identity {R : Type*} [CommRing R] [Nontrivial R]
    (u : Fin 64 → R) (k : Fin 128 → R) :
    63 * 128 + 127 = 8191 ∧
    b61ModPoly R = X ^ b61N + 1 ∧
    (tildeU u * tildeK k) %ₘ b61ModPoly R = tildeU u * tildeK k ∧
    (∀ (i : Fin 64) (j : Fin 128),
      ((tildeU u * tildeK k) %ₘ b61ModPoly R).coeff (128 * i.val + j.val) = u i * k j) ∧
    AdjoinRoot.mk (b61ModPoly R) (tildeU u) * AdjoinRoot.mk (b61ModPoly R) (tildeK k) =
      AdjoinRoot.mk (b61ModPoly R) (packSlicePoly (Matrix.vecMulVec u k)) := by
  have hmod : (tildeU u * tildeK k) %ₘ b61ModPoly R = tildeU u * tildeK k := by
    rw [tildeU_mul_tildeK_eq_packSlice]
    exact (modByMonic_eq_self_iff (b61ModPoly_monic R)).mpr
      (packSlicePoly_degree_lt_negacyclic _ (by rw [b61N_val]))
  refine ⟨by norm_num, negacyclicModPoly_eq_add_one R b61N, hmod, fun i j => ?_, ?_⟩
  · rw [hmod, tildeU_mul_tildeK_eq_packSlice, packSlicePoly_coeff_slot, Matrix.vecMulVec_apply]
  · rw [← map_mul, tildeU_mul_tildeK_eq_packSlice]

noncomputable def revKeyPoly {R : Type*} [CommRing R] (k : Fin 128 → R) : R[X] :=
  ∑ c : Fin 128, Polynomial.monomial (127 - c.val) (k c)

private theorem monomial_read {R : Type*} [CommRing R] [Nontrivial R]
    {N d slot : ℕ} (hN : 0 < N) (hslot : slot < N) (hwrap : d < N + slot) (v : R) :
    ((Polynomial.monomial d v) %ₘ negacyclicModPoly R N).coeff slot =
      if d = slot then v else 0 := by
  let q := negacyclicModPoly R N
  have hq : q.Monic := negacyclicModPoly_monic R (by omega)
  have hsmall (e : ℕ) (he : e < N) :
      Polynomial.monomial e v %ₘ q = Polynomial.monomial e v := by
    apply (modByMonic_eq_self_iff hq).mpr
    rw [negacyclicModPoly_degree R hN]
    exact lt_of_le_of_lt (degree_monomial_le e v) (by exact_mod_cast he)
  change ((Polynomial.monomial d v) %ₘ q).coeff slot = _
  by_cases hd : d < N
  · rw [hsmall d hd, Polynomial.coeff_monomial]
  · let m := Polynomial.monomial (d - N) v
    have hsplit : Polynomial.monomial d v = m * q - m := by
      rw [show q = X ^ N + 1 from negacyclicModPoly_eq_add_one R N, mul_add, mul_one,
        add_sub_cancel_right, ← Polynomial.monomial_one_right_eq_X_pow]
      rw [show m = Polynomial.monomial (d - N) v from rfl, Polynomial.monomial_mul_monomial,
        mul_one, Nat.sub_add_cancel (by omega)]
    rw [hsplit, sub_modByMonic, mul_self_modByMonic hq, zero_sub, coeff_neg,
      hsmall (d - N) (by omega), coeff_monomial, ite_eq_right (by omega), neg_zero,
      ite_eq_right (by omega)]

private theorem read_sum {R : Type*} [CommRing R] [Nontrivial R] {a b N : ℕ}
    (ha : a = 64) (hb : b = 128) (hN : N = 8192)
    (S : Matrix (Fin a) (Fin b) R) (k : Fin b → R) (i : Fin a) :
    (((∑ r, ∑ j, Polynomial.monomial (128 * r.val + j.val) (S r j)) *
      (∑ c, Polynomial.monomial (127 - c.val) (k c))) %ₘ negacyclicModPoly R N).coeff
      (128 * i.val + 127) = (S.mulVec k) i := by
  change ((Polynomial.modByMonicHom (negacyclicModPoly R N)) _).coeff _ = _
  simp only [Finset.sum_mul, Finset.mul_sum, Polynomial.monomial_mul_monomial, map_sum,
    Polynomial.finsetSum_coeff, Polynomial.modByMonicHom_apply]
  have hi := i.isLt
  have term (r : Fin a) (j c : Fin b) :
      ((Polynomial.monomial (128 * r.val + j.val + (127 - c.val)) (S r j * k c)) %ₘ
        negacyclicModPoly R N).coeff (128 * i.val + 127) =
        if r = i ∧ j = c then S r j * k c else 0 := by
    have hr := r.isLt; have hj := j.isLt; have hc := c.isLt
    rw [monomial_read (by omega) (by omega) (by omega)]
    congr 1
    exact propext ⟨fun h => ⟨Fin.ext (by omega), Fin.ext (by omega)⟩, by rintro ⟨rfl, rfl⟩; omega⟩
  simp_rw [term, ite_and]
  simp [Matrix.mulVec, dotProduct]

theorem matvec_read_mod_negacyclic {R : Type*} [CommRing R] [Nontrivial R] {N : ℕ} (hN : N = 8192)
    (S : Matrix (Fin 64) (Fin 128) R) (k : Fin 128 → R) (i : Fin 64) :
    ((packSlicePoly S * revKeyPoly k) %ₘ negacyclicModPoly R N).coeff (128 * i.val + 127) =
      (S.mulVec k) i := read_sum rfl rfl hN S k i

/-- **Companion Readout Identity (`b61_coeff_matvec_read_identity`):**
`((packSlicePoly S * revKeyPoly k) %ₘ (X^{8192} + 1)).coeff (128 * i + 127) = (S *ᵥ k)_i` (`8318 - 8192 = 126 < 127`). -/
theorem b61_coeff_matvec_read_identity {R : Type*} [CommRing R] [Nontrivial R]
    (S : Matrix (Fin 64) (Fin 128) R) (k : Fin 128 → R) (i : Fin 64) :
    ((packSlicePoly S * revKeyPoly k) %ₘ b61ModPoly R).coeff (128 * i.val + 127) =
      (S.mulVec k) i :=
  matvec_read_mod_negacyclic b61N_val S k i

def qwen35FastWeightPackEquiv : (Fin 16 × Fin 128 × Fin 128) ≃ (Fin 32 × Fin b61N) where
  toFun := fun ⟨h, r, c⟩ =>
    (⟨2 * h.val + r.val / 64, by have := h.isLt; have := r.isLt; omega⟩,
      ⟨128 * (r.val % 64) + c.val, by have := r.isLt; have := c.isLt; rw [b61N_val]; omega⟩)
  invFun := fun ⟨b, slot⟩ =>
    (⟨b.val / 2, by have := b.isLt; omega⟩,
      ⟨64 * (b.val % 2) + slot.val / 128, by
        have hb := b.isLt; have hs : slot.val < 8192 := by simpa [b61N_val] using slot.isLt
        omega⟩,
      ⟨slot.val % 128, by omega⟩)
  left_inv := fun ⟨h, r, c⟩ => by
    have := h.isLt; have := r.isLt; have := c.isLt; ext <;> simp only <;> omega
  right_inv := fun ⟨b, slot⟩ => by
    have hb := b.isLt; have hs : slot.val < 8192 := by simpa [b61N_val] using slot.isLt
    ext <;> simp only <;> omega

theorem b61_qwen35_32ct_packing_bijection :
    Fintype.card (Fin 16 × Fin 128 × Fin 128) = 262144 ∧
    Fintype.card (Fin 32 × Fin b61N) = 262144 ∧
    Function.Bijective qwen35FastWeightPackEquiv :=
  ⟨by simp only [Fintype.card_prod, Fintype.card_fin],
   by rw [← Fintype.card_congr qwen35FastWeightPackEquiv]; simp only [Fintype.card_prod, Fintype.card_fin],
   qwen35FastWeightPackEquiv.bijective⟩

theorem negacyclic_degree_N_sign_flip {N : ℕ} :
    AdjoinRoot.mk (negacyclicModPoly ℤ N) (Polynomial.monomial N (1 : ℤ)) =
      AdjoinRoot.mk (negacyclicModPoly ℤ N) (Polynomial.C (-1 : ℤ)) := by
  have h1 : Polynomial.monomial N (1 : ℤ) = negacyclicModPoly ℤ N + Polynomial.C (-1 : ℤ) := by
    rw [Polynomial.monomial_one_right_eq_X_pow, negacyclicModPoly, add_assoc, ← C.map_add]; norm_num
  rw [h1, map_add, AdjoinRoot.mk_self, zero_add]

theorem tooth_b61_degree_8192_negacyclic_sign_flip :
    AdjoinRoot.mk (b61ModPoly ℤ) (Polynomial.monomial (128 * 64) (1 : ℤ)) =
      AdjoinRoot.mk (b61ModPoly ℤ) (Polynomial.C (-1 : ℤ)) ∧
    Polynomial.C (-1 : ℤ) ≠ Polynomial.C (1 : ℤ) := by
  refine ⟨?_, fun h => by have hc := congrArg (fun p : ℤ[X] => p.coeff 0) h; norm_num at hc⟩
  have hN : 128 * 64 = b61N := rfl
  rw [hN]; exact negacyclic_degree_N_sign_flip

end StatefulWyAndB61Packing

/-! ## §3. Theorem 3 — Exact `W0` Subspace Unlearning, WY Chunk Replay, & Cross-Term Tooth -/

section ExactW0Unlearning

def tombEpisode {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (ep : Fin τ → FastWeightStepInput R dv dk) : Fin τ → FastWeightStepInput R dv dk :=
  fun m => { γ := (ep m).γ, β := 0, k := (ep m).k, v := (ep m).v }

theorem fastWeightSeq_tombEpisode {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (ep : Fin τ → FastWeightStepInput R dv dk) (S_pre : Matrix (Fin dv) (Fin dk) R) :
    fastWeightSeq (List.ofFn (tombEpisode ep)) S_pre = wyGamma ep • S_pre := by
  have hEqv := gdnFastWeight_wy_chunk_equiv (tombEpisode ep) S_pre 0
  have hZero : (1 + wyCouplingL (tombEpisode ep)) * (0 : Matrix (Fin τ) (Fin dv) R) =
      wyValueMat (tombEpisode ep) - wyKeyInMat (tombEpisode ep) * S_preᵀ := by
    ext i r; simp [tombEpisode, wyValueMat, wyKeyInMat, Matrix.mul_apply]
  simpa [show wyGamma (tombEpisode ep) = wyGamma ep from rfl] using hEqv.2 hZero

def postSeqDecay {R : Type*} [CommRing R] {dv dk : ℕ} :
    List (FastWeightStepInput R dv dk) → R
  | [] => 1
  | st :: rest => postSeqDecay rest * st.γ

theorem fastWeightStep_add_orthogonal_delta {R : Type*} [CommRing R] {dv dk : ℕ}
    (st : FastWeightStepInput R dv dk) (S Δ : Matrix (Fin dv) (Fin dk) R)
    (horth : Δ.mulVec st.k = 0) :
    fastWeightStep st (S + Δ) = fastWeightStep st S + st.γ • Δ := by
  unfold fastWeightStep; rw [Matrix.add_mulVec, horth, add_zero, smul_add]; abel

theorem fastWeightSeq_add_orthogonal_sketch {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (U_ep : Matrix (Fin τ) (Fin dv) R) (K_dec : Matrix (Fin dk) (Fin τ) R) :
    ∀ (post : List (FastWeightStepInput R dv dk)) (S_base : Matrix (Fin dv) (Fin dk) R) (g : R),
      (∀ st ∈ post, ∀ m : Fin τ, dotProduct (fun c => K_dec c m) st.k = 0) →
      fastWeightSeq post (S_base + g • (U_epᵀ * K_decᵀ)) =
        fastWeightSeq post S_base + (postSeqDecay post * g) • (U_epᵀ * K_decᵀ)
  | [], S_base, g, _ => by simp [postSeqDecay]
  | st :: rest, S_base, g, horth => by
      have hmul0 : (g • (U_epᵀ * K_decᵀ)).mulVec st.k = 0 := by
        funext r
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.mul_apply,
          Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply]
        have hswap : (∑ c : Fin dk, g * (∑ m : Fin τ, U_ep m r * K_dec c m) * st.k c) =
            ∑ m : Fin τ, g * U_ep m r * (∑ c : Fin dk, K_dec c m * st.k c) := by
          trans (∑ c : Fin dk, ∑ m : Fin τ, g * U_ep m r * (K_dec c m * st.k c))
          · refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun m _ => (Finset.mul_sum ..).symm
        rw [hswap]; apply Finset.sum_eq_zero; intro m _
        have hz : ∑ c : Fin dk, K_dec c m * st.k c = 0 := horth st (List.mem_cons_self ..) m
        rw [hz, mul_zero]
      simp only [fastWeightSeq_cons, postSeqDecay]
      rw [fastWeightStep_add_orthogonal_delta st S_base _ hmul0, smul_smul,
        fastWeightSeq_add_orthogonal_sketch U_ep K_dec rest (fastWeightStep st S_base) (st.γ * g)
          (fun s hs m => horth s (List.mem_cons_of_mem _ hs) m), mul_assoc]

/-- **Theorem 3a (`w0_unlearn_orthogonal_sketch_exact`):**
When post-episode keys are orthogonal (`K_{t>e}ᵀ K_e = 0`), homomorphic decayed sketch subtraction
`S_T - postSeqDecay post • Δ_e` equals `S_retrained_without_e` (`tombEpisode` for general `γ_e`,
and literal omission `fastWeightSeq post S_pre` when `∀ m, (ep m).γ = 1`). -/
theorem w0_unlearn_orthogonal_sketch_exact {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (ep : Fin τ → FastWeightStepInput R dv dk)
    (post : List (FastWeightStepInput R dv dk))
    (S_pre : Matrix (Fin dv) (Fin dk) R)
    (U_e : Matrix (Fin τ) (Fin dv) R)
    (hWY : (1 + wyCouplingL ep) * U_e = wyValueMat ep - wyKeyInMat ep * S_preᵀ)
    (horth : ∀ st ∈ post, ∀ m : Fin τ, dotProduct (ep m).k st.k = 0) :
    let Δ_e := U_eᵀ * (wyKeyDecayed ep)ᵀ
    let S_T := fastWeightSeq post (fastWeightSeq (List.ofFn ep) S_pre)
    S_T - postSeqDecay post • Δ_e =
      fastWeightSeq post (fastWeightSeq (List.ofFn (tombEpisode ep)) S_pre) ∧
    ((∀ m : Fin τ, (ep m).γ = 1) →
      S_T - postSeqDecay post • Δ_e = fastWeightSeq post S_pre) := by
  have hEp := (gdnFastWeight_wy_chunk_equiv ep S_pre U_e).2 hWY
  have hTomb := fastWeightSeq_tombEpisode ep S_pre
  have horth_dec : ∀ st ∈ post, ∀ m : Fin τ, dotProduct (fun c => wyKeyDecayed ep c m) st.k = 0 := by
    intro st hst m; have hm0 : dotProduct (ep m).k st.k = 0 := horth st hst m
    simp only [dotProduct, wyKeyDecayed] at hm0 ⊢
    have hfactor : (∑ c : Fin dk, decayProd (fun x => (ep x).γ) (m.val + 1) τ * (ep m).k c * st.k c) =
        decayProd (fun x => (ep x).γ) (m.val + 1) τ * ∑ c : Fin dk, (ep m).k c * st.k c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfactor, hm0, mul_zero]
  have hProp := fastWeightSeq_add_orthogonal_sketch U_e (wyKeyDecayed ep) post (wyGamma ep • S_pre) 1 horth_dec
  simp only [one_smul, mul_one] at hProp
  refine ⟨by rw [hEp, hTomb, hProp, add_sub_cancel_right], fun hUnit => ?_⟩
  have hGam1 : wyGamma ep = 1 := by
    unfold wyGamma
    suffices ∀ n ≤ τ, decayProd (fun m => (ep m).γ) 0 n = 1 from this τ (le_refl τ)
    intro n; induction n with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk; rw [decayProd_succ_of_le _ (Nat.zero_le k) hk, hUnit ⟨k, hk⟩, one_mul,
          ih (Nat.le_of_succ_le hk)]
  rw [hEp, hProp, hGam1, one_smul, add_sub_cancel_right]

def flattenFastChunks {R : Type*} {τ dv dk : ℕ} :
    {C : ℕ} → (Fin C → Fin τ → FastWeightStepInput R dv dk) → List (FastWeightStepInput R dv dk)
  | 0, _ => []
  | _ + 1, chunks => List.ofFn (chunks 0) ++ flattenFastChunks (fun c => chunks c.succ)

def replayWyChunks {R : Type*} [CommRing R] {τ dv dk : ℕ} :
    {C : ℕ} → (Fin C → Fin τ → FastWeightStepInput R dv dk) →
      Matrix (Fin dv) (Fin dk) R → Matrix (Fin dv) (Fin dk) R
  | 0, _, S => S
  | _ + 1, chunks, S =>
      let c0 := chunks 0
      let U0 := neumannInv (wyCouplingL c0) * (wyValueMat c0 - wyKeyInMat c0 * Sᵀ)
      replayWyChunks (fun c => chunks c.succ) (wyGamma c0 • S + U0ᵀ * (wyKeyDecayed c0)ᵀ)

def wyChunkAffineOp {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (chunk : Fin τ → FastWeightStepInput R dv dk) :
    Matrix (Fin dk) (Fin dk) R × Matrix (Fin dv) (Fin dk) R :=
  let N := neumannInv (wyCouplingL chunk)
  (wyGamma chunk • (1 : Matrix (Fin dk) (Fin dk) R) -
      (wyKeyInMat chunk)ᵀ * Nᵀ * (wyKeyDecayed chunk)ᵀ,
    (wyValueMat chunk)ᵀ * Nᵀ * (wyKeyDecayed chunk)ᵀ)

def applyAffineOps {R : Type*} [CommRing R] {dv dk : ℕ} :
    List (Matrix (Fin dk) (Fin dk) R × Matrix (Fin dv) (Fin dk) R) →
      Matrix (Fin dv) (Fin dk) R → Matrix (Fin dv) (Fin dk) R
  | [], S => S
  | (A, B) :: ops, S => applyAffineOps ops (S * A + B)

/-- **Theorem 3b (`w0_unlearn_wy_chunk_replay_exact` & `w0_unlearn_wy_affine_operator_exact`):**
For general overlapping keys (`K_{t>e}ᵀ K_e ≠ 0`), compressed WY chunk-operator replay from `S_pre`
equals `S_retrained_without_e` identically over ANY `CommRing R`. -/
theorem w0_unlearn_wy_chunk_replay_exact {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (preSteps : List (FastWeightStepInput R dv dk))
    {C : ℕ} (postChunks : Fin C → Fin τ → FastWeightStepInput R dv dk)
    (S₀ : Matrix (Fin dv) (Fin dk) R) :
    replayWyChunks postChunks (fastWeightSeq preSteps S₀) =
      fastWeightSeq (preSteps ++ flattenFastChunks postChunks) S₀ := by
  rw [fastWeightSeq_append]
  suffices ∀ {C' : ℕ} (cs : Fin C' → Fin τ → FastWeightStepInput R dv dk)
      (S : Matrix (Fin dv) (Fin dk) R),
      replayWyChunks cs S = fastWeightSeq (flattenFastChunks cs) S from
    this postChunks (fastWeightSeq preSteps S₀)
  intro C' cs S; induction C' generalizing S with
  | zero => rfl
  | succ C' ih =>
      simp only [replayWyChunks, flattenFastChunks, fastWeightSeq_append]
      have hEqv := gdnFastWeight_wy_chunk_equiv (cs 0) S
        (neumannInv (wyCouplingL (cs 0)) * (wyValueMat (cs 0) - wyKeyInMat (cs 0) * Sᵀ))
      rw [← hEqv.2 (hEqv.1.mpr rfl)]; exact ih (fun c => cs c.succ) _

theorem w0_unlearn_wy_affine_operator_exact {R : Type*} [CommRing R] {τ dv dk : ℕ}
    (preSteps : List (FastWeightStepInput R dv dk))
    {C : ℕ} (postChunks : Fin C → Fin τ → FastWeightStepInput R dv dk)
    (S₀ : Matrix (Fin dv) (Fin dk) R) :
    applyAffineOps (List.ofFn (fun c => wyChunkAffineOp (postChunks c))) (fastWeightSeq preSteps S₀) =
      fastWeightSeq (preSteps ++ flattenFastChunks postChunks) S₀ := by
  rw [← w0_unlearn_wy_chunk_replay_exact]
  suffices ∀ {C' : ℕ} (cs : Fin C' → Fin τ → FastWeightStepInput R dv dk)
      (S : Matrix (Fin dv) (Fin dk) R),
      applyAffineOps (List.ofFn (fun c => wyChunkAffineOp (cs c))) S = replayWyChunks cs S from
    this postChunks (fastWeightSeq preSteps S₀)
  intro C' cs S; induction C' generalizing S with
  | zero => rfl
  | succ C' ih =>
      rw [List.ofFn_succ, applyAffineOps, replayWyChunks, ih (fun c => cs c.succ)]
      congr 1; unfold wyChunkAffineOp
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
      abel

theorem naive_subtract_discrepancy_eq_cross_term {R : Type*} [CommRing R] {dv dk : ℕ}
    (ep st : FastWeightStepInput R dv dk) (S₀ : Matrix (Fin dv) (Fin dk) R) (hγ0 : ep.γ = 1) :
    let u₀ := ep.β • (ep.v - S₀.mulVec ep.k)
    let Δ₀ := Matrix.vecMulVec u₀ ep.k
    fastWeightStep st S₀ - (fastWeightStep st (fastWeightStep ep S₀) - st.γ • Δ₀) =
      (st.β * dotProduct ep.k st.k) • Matrix.vecMulVec u₀ st.k := by
  ext r c
  simp only [fastWeightStep, hγ0, one_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  have hexp :
      (∑ x : Fin dk, (S₀ r x + ep.β * ((ep.v r - ∑ y : Fin dk, S₀ r y * ep.k y) * ep.k x)) * st.k x) =
        (∑ x : Fin dk, S₀ r x * st.k x) +
          ep.β * (ep.v r - ∑ y : Fin dk, S₀ r y * ep.k y) * (∑ x : Fin dk, ep.k x * st.k x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp]; ring

/-- **`#tooth` Falsifier (`naive_subtract_cross_term_tooth`):** naive sketch subtraction fails
whenever `ep.k ⬝ᵥ st.k ≠ 0` (`st.β ≠ 0`, `u₀ ≠ 0`, `st.k ≠ 0`), while WY replay stays exact. -/
theorem naive_subtract_cross_term_tooth :
    (∀ {D : Type*} [CommRing D] [NoZeroDivisors D] {dv dk : ℕ}
      (ep st : FastWeightStepInput D dv dk) (S₀ : Matrix (Fin dv) (Fin dk) D)
      (r : Fin dv) (c : Fin dk),
      ep.γ = 1 → st.β ≠ 0 → dotProduct ep.k st.k ≠ 0 →
      (ep.β • (ep.v - S₀.mulVec ep.k)) r ≠ 0 → st.k c ≠ 0 →
      fastWeightStep st (fastWeightStep ep S₀) -
          st.γ • Matrix.vecMulVec (ep.β • (ep.v - S₀.mulVec ep.k)) ep.k ≠
        fastWeightStep st S₀) ∧
    (let ep : FastWeightStepInput (ZMod 17) 2 2 := ⟨1, 1, ![1, 0], ![5, 3]⟩
     let st : FastWeightStepInput (ZMod 17) 2 2 := ⟨2, 1, ![1, 1], ![9, 4]⟩
     let S₀ : Matrix (Fin 2) (Fin 2) (ZMod 17) := 0
     let u₀ := ep.β • (ep.v - S₀.mulVec ep.k)
     let S_naive := fastWeightStep st (fastWeightStep ep S₀) - st.γ • Matrix.vecMulVec u₀ ep.k
     let S_retrained := fastWeightStep st S₀
     let S_wy := replayWyChunks (fun _ : Fin 1 => fun _ : Fin 1 => st) S₀
     dotProduct ep.k st.k ≠ 0 ∧ S_naive ≠ S_retrained ∧ S_wy = S_retrained) := by
  refine ⟨?_, by decide⟩
  intro D _ _ dv dk ep st S₀ r c hγ0 hβ hdot hu hk heq
  have hdisc := naive_subtract_discrepancy_eq_cross_term ep st S₀ hγ0
  dsimp only at hdisc; rw [heq, sub_self] at hdisc
  have hrc := congrArg (fun M => M r c) hdisc.symm
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply, smul_eq_mul] at hrc
  exact mul_ne_zero (mul_ne_zero hβ hdot) (mul_ne_zero hu hk) hrc

end ExactW0Unlearning

/-! ## §4. `#guard_msgs`-Pinned Axiom Audit (`0` Custom Axioms) -/

/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.single_provider_cannot_prevent_shadow_branching' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms single_provider_cannot_prevent_shadow_branching
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.threshold_custody_prevents_shadow_branching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms threshold_custody_prevents_shadow_branching
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.threshold_policy_token_prevents_shadow_branching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms threshold_policy_token_prevents_shadow_branching
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.tooth_split_quorum_without_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_split_quorum_without_intersection
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.unitLowerTri_invertible_ring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unitLowerTri_invertible_ring
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.gdnFastWeight_wy_chunk_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnFastWeight_wy_chunk_equiv
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.gdnFastWeight_wy_chunk_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gdnFastWeight_wy_chunk_zmod
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.b61_coeff_outer_product_ring_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms b61_coeff_outer_product_ring_identity
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.b61_coeff_matvec_read_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms b61_coeff_matvec_read_identity
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.b61_qwen35_32ct_packing_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms b61_qwen35_32ct_packing_bijection
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.tooth_b61_degree_8192_negacyclic_sign_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_b61_degree_8192_negacyclic_sign_flip
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.w0_unlearn_orthogonal_sketch_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms w0_unlearn_orthogonal_sketch_exact
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.w0_unlearn_wy_chunk_replay_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms w0_unlearn_wy_chunk_replay_exact
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.w0_unlearn_wy_affine_operator_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms w0_unlearn_wy_affine_operator_exact
/-- info: 'Minidregg.Assurance.DarkB61ContinualGdn.naive_subtract_cross_term_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms naive_subtract_cross_term_tooth

end Minidregg.Assurance.DarkB61ContinualGdn
