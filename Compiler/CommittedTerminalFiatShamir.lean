/-
# Compiler.CommittedTerminalFiatShamir -- the controller's challenges under the tree's Fiat–Shamir theorem

`CommittedTerminalController.check` takes `gamma` and the round challenges as
INPUTS ("their Fiat–Shamir derivation is not this controller's").  This module
puts them under the tree's Fiat–Shamir keystone (`Selvage/FiatShamir.lean`,
`fsKeystone_proved : FsOfRbrKeystone`) rather than inventing an oracle model:

* **§2 the protocol as a `Reduction`** (`gateReduction`, Selvage/Rbr.lean):
  `k = m + 1` public-coin rounds -- the gamma round (a junk zeroth prover
  message, then `γ`) and the `m` sumcheck rounds (`(g_i(0), g_i(1))`, then
  `r_i`); the statement is `(root, word)` -- the word is the reduction's
  IMPLICIT INSTANCE `𝕪`, read in full by the verifier (full-word resolution);
  `verify` IS `check` at the challenges with the terminal recomputed from the
  word (`gateVerify_some_iff`).  The source relation: the word recommits to
  the root and satisfies the descriptor.  The target relation is `True`: at
  full word nothing is handed on, so knowledge soundness here is plain
  soundness (`W = Unit`).  `δ* = 1/n` makes the paper's `δ`-relaxation exact
  (`relaxedMem_iff`: below `1/n` a word within fractional distance `δ` of `y⋆`
  IS `y⋆`).
* **§3 the knowledge state function** (Def 4.1): at the empty transcript, the
  source relation; after `(π₀, γ)` and `i` sumcheck rounds, every Boolean
  check so far and the running claim equal to the honest level-`i` residual
  claim of the gamma table (`residualSum`, REUSED); at the full transcript,
  exactly the verifier's verdict (`full_iff`, through `residualSum_full` and
  `read_laneTerminal`).
* **§4 relaxed round-by-round knowledge soundness** (Def 4.2, `gateRbr`): the
  gamma round's bad event is the gamma event of `CommittedTerminalCompose`
  (a failing trace whose batched residual vanishes at the fresh `γ`), priced
  `(N−1)/|F|` by `gammaZero_prob_le` (REUSED); each sumcheck round's bad event
  is a false claim passing the Boolean check and the fresh challenge landing
  where the prover's degree-`≤ 1` message meets the honest round polynomial --
  at most one point, `card_agreeFinset_lt` (REUSED): `1/|F|`.  Then
  **`gateProof_fs_sound`** is `fsKeystone_proved.sound` at this instance: the
  non-interactive verifier `fiatShamir (gateReduction …)` is straightline
  knowledge sound in the lazily-sampled ROM with error `(t + (m+1)) · price`,
  `price = 0 + (N−1)/|F| + m·(1/|F|)` -- the `gateProof_sound` ledger, every
  term visible (`gateProof_fs_sound_reading` spells the event out).

**What is and is not consumed.**  The reduction consumes only `S.commit`; the
`BindingCommitment` premise is NAMED (the price theorems carry it) but at full
word its binding is not load-bearing -- the word is in the statement, so the
FS query hashes the word itself.  Binding becomes load-bearing exactly when
the word leaves the statement and only its root is hashed: that is the BCS
compilation the FS file names `[FS-BCS]` and this lane names
`[CT-merkle-profile]`.  The ROM is the tree's inhabited lazy-sampling handler
(`Oracle`, never an axiom); "the deployed cSHAKE realizes it" is `[FS-ROM]`,
the one named idealization, and the concrete oracle below is that function.
-/

import Compiler.CommittedTerminalController
import Selvage.FiatShamir

namespace Minidregg.Compiler.CommittedTerminalFiatShamir

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.CommittedTerminalRealizer Minidregg.Compiler.CommittedTerminalCompose
open Minidregg.Compiler.CommittedTerminalController
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

/-- The controller's lane transcript (disambiguated from `Selvage.Transcript`). -/
abbrev LaneTranscript := CommittedTerminalController.Transcript

variable {m : Nat}

/-! ## §1. The lane carrier is finite; `readExt6` is a bijection -/

/-- Six lanes are six `BabyBear`s. -/
def Ext6L.equivFn : Ext6L ≃ (Fin 6 → BabyBear) where
  toFun := Ext6L.toFn
  invFun := Ext6L.ofFn
  left_inv a := by cases a; rfl
  right_inv := Ext6L.toFn_ofFn

instance : Fintype Ext6L := Fintype.ofEquiv (Fin 6 → BabyBear) Ext6L.equivFn.symm

theorem card_ext6L : Fintype.card Ext6L = babyBearP ^ 6 := by
  rw [Fintype.card_congr Ext6L.equivFn, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Injective (`readExt6_injective`) between types of the same cardinality. -/
theorem readExt6_bijective : Function.Bijective readExt6 :=
  (Fintype.bijective_iff_injective_and_card readExt6).mpr
    ⟨readExt6_injective, by rw [card_ext6L, card_ext6]⟩

noncomputable def readEquiv : Ext6L ≃ Ext6Q := Equiv.ofBijective readExt6 readExt6_bijective

/-- Lane probabilities are field probabilities: `uniformProb` only counts. -/
theorem uniformProb_read (p : Ext6Q → Prop) :
    uniformProb Ext6L (fun a => p (readExt6 a)) = uniformProb Ext6Q p :=
  uniformProb_equiv readEquiv p

/-! ## §2. The controller's protocol as a `Reduction` -/

section Reduction

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool))

/-- The zeroth prover message: a `Reduction`'s prover moves first in every round, and the
gamma round has nothing to say. -/
def junkMsg : RoundMsg := (ext6Zero, ext6Zero)

/-- The challenge vector is `(γ, r₀, …, r_{m−1})`. -/
def gammaOf (ρs : Fin (m + 1) → Ext6L) : Ext6L := ρs 0

def roundsOf (ρs : Fin (m + 1) → Ext6L) : Fin m → Ext6L := fun i => ρs i.succ

/-- The messages after the junk zeroth one. -/
def messagesOf (πs : Fin (m + 1) → RoundMsg) : Fin m → RoundMsg := fun i => πs i.succ

/-- The lane transcript the controller decides. -/
def transcriptOf (πs : Fin (m + 1) → RoundMsg) (ρs : Fin (m + 1) → Ext6L) : LaneTranscript m :=
  ⟨messagesOf πs, roundsOf ρs⟩

/-- The opening of `y` at these challenges: the whole word and its RECOMPUTED terminal. -/
def openingOf (y : Fin n → BabyBear) (ρs : Fin (m + 1) → Ext6L) : Opening n :=
  ⟨y, laneTerminal (gammaOf ρs) (roundsOf ρs) encNat (descriptorResiduals d (traceOf y))⟩

/-- **The verifier**: `check` at the challenges, on the full word. -/
def gateVerify (rt : Root) (y : Fin n → BabyBear) (πs : Fin (m + 1) → RoundMsg)
    (ρs : Fin (m + 1) → Ext6L) : Option (Unit × (Fin 1 → Unit)) :=
  match check commit d encNat (gammaOf ρs) rt (openingOf d encNat y ρs) (transcriptOf πs ρs) with
  | .ok _ => some ((), fun _ => ())
  | .error _ => none

/-- The verifier accepts exactly when the word recommits, every round check passes, and the
chain closes at the recomputed terminal. -/
theorem gateVerify_some_iff (rt : Root) (y : Fin n → BabyBear) (πs : Fin (m + 1) → RoundMsg)
    (ρs : Fin (m + 1) → Ext6L) :
    gateVerify commit d encNat rt y πs ρs = some ((), fun _ => ()) ↔
      commit y = rt ∧ roundsOk (transcriptOf πs ρs) = true ∧
        laneChain (transcriptOf πs ρs) m =
          laneTerminal (gammaOf ρs) (roundsOf ρs) encNat (descriptorResiduals d (traceOf y)) := by
  unfold gateVerify
  constructor
  · intro h
    cases hch : check commit d encNat (gammaOf ρs) rt (openingOf d encNat y ρs)
        (transcriptOf πs ρs) with
    | ok rc =>
      obtain ⟨hv, hr, hc, -, -, -⟩ := check_ok_spec commit d encNat _ _ _ _ rc hch
      obtain ⟨hrt, -, hval⟩ := (realize_ok_iff commit d encNat _ _ _ _ _).mp hv
      exact ⟨hrt, hr, by rw [hc, hval]; rfl⟩
    | error e =>
      rw [hch] at h
      exact absurd h (by simp)
  · rintro ⟨hrt, hr, hc⟩
    have hv : realize commit d encNat (gammaOf ρs) (transcriptOf πs ρs).challenge rt
        (openingOf d encNat y ρs) = .ok (openingOf d encNat y ρs).value :=
      (realize_ok_iff commit d encNat _ _ _ _ _).mpr ⟨hrt, rfl, rfl⟩
    rw [check_ok_of commit d encNat _ _ _ _ _ hv hr hc]

/-- Any accepting output is the one accepting output. -/
theorem gateVerify_exists_iff (rt : Root) (y : Fin n → BabyBear) (πs : Fin (m + 1) → RoundMsg)
    (ρs : Fin (m + 1) → Ext6L) :
    (∃ x' y', gateVerify commit d encNat rt y πs ρs = some (x', y')) ↔
      gateVerify commit d encNat rt y πs ρs = some ((), fun _ => ()) := by
  constructor
  · rintro ⟨x', y', h⟩
    rw [h]
  · intro h
    exact ⟨_, _, h⟩

/-- **The gate proof as a `Reduction`** (Selvage/Rbr.lean).  Index `Unit`; explicit instance the
root; implicit instance the WORD (full-word resolution: the verifier reads it); target
relation `True` (nothing is handed on); witness `Unit` (knowledge soundness = soundness);
`k = m + 1` rounds over the lane alphabets; `δ* = 1/n` so the relaxation is exact. -/
noncomputable def gateReduction (hn : 0 < n) : Reduction where
  Idx := Unit
  X := Root
  A := BabyBear
  X' := Unit
  A' := Unit
  W := Unit
  n := n
  n' := 1
  n_pos := hn
  n'_pos := one_pos
  R := fun _ rt y _ => commit y = rt ∧ descriptorHolds d (traceOf y)
  R' := fun _ _ _ _ => True
  k := m + 1
  k_pos := Nat.succ_pos m
  PMsg := RoundMsg
  Chal := Ext6L
  pmsgNonempty := ⟨junkMsg⟩
  chalFintype := inferInstance
  chalNonempty := ⟨ext6Zero⟩
  δstar := 1 / (n : ℝ)
  δstar_pos := one_div_pos.mpr (Nat.cast_pos.mpr hn)
  δstar_le_one := by
    rw [div_le_one (Nat.cast_pos.mpr hn)]
    exact Nat.one_le_cast.mpr hn
  verify := fun _ rt y πs ρs => gateVerify commit d encNat rt y πs ρs

/-- Below `1/n` fractional Hamming distance is exact equality. -/
theorem eq_of_fracHamming_lt {A : Type} {n : Nat} (hn : 0 < n) (u v : Fin n → A)
    (h : fracHamming u v < 1 / (n : ℝ)) : u = v := by
  unfold fracHamming at h
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_lt_div_iff_of_pos_right hnpos] at h
  have hcard : Nat.card {i : Fin n // u i ≠ v i} < 1 := by exact_mod_cast h
  have hzero : Nat.card {i : Fin n // u i ≠ v i} = 0 := by omega
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff] at hzero
  funext i
  by_contra hne
  exact hzero.false ⟨i, hne⟩

omit [DecidableEq Root] in
/-- **The relaxation is exact at `δ < 1/n`**: `R_{≤δ}` is `R`. -/
theorem relaxedMem_iff {A W : Type} {n : Nat} (hn : 0 < n)
    (R : Unit → Root → (Fin n → A) → W → Prop) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ))) (rt : Root) (y : Fin n → A) (w : W) :
    RelaxedMem R δ () rt y w ↔ R () rt y w := by
  constructor
  · rintro ⟨ystar, hR, hd⟩
    rw [eq_of_fracHamming_lt hn y ystar (lt_of_le_of_lt hd hδ.2)]
    exact hR
  · intro hR
    exact ⟨y, hR, by rw [fracHamming_self]; exact le_of_lt hδ.1⟩

/-! ## §3. The knowledge state function (Def 4.1) -/

/-- The completed sumcheck rounds after the gamma round, read as a lane transcript (junk past
the depth, never consulted below it). -/
def trOfRounds (rest : List (RoundMsg × Ext6L)) : LaneTranscript m :=
  ⟨fun i => (rest.getD i (junkMsg, ext6Zero)).1, fun i => (rest.getD i (junkMsg, ext6Zero)).2⟩

/-- Every Boolean check strictly below depth `i`. -/
def roundsOkBelow (tr : LaneTranscript m) (i : Nat) : Prop :=
  ∀ j : Fin m, j.val < i → ext6Add (tr.message j).1 (tr.message j).2 = laneChain tr j

variable (encFor : ∀ wv : Nat → BabyBear, Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))

/-- The honest level-`i` residual claim of the gamma table at the transcript's challenges:
`Σ_{b ∈ {0,1}^{m−i}} f̂(r₀,…,r_{i−1}, b)` (`residualSum`, REUSED). -/
noncomputable def honestClaim (y : Fin n → BabyBear) (gamma : Ext6L) (tr : LaneTranscript m)
    (i : Nat) : Ext6Q :=
  residualSum (mle (gammaResidualTable d (traceOf y) (encFor (traceOf y)) (readExt6 gamma)))
    (fun q => readExt6 (tr.challenge q)) i

/-- **The knowledge state on completed rounds.**  Empty: the trace satisfies the descriptor.
After `(π₀, γ)` and `i` sumcheck rounds: every Boolean check so far, and the running claim
is the honest level-`i` residual claim. -/
def StageOk (y : Fin n → BabyBear) : List (RoundMsg × Ext6L) → Prop
  | [] => descriptorHolds d (traceOf y)
  | (_, gamma) :: rest =>
      roundsOkBelow (trOfRounds (m := m) rest) rest.length ∧
        readExt6 (laneChain (trOfRounds (m := m) rest) rest.length) =
          honestClaim d encFor y gamma (trOfRounds (m := m) rest) rest.length

theorem getD_ofFn {α : Type} (f : Fin m → α) (i : Fin m) (dflt : α) :
    (List.ofFn f).getD i.val dflt = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem trOfRounds_ofFn (msg : Fin m → RoundMsg) (ch : Fin m → Ext6L) :
    trOfRounds (List.ofFn fun i => (msg i, ch i)) = ⟨msg, ch⟩ := by
  unfold trOfRounds
  congr 1 <;> funext i <;> rw [getD_ofFn]

theorem roundsOkBelow_full (tr : LaneTranscript m) :
    roundsOkBelow tr m ↔ roundsOk tr = true := by
  rw [roundsOk_iff]
  exact ⟨fun h i => h i i.isLt, fun h i _ => h i⟩

theorem residualSum_mle_zero (f : (Fin m → Bool) → Ext6Q) (x : Fin m → Ext6Q) :
    residualSum (mle f) x 0 = ∑ b, f b := by
  have h := scChain_mleHonest_partial f (chalOf x) (Nat.zero_le m)
  rw [chalOf_restrict] at h
  exact h.symm

/-- At the full depth the honest claim is the recomputed terminal, read. -/
theorem honestClaim_full (hEnc : ∀ wv k, encFor wv k = encNat k) (y : Fin n → BabyBear)
    (gamma : Ext6L) (tr : LaneTranscript m) :
    honestClaim d encFor y gamma tr m =
      readExt6 (laneTerminal gamma tr.challenge encNat (descriptorResiduals d (traceOf y))) := by
  rw [honestClaim, residualSum_full,
    read_laneTerminal d (traceOf y) (encFor (traceOf y)) encNat (hEnc (traceOf y)) gamma tr.challenge]

/-- The knowledge state at a full transcript, in the controller's vocabulary. -/
theorem stageOk_ofFull (y : Fin n → BabyBear) (πs : Fin (m + 1) → RoundMsg)
    (ρs : Fin (m + 1) → Ext6L) :
    StageOk d encFor y (Selvage.Transcript.ofFull πs ρs).rounds ↔
      roundsOkBelow (transcriptOf πs ρs) m ∧
        readExt6 (laneChain (transcriptOf πs ρs) m) =
          honestClaim d encFor y (gammaOf ρs) (transcriptOf πs ρs) m := by
  simp only [Selvage.Transcript.ofFull, List.ofFn_succ, StageOk, List.length_ofFn, trOfRounds_ofFn]
  exact Iff.rfl

open Classical in
/-- **The knowledge state function** of the gate reduction: the root recommits and `StageOk`
holds at the completed rounds; the pending prover message is ignored (so prover moves are
trivially monotone). -/
noncomputable def gateKState (hEnc : ∀ wv k, encFor wv k = encNat k) (hn : 0 < n) :
    KStateFn (gateReduction commit d encNat hn) where
  state := fun _ st tr _ => decide (commit st.y = st.x ∧ StageOk d encFor st.y tr.rounds)
  empty_iff := by
    intro δ hδ st w
    rw [decide_eq_true_iff]
    exact (relaxedMem_iff hn (gateReduction commit d encNat hn).R hδ st.x st.y w).symm
  prover_monotone := by
    intro δ hδ st rs w _ h π
    exact h
  full_iff := by
    intro δ hδ st πs ρs w
    rw [decide_eq_true_iff]
    refine Iff.trans (and_congr_right fun _ => stageOk_ofFull d encFor st.y πs ρs) ?_
    have hfull : ∀ (x' : Unit) (y' : Fin 1 → Unit),
        RelaxedMem (gateReduction commit d encNat hn).R' δ () x' y' w :=
      fun x' y' => ⟨y', trivial, by rw [fracHamming_self]; exact le_of_lt hδ.1⟩
    constructor
    · rintro ⟨hrt, hok, hclaim⟩
      refine ⟨(), fun _ => (), ?_, hfull _ _⟩
      show gateVerify commit d encNat st.x st.y πs ρs = some ((), fun _ => ())
      rw [gateVerify_some_iff]
      refine ⟨hrt, (roundsOkBelow_full _).mp hok, ?_⟩
      apply lane_eq_of_read
      rw [hclaim, honestClaim_full d encNat encFor hEnc]
      rfl
    · rintro ⟨x', y', hv, -⟩
      have hv' : gateVerify commit d encNat st.x st.y πs ρs = some ((), fun _ => ()) :=
        (gateVerify_exists_iff commit d encNat st.x st.y πs ρs).mp ⟨x', y', hv⟩
      obtain ⟨hrt, hok, hclose⟩ := (gateVerify_some_iff commit d encNat st.x st.y πs ρs).mp hv'
      refine ⟨hrt, (roundsOkBelow_full _).mpr hok, ?_⟩
      rw [honestClaim_full d encNat encFor hEnc, hclose]
      rfl

/-! ## §4. Relaxed round-by-round knowledge soundness (Def 4.2) -/

/-- **The gamma round's bad event is the gamma event**: a failing trace whose batched residual
vanishes at the fresh `γ` -- `≤ (N−1)/|F|` (`gammaZero_prob_le`, REUSED). -/
theorem stage_bad_zero (y : Fin n → BabyBear) (π : RoundMsg) :
    uniformProb Ext6L (fun ρ => ¬ StageOk d encFor y [] ∧ StageOk d encFor y [(π, ρ)]) ≤
      ((d.gates.length + d.zeros.length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q := by
  by_cases hd : descriptorHolds d (traceOf y)
  · rw [uniformProb_false (fun ρ h => h.1 hd)]
    positivity
  · have hmono : ∀ ρ, (¬ StageOk d encFor y [] ∧ StageOk d encFor y [(π, ρ)]) →
        (∑ b, gammaResidualTable d (traceOf y) (encFor (traceOf y)) (readExt6 ρ) b) = 0 := by
      rintro ρ ⟨-, -, hclaim⟩
      simp only [List.length_nil] at hclaim
      rw [honestClaim, residualSum_mle_zero] at hclaim
      rw [← hclaim]
      show readExt6 ext6Zero = 0
      exact read_zero
    refine le_trans (uniformProb_mono hmono) ?_
    rw [uniformProb_read (fun γ =>
      (∑ b, gammaResidualTable d (traceOf y) (encFor (traceOf y)) γ b) = 0)]
    have h := gammaZero_prob_le d (traceOf y) (encFor (traceOf y)) hd
    rw [descriptorResiduals_length] at h
    exact h

theorem trOfRounds_message_lt (rest tail : List (RoundMsg × Ext6L)) (i : Fin m)
    (hi : i.val < rest.length) :
    (trOfRounds (m := m) (rest ++ tail)).message i = (trOfRounds (m := m) rest).message i := by
  simp only [trOfRounds, List.getD_append _ _ _ _ hi]

theorem trOfRounds_challenge_lt (rest tail : List (RoundMsg × Ext6L)) (i : Fin m)
    (hi : i.val < rest.length) :
    (trOfRounds (m := m) (rest ++ tail)).challenge i = (trOfRounds (m := m) rest).challenge i := by
  simp only [trOfRounds, List.getD_append _ _ _ _ hi]

theorem trOfRounds_message_last (rest : List (RoundMsg × Ext6L)) (π : RoundMsg) (ρ : Ext6L)
    (i : Fin m) (hi : i.val = rest.length) :
    (trOfRounds (m := m) (rest ++ [(π, ρ)])).message i = π := by
  simp only [trOfRounds, hi, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem trOfRounds_challenge_last (rest : List (RoundMsg × Ext6L)) (π : RoundMsg) (ρ : Ext6L)
    (i : Fin m) (hi : i.val = rest.length) :
    (trOfRounds (m := m) (rest ++ [(π, ρ)])).challenge i = ρ := by
  simp only [trOfRounds, hi, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem trOfRounds_challenge_junk (rest : List (RoundMsg × Ext6L)) (i : Fin m)
    (hi : rest.length ≤ i.val) :
    (trOfRounds (m := m) rest).challenge i = ext6Zero := by
  simp only [trOfRounds, List.getD_eq_default _ _ hi]

/-- The lane chain below the depth reads only the rounds below it. -/
theorem laneChain_append_le (rest tail : List (RoundMsg × Ext6L)) (i : Nat)
    (hi : i ≤ rest.length) (hm : i ≤ m) :
    laneChain (trOfRounds (m := m) (rest ++ tail)) i = laneChain (trOfRounds (m := m) rest) i := by
  cases i with
  | zero => rfl
  | succ i =>
    have him : i < m := by omega
    show laneEval (messageAt _ i) (challengeAt _ i) = laneEval (messageAt _ i) (challengeAt _ i)
    rw [messageAt_of_lt _ him, messageAt_of_lt _ him, challengeAt, dif_pos him, challengeAt,
      dif_pos him, trOfRounds_message_lt _ _ ⟨i, him⟩ (by simp; omega),
      trOfRounds_challenge_lt _ _ ⟨i, him⟩ (by simp; omega)]

theorem roundsOkBelow_append_succ (rest : List (RoundMsg × Ext6L)) (π : RoundMsg) (ρ : Ext6L)
    (hlen : rest.length < m)
    (h : roundsOkBelow (trOfRounds (m := m) (rest ++ [(π, ρ)])) (rest.length + 1)) :
    roundsOkBelow (trOfRounds (m := m) rest) rest.length ∧
      ext6Add π.1 π.2 = laneChain (trOfRounds (m := m) rest) rest.length := by
  constructor
  · intro j hj
    have hj' := h j (Nat.lt_succ_of_lt hj)
    rw [trOfRounds_message_lt _ _ j hj, laneChain_append_le _ _ _ (le_of_lt hj) (le_of_lt j.isLt)]
      at hj'
    exact hj'
  · have hj' := h ⟨rest.length, hlen⟩ (Nat.lt_succ_self _)
    rw [trOfRounds_message_last _ _ _ _ rfl,
      laneChain_append_le _ _ _ (le_refl _) (le_of_lt hlen)] at hj'
    exact hj'

/-- The level-`k` residual reads the challenges only below `k`. -/
theorem residualSum_congr (g : (Fin m → Ext6Q) → Ext6Q) (x x' : Fin m → Ext6Q) (k : Nat)
    (h : ∀ j : Fin m, j.val < k → x j = x' j) :
    residualSum g x k = residualSum g x' k := by
  unfold residualSum
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext j
  simp only [glue_apply]
  split_ifs with hj
  · rfl
  · exact h j (Nat.lt_of_not_le hj)

/-- The challenges of the extended transcript are the old ones updated at the depth. -/
theorem read_challenge_append (rest : List (RoundMsg × Ext6L)) (π : RoundMsg) (ρ : Ext6L)
    (hlen : rest.length < m) :
    (fun q => readExt6 ((trOfRounds (m := m) (rest ++ [(π, ρ)])).challenge q)) =
      Function.update (fun q => readExt6 ((trOfRounds (m := m) rest).challenge q))
        ⟨rest.length, hlen⟩ (readExt6 ρ) := by
  funext q
  rcases lt_trichotomy q.val rest.length with hq | hq | hq
  · rw [Function.update_of_ne (fun h => by rw [h] at hq; exact lt_irrefl _ hq),
      trOfRounds_challenge_lt _ _ q hq]
  · have hq' : q = ⟨rest.length, hlen⟩ := Fin.ext hq
    rw [hq', Function.update_self, trOfRounds_challenge_last _ _ _ _ rfl]
  · rw [Function.update_of_ne (fun h => by rw [h] at hq; exact lt_irrefl _ hq),
      trOfRounds_challenge_junk _ q (by simp; omega),
      trOfRounds_challenge_junk _ q (le_of_lt hq)]

/-- The honest round-`j` polynomial of the gamma table at the transcript's challenges
(`roundPoly`, REUSED): degree `≤ 1`, evaluating to the round partial sum. -/
noncomputable def honestRound (y : Fin n → BabyBear) (gamma : Ext6L) (tr : LaneTranscript m)
    (j : Fin m) : Polynomial Ext6Q :=
  roundPoly (mle (gammaResidualTable d (traceOf y) (encFor (traceOf y)) (readExt6 gamma)))
    (fun q => readExt6 (tr.challenge q)) j

theorem honestRound_degree (y : Fin n → BabyBear) (gamma : Ext6L) (tr : LaneTranscript m)
    (j : Fin m) : (honestRound d encFor y gamma tr j).degree < ((1 + 1 : ℕ) : WithBot ℕ) :=
  roundPoly_degree _ _ _

theorem honestRound_eval (y : Fin n → BabyBear) (gamma : Ext6L) (tr : LaneTranscript m)
    (j : Fin m) (t : Ext6Q) :
    (honestRound d encFor y gamma tr j).eval t =
      roundSum (mle (gammaResidualTable d (traceOf y) (encFor (traceOf y)) (readExt6 gamma)))
        (fun q => readExt6 (tr.challenge q)) j t :=
  roundPoly_eval (mle_multilinear _ _) _ _

/-- The honest level-`j` claim is the honest round-`j` polynomial's Boolean sum. -/
theorem honestClaim_eq_boolean_sum (y : Fin n → BabyBear) (gamma : Ext6L) (tr : LaneTranscript m)
    {j : Nat} (hj : j < m) :
    honestClaim d encFor y gamma tr j =
      (honestRound d encFor y gamma tr ⟨j, hj⟩).eval 0 +
        (honestRound d encFor y gamma tr ⟨j, hj⟩).eval 1 := by
  rw [honestRound_eval, honestRound_eval, honestClaim, residualSum_eq_roundSum_bool hj]

/-- The honest level-`(j+1)` claim after the fresh challenge is the honest round-`j` polynomial
at that challenge. -/
theorem honestClaim_succ (y : Fin n → BabyBear) (gamma : Ext6L) (rest : List (RoundMsg × Ext6L))
    (hlen : rest.length < m) (π : RoundMsg) (ρ : Ext6L) :
    honestClaim d encFor y gamma (trOfRounds (m := m) (rest ++ [(π, ρ)])) (rest.length + 1) =
      (honestRound d encFor y gamma (trOfRounds (m := m) rest) ⟨rest.length, hlen⟩).eval
        (readExt6 ρ) := by
  rw [honestRound_eval, roundSum_eq_residualSum_update, honestClaim, read_challenge_append rest π ρ hlen]

/-- The lane chain after the fresh challenge is the pending message at that challenge. -/
theorem laneChain_append_succ (rest : List (RoundMsg × Ext6L)) (hlen : rest.length < m)
    (π : RoundMsg) (ρ : Ext6L) :
    readExt6 (laneChain (trOfRounds (m := m) (rest ++ [(π, ρ)])) (rest.length + 1)) =
      (readPoly1 π).eval (readExt6 ρ) := by
  show readExt6 (laneEval (messageAt _ rest.length) (challengeAt _ rest.length)) = _
  rw [messageAt_of_lt _ hlen, challengeAt, dif_pos hlen,
    trOfRounds_message_last _ _ _ ⟨rest.length, hlen⟩ rfl,
    trOfRounds_challenge_last _ _ _ ⟨rest.length, hlen⟩ rfl, readPoly1_eval]

open Classical in
/-- **A sumcheck round's bad event is one root**: the running claim is false, the pending
message passes the Boolean check, and the fresh challenge lands where the prover's degree-`≤ 1`
message meets the honest round polynomial -- at most one point (`card_agreeFinset_lt`, REUSED):
`≤ 1/|F|`. -/
theorem stage_bad_succ (y : Fin n → BabyBear) (π₀ : RoundMsg) (gamma : Ext6L)
    (rest : List (RoundMsg × Ext6L)) (hlen : rest.length < m) (π : RoundMsg) :
    uniformProb Ext6L (fun ρ => ¬ StageOk d encFor y ((π₀, gamma) :: rest) ∧
        StageOk d encFor y ((π₀, gamma) :: rest ++ [(π, ρ)])) ≤
      1 / Fintype.card Ext6Q := by
  have hmono : ∀ ρ, (¬ StageOk d encFor y ((π₀, gamma) :: rest) ∧
      StageOk d encFor y ((π₀, gamma) :: rest ++ [(π, ρ)])) →
      readPoly1 π ≠ honestRound d encFor y gamma (trOfRounds (m := m) rest) ⟨rest.length, hlen⟩ ∧
        readExt6 ρ ∈ agreeFinset (readPoly1 π)
          (honestRound d encFor y gamma (trOfRounds (m := m) rest) ⟨rest.length, hlen⟩) := by
    rintro ρ ⟨hnot, hst⟩
    simp only [List.cons_append, StageOk, List.length_append, List.length_singleton] at hst
    obtain ⟨hok', hclaim'⟩ := hst
    obtain ⟨hok, hbool⟩ := roundsOkBelow_append_succ rest π ρ hlen hok'
    have hclaim : readExt6 (laneChain (trOfRounds (m := m) rest) rest.length) ≠
        honestClaim d encFor y gamma (trOfRounds (m := m) rest) rest.length :=
      fun heq => hnot ⟨hok, heq⟩
    refine ⟨?_, ?_⟩
    · intro heq
      apply hclaim
      rw [honestClaim_eq_boolean_sum d encFor y gamma _ hlen, ← heq, readPoly1_eval_zero,
        readPoly1_eval_one, ← read_add, hbool]
    · rw [mem_agreeFinset, ← laneChain_append_succ rest hlen π ρ, hclaim',
        honestClaim_succ d encFor y gamma rest hlen π ρ]
  refine le_trans (uniformProb_mono hmono) ?_
  by_cases hne : readPoly1 π = honestRound d encFor y gamma (trOfRounds (m := m) rest)
      ⟨rest.length, hlen⟩
  · rw [uniformProb_false (fun ρ h => h.1 hne)]
    positivity
  · refine le_trans (uniformProb_mono (fun ρ h => h.2)) ?_
    rw [uniformProb_read (fun t => t ∈ agreeFinset (readPoly1 π) _), uniformProb_mem_finset]
    have hcard := card_agreeFinset_lt (readPoly1_degree π) (honestRound_degree d encFor y gamma _ _) hne
    have hcard' : ((agreeFinset (readPoly1 π) (honestRound d encFor y gamma
        (trOfRounds (m := m) rest) ⟨rest.length, hlen⟩)).card : ℝ) ≤ 1 := by
      exact_mod_cast (by omega : (agreeFinset (readPoly1 π) (honestRound d encFor y gamma
        (trOfRounds (m := m) rest) ⟨rest.length, hlen⟩)).card ≤ 1)
    have hpos : (0 : ℝ) ≤ Fintype.card Ext6Q := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_right hcard' hpos

/-- Per-round knowledge errors: the gamma round pays `(N−1)/|F|`, every sumcheck round `1/|F|`. -/
noncomputable def gateErr (i : Fin (m + 1)) : ℝ :=
  if i.val = 0 then ((d.gates.length + d.zeros.length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q
  else 1 / Fintype.card Ext6Q

open Classical in
/-- **[CT-fiat-shamir-lanes] the RBR instance** (Def 4.2) of the gate reduction: the identity
round extractor (`W = Unit`), the state function above, and the per-round errors discharged by
`stage_bad_zero` and `stage_bad_succ`. -/
noncomputable def gateRbr (hEnc : ∀ wv k, encFor wv k = encNat k) (hn : 0 < n) :
    RbrKnowledgeSoundness (gateReduction commit d encNat hn) where
  kstate := gateKState commit d encNat encFor hEnc hn
  extract := fun _ _ w => w
  err := fun i _ _ => gateErr d i
  extractTime := fun _ => 0
  extract_sound := by
    intro δ hδ st i rs hlen π
    have hmono : ∀ ρ : (gateReduction commit d encNat hn).Chal, (∃ w : Unit,
        (gateKState commit d encNat encFor hEnc hn).state δ st ⟨rs, some π⟩ w = false ∧
        (gateKState commit d encNat encFor hEnc hn).state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true) →
        ¬ StageOk d encFor st.y rs ∧ StageOk d encFor st.y (rs ++ [(π, ρ)]) := by
      rintro ρ ⟨w, h1, h2⟩
      have h1' : decide (commit st.y = st.x ∧ StageOk d encFor st.y rs) = false := h1
      have h2' : decide (commit st.y = st.x ∧ StageOk d encFor st.y (rs ++ [(π, ρ)])) = true := h2
      rw [decide_eq_false_iff_not] at h1'
      rw [decide_eq_true_iff] at h2'
      exact ⟨fun h => h1' ⟨h2'.1, h⟩, h2'.2⟩
    refine le_trans (uniformProb_mono hmono) ?_
    cases rs with
    | nil =>
      have hi : i.val = 0 := by simpa using hlen.symm
      simp only [gateErr, hi, if_true]
      exact stage_bad_zero d encFor st.y π
    | cons hd rest =>
      obtain ⟨π₀, gamma⟩ := hd
      have hi : i.val = rest.length + 1 := by simpa using hlen.symm
      have hrest : rest.length < m := by
        have hk : (gateReduction commit d encNat hn).k = m + 1 := rfl
        have := i.isLt
        omega
      simp only [gateErr, hi, Nat.succ_ne_zero, if_false]
      exact stage_bad_succ d encFor st.y π₀ gamma rest hrest π

/-! ## §5. The keystone, instantiated -/

/-- **The full-word price, every term visible**: terminal `0` (under the named commitment),
the gamma event `(N−1)/|F|`, the sumcheck `m·(1/|F|)`. -/
noncomputable def gatePrice (d : ConstraintDescriptor BabyBear) (m : Nat) : ℝ :=
  0 + ((d.gates.length + d.zeros.length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q +
    (m : ℝ) * (1 / Fintype.card Ext6Q)

theorem gatePrice_nonneg : 0 ≤ gatePrice d m := by
  unfold gatePrice
  positivity

theorem gateErr_le_gatePrice (i : Fin (m + 1)) : gateErr d i ≤ gatePrice d m := by
  unfold gateErr gatePrice
  have hc : (0 : ℝ) ≤ 1 / Fintype.card Ext6Q := by positivity
  have hg : (0 : ℝ) ≤ ((d.gates.length + d.zeros.length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q := by
    positivity
  split_ifs with h
  · have : (0 : ℝ) ≤ (m : ℝ) * (1 / Fintype.card Ext6Q) := by positivity
    linarith
  · have hm : (1 : ℝ) ≤ m := by
      have := i.isLt
      have : 1 ≤ i.val := Nat.pos_of_ne_zero h
      exact_mod_cast (by omega : 1 ≤ m)
    have := mul_le_mul_of_nonneg_right hm hc
    linarith

/-- **[CT-fiat-shamir-lanes] `gateProof_fs_sound`** -- `fsKeystone_proved.sound`
(Selvage/FiatShamir.lean, the FS-of-RBR keystone, proved unconditionally) at the gate reduction
and its RBR instance: the non-interactive verifier `fiatShamir (gateReduction …)` is straightline
knowledge sound in the lazily-sampled ROM for EVERY statement (`Z = univ`), with error
`(t + (m+1)) · (0 + (N−1)/|F| + m·(1/|F|))` against a `t`-query adversary -- the
`gateProof_sound` ledger under the keystone's `(t + k)` factor, `k = m + 1` rounds. -/
theorem gateProof_fs_sound (hEnc : ∀ wv k, encFor wv k = encNat k) (hn : 0 < n) :
    FsStraightlineKnowledgeSoundness (gateReduction commit d encNat hn) Set.univ
      (fun _s t _δ => ((t : ℝ) + ((m + 1 : ℕ) : ℝ)) * gatePrice d m) :=
  fsKeystone_proved.sound (gateReduction commit d encNat hn) (gateRbr commit d encNat encFor hEnc hn)
    Set.univ (fun _ => gatePrice d m) (fun _ _ => gatePrice_nonneg d)
    (fun i _ _ _ _ => gateErr_le_gatePrice d i)

/-- **What `gateProof_fs_sound` says, spelled out** (`W = Unit`, `R' = True`, `Z = univ`, the
relaxation exact below `1/n`): for every salt size `s`, query budget `t`, `δ ∈ (0, 1/n)`, and
deterministic `t`-query ROM adversary `P` (an `SrProver`: its oracle queries are salted transcript
prefixes), the probability over the lazily-sampled coins that `P` outputs a proof string whose
statement is FALSE -- the word does not recommit to the root, or does not satisfy the
descriptor -- and the FS verifier at the derived challenges ACCEPTS it, is at most
`(t + (m+1)) · price`. -/
theorem gateProof_fs_sound_reading (hEnc : ∀ wv k, encFor wv k = encNat k) (hn : 0 < n)
    (s t : ℕ) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (P : SrProver (gateReduction commit d encNat hn) s) :
    uniformProb ((Fin t → (gateReduction commit d encNat hn).Chal) ×
        (Fin (gateReduction commit d encNat hn).k → (gateReduction commit d encNat hn).Chal))
      (fun coins =>
        let o := P.out ((srTrace P coins.1).map Prod.snd)
        ¬ (commit o.stmt.y = o.stmt.x ∧ descriptorHolds d (traceOf o.stmt.y)) ∧
          fiatShamir (gateReduction commit d encNat hn) s
            (fsOracle o (srFinalChal P coins.1 coins.2)) o ≠ none) ≤
      ((t : ℝ) + ((m + 1 : ℕ) : ℝ)) * gatePrice d m := by
  obtain ⟨E, hE⟩ := gateProof_fs_sound commit d encNat encFor hEnc hn
  refine le_trans (le_of_eq (uniformProb_congr fun coins => ?_)) (hE s t δ hδ P)
  dsimp only
  constructor
  · rintro ⟨hfalse, hacc⟩
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hacc
    refine ⟨Set.mem_univ _, ?_, v.1, v.2, hv, ?_⟩
    · intro hrel
      exact hfalse ((relaxedMem_iff hn (gateReduction commit d encNat hn).R hδ _ _ _).mp hrel)
    · exact ⟨v.2, trivial, by rw [fracHamming_self]; exact le_of_lt hδ.1⟩
  · rintro ⟨-, hrel, x', y', hv, -⟩
    refine ⟨?_, ?_⟩
    · intro hR
      exact hrel ((relaxedMem_iff hn (gateReduction commit d encNat hn).R hδ _ _ _).mpr hR)
    · rw [hv]
      exact Option.some_ne_none _

end Reduction

/-! ## §6. [CT-joint-price]: one number over `(γ, r)` -/

section Joint

variable (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
variable (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))

/-- An event of the first coordinate has the marginal's probability (`uniformProb_prod_le` after
`Equiv.prodComm`). -/
theorem uniformProb_fst_le {A B : Type} [Fintype A] [Fintype B] (p : A → Prop) {ε : ℝ}
    (hε : 0 ≤ ε) (h : uniformProb A p ≤ ε) :
    uniformProb (A × B) (fun c => p c.1) ≤ ε := by
  rw [← uniformProb_equiv (Equiv.prodComm B A) (fun c : A × B => p c.1)]
  exact uniformProb_prod_le hε (fun _ => h)

/-- **[CT-joint-price] the interactive ledger as ONE number over `(γ, r)`**: for a failing trace
and any family of strategies (round messages may depend on `γ` and the challenge prefix), the
gamma event or the sumcheck event happens with probability at most `(N−1)/|F| + m·(1/|F|)` --
`gammaZero_prob_le` on the first coordinate, `sumcheck_prob_le` on every fibre over `γ`, and the
union bound (`uniformProb_or_le`, `uniformProb_prod_le`, REUSED). -/
theorem gateProof_joint_price (hfail : ¬ descriptorHolds d wv)
    (P : Ext6Q → (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : ∀ γ, PrefixMeasurable (P γ))
    (hdeg : ∀ (γ : Ext6Q) (χ : ℕ → Ext6Q) (i : ℕ), i < m →
      (P γ χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Ext6Q × (Fin m → Ext6Q)) (fun c =>
        (∑ b, gammaResidualTable d wv enc c.1 b) = 0 ∨
          AdaptiveAcceptsFalse (P c.1) (mleHonest (gammaResidualTable d wv enc c.1)) 0
            (∑ b, gammaResidualTable d wv enc c.1 b) c.2) ≤
      (((descriptorResiduals d wv).length - 1 : ℕ) : ℝ) / Fintype.card Ext6Q +
        (m : ℝ) * (1 / Fintype.card Ext6Q) := by
  refine le_trans (uniformProb_or_le _ _) (add_le_add ?_ ?_)
  · exact uniformProb_fst_le (fun γ : Ext6Q => (∑ b, gammaResidualTable d wv enc γ b) = 0)
      (by positivity) (gammaZero_prob_le d wv enc hfail)
  · have hfib : ∀ γ : Ext6Q, uniformProb (Fin m → Ext6Q) (fun r =>
        AdaptiveAcceptsFalse (P γ) (mleHonest (gammaResidualTable d wv enc γ)) 0
          (∑ b, gammaResidualTable d wv enc γ b) r) ≤ (m : ℝ) * (1 / Fintype.card Ext6Q) :=
      fun γ => sumcheck_prob_le (gammaResidualTable d wv enc γ) (P γ) (hpm γ) (hdeg γ)
    exact uniformProb_prod_le (p := fun c : Ext6Q × (Fin m → Ext6Q) =>
        AdaptiveAcceptsFalse (P c.1) (mleHonest (gammaResidualTable d wv enc c.1)) 0
          (∑ b, gammaResidualTable d wv enc c.1 b) c.2)
      (by positivity) hfib

end Joint

/-! ## §7. Stage 0: `stage0Receipt_price` -/

namespace Stage0

open CommittedTerminalRealizer.Stage0Exhibit
open Minidregg.Compiler.EvmAddAir

/-- `N = 3,298 + 850 = 4,148` residuals (`evmAddDescriptor_shape`, kernel-decided upstream). -/
theorem residual_count :
    evmAddDescriptor.gates.length + evmAddDescriptor.zeros.length = 4148 := by
  rw [evmAddDescriptor_shape.1, evmAddDescriptor_shape.2.2]

/-- The Stage-0 price with the field size written out: `p = 2^31 − 2^27 + 1`, `|F| = p^6`. -/
theorem gatePrice_stage0 :
    gatePrice evmAddDescriptor 13 =
      (0 : ℝ) + ((4148 - 1 : ℕ) : ℝ) / ((2013265921 : ℝ) ^ 6) +
        (13 : ℝ) * (1 / ((2013265921 : ℝ) ^ 6)) := by
  rw [gatePrice, residual_count, card_ext6]
  norm_num [babyBearP]

/-- **[CT-joint-price] `stage0Receipt_price`** -- the non-interactive Stage-0 receipt's error as
ONE expression with every term visible, under the named premise `S : BindingCommitment`
(only `S.commit` is consumed at full word; see the module header):
`(t + 14) · (0 + 4147/p^6 + 13·(1/p^6))` -- the FS factor `(t + k)` for a `t`-query adversary
and `k = 13 + 1` rounds (`fsKeystone_proved`), the terminal `0`, the gamma event
`(N − 1)/|F|` at `N = 4,148`, the sumcheck `m/|F|` at `m = 13` (sharp, degree one), `|F| = p^6`
for `Ext6`.  **This is the FULL-WORD price**: the verifier reads the whole 4,131-wire word;
`[CT-sampled]` (a sampled realizer and its list-decoding seam) and `[CT-merkle-profile]` (a
short root under `[COMMIT-CR]`, the word leaving the hashed statement) are NOT in it.  The ROM
is the tree's lazy-sampling handler; the deployed cSHAKE realizing it is `[FS-ROM]`. -/
theorem stage0Receipt_price {Root Op : Type} [DecidableEq Root]
    (S : BindingCommitment Root BabyBear (Fin 4131) Op) :
    FsStraightlineKnowledgeSoundness
      (gateReduction S.commit evmAddDescriptor (bitCorner 13) (by norm_num)) Set.univ
      (fun _s t _δ => ((t : ℝ) + (13 + 1 : ℝ)) *
        ((0 : ℝ) + ((4148 - 1 : ℕ) : ℝ) / ((2013265921 : ℝ) ^ 6) +
          (13 : ℝ) * (1 / ((2013265921 : ℝ) ^ 6)))) := by
  have h := gateProof_fs_sound S.commit evmAddDescriptor (bitCorner 13)
    (fun wv => residualEmbedding evmAddDescriptor wv stage0_residuals_fit) (fun _ _ => rfl)
    (by norm_num)
  have hfun : (fun (_s t : ℕ) (_δ : ℝ) => ((t : ℝ) + (13 + 1 : ℝ)) *
        ((0 : ℝ) + ((4148 - 1 : ℕ) : ℝ) / ((2013265921 : ℝ) ^ 6) +
          (13 : ℝ) * (1 / ((2013265921 : ℝ) ^ 6)))) =
      (fun (_s t : ℕ) (_δ : ℝ) => ((t : ℝ) + ((13 + 1 : ℕ) : ℝ)) * gatePrice evmAddDescriptor 13) := by
    funext _ t _
    rw [gatePrice_stage0]
    push_cast
    ring
  rw [hfun]
  exact h

/-- **The concrete rational, kernel-evaluated**: the per-`(t + 14)` factor is exactly
`4160 / 2013265921^6`, below `2^-173`. -/
theorem stage0Price_value :
    ((0 : ℚ) + ((4148 - 1 : ℕ) : ℚ) / ((2013265921 : ℚ) ^ 6) +
        (13 : ℚ) * (1 / ((2013265921 : ℚ) ^ 6))) = 4160 / 2013265921 ^ 6 ∧
      (4160 : ℚ) / 2013265921 ^ 6 < 1 / 2 ^ 173 := by
  norm_num

end Stage0

/-! ## §8. The deployed oracle, the non-interactive controller, the causal honest prover -/

section Oracle

open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)
open Minidregg.Compiler.Tower256CshakeMerkleController (Cshake256)
open Minidregg.Theory.TypedAuthorization (Digest)

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (hn : 0 < n)

/-- A lane message as twelve limbs. -/
def msgLimbs (p : RoundMsg) : List Nat :=
  [p.1.c0.val, p.1.c1.val, p.1.c2.val, p.1.c3.val, p.1.c4.val, p.1.c5.val,
    p.2.c0.val, p.2.c1.val, p.2.c2.val, p.2.c3.val, p.2.c4.val, p.2.c5.val]

theorem msgLimbs_injective : Function.Injective msgLimbs := by
  rintro ⟨⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩⟩
    ⟨⟨c0, c1, c2, c3, c4, c5⟩, ⟨e0, e1, e2, e3, e4, e5⟩⟩ h
  simp only [msgLimbs, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [Prod.mk.injEq, Ext6L.mk.injEq]
  exact ⟨⟨ZMod.val_injective _ h0, ZMod.val_injective _ h1, ZMod.val_injective _ h2,
      ZMod.val_injective _ h3, ZMod.val_injective _ h4, ZMod.val_injective _ h5⟩,
    ⟨ZMod.val_injective _ h6, ZMod.val_injective _ h7, ZMod.val_injective _ h8,
      ZMod.val_injective _ h9, ZMod.val_injective _ h10, ZMod.val_injective _ h11⟩⟩

/-- **The lane transcript as the FS input**: the root's bytes, the word's limbs, and the prefix
messages' limbs (the salts are empty at `s = 0`).  An `SrMove` of the gate reduction is exactly
"statement + salted message prefix" (Selvage/Rbr.lean); this is its wire form. -/
def moveWire (encodeRoot : Root → List UInt8) (q : SrMove (gateReduction commit d encNat hn) 0) :
    List UInt8 × (List Nat × List (List Nat)) :=
  let y : Fin n → BabyBear := q.stmt.y
  (encodeRoot q.stmt.x, (List.ofFn fun i : Fin n => (y i).val, q.pfx.map fun e => msgLimbs e.1))

/-- The prefix-decodable codec of the wire form (the tree's `StreamCodec`, REUSED). -/
def moveStream : StreamCodec (List UInt8 × (List Nat × List (List Nat))) :=
  StreamCodec.product Tower256ConcreteBackend.bytesStream
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.list (StreamCodec.list StreamCodec.nat)))

/-- The bytes hashed for one query. -/
def encodeMove (encodeRoot : Root → List UInt8) (q : SrMove (gateReduction commit d encNat hn) 0) :
    List UInt8 :=
  moveStream.encode (moveWire commit d encNat hn encodeRoot q)

/-- A prefix-decodable codec encodes injectively (`decodePrefix_encode` at the empty suffix). -/
theorem streamEncode_injective {α : Type} (c : StreamCodec α) : Function.Injective c.encode := by
  intro a b h
  have ha := c.decodePrefix_encode a []
  have hb := c.decodePrefix_encode b []
  rw [List.append_nil] at ha hb
  rw [h, hb] at ha
  exact ((Prod.mk.injEq _ _ _ _).mp (Option.some.inj ha)).1.symm

theorem moveWire_injective (encodeRoot : Root → List UInt8) (hroot : Function.Injective encodeRoot) :
    Function.Injective (moveWire commit d encNat hn encodeRoot) := by
  rintro ⟨⟨i₁, x₁, y₁⟩, p₁⟩ ⟨⟨i₂, x₂, y₂⟩, p₂⟩ h
  simp only [moveWire, Prod.mk.injEq] at h
  obtain ⟨hx, hy, hp⟩ := h
  have hx' : x₁ = x₂ := hroot hx
  have hy' : y₁ = y₂ := by
    funext i
    exact ZMod.val_injective _ (congrFun (List.ofFn_inj.mp hy) i)
  have hp' : p₁ = p₂ := by
    refine List.map_injective_iff.mpr ?_ hp
    intro e e' he
    exact Prod.ext (msgLimbs_injective he) (Subsingleton.elim _ _)
  cases hx'
  cases hy'
  cases hp'
  rfl

/-- **The FS input is a function of the transcript**: distinct queries hash distinct bytes. -/
theorem encodeMove_injective (encodeRoot : Root → List UInt8)
    (hroot : Function.Injective encodeRoot) :
    Function.Injective (encodeMove commit d encNat hn encodeRoot) :=
  fun _ _ h => moveWire_injective commit d encNat hn encodeRoot hroot
    (streamEncode_injective moveStream h)

/-- Six little-endian radix-`p` limbs of a digest: `digestToExt6` (`Ext6GateProofController`,
the noncomputable controller's) in lanes. -/
def digestToExt6L (dg : Digest) : Ext6L :=
  ⟨(((dg.value / babyBearP ^ 0) % babyBearP : Nat) : BabyBear),
    (((dg.value / babyBearP ^ 1) % babyBearP : Nat) : BabyBear),
    (((dg.value / babyBearP ^ 2) % babyBearP : Nat) : BabyBear),
    (((dg.value / babyBearP ^ 3) % babyBearP : Nat) : BabyBear),
    (((dg.value / babyBearP ^ 4) % babyBearP : Nat) : BabyBear),
    (((dg.value / babyBearP ^ 5) % babyBearP : Nat) : BabyBear)⟩

theorem read_digestToExt6L (dg : Digest) :
    readExt6 (digestToExt6L dg) = Ext6GateProofController.digestToExt6 dg := by
  unfold readExt6 Ext6GateProofController.digestToExt6
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Domain separation for this transcript. -/
def fsCustomization : List UInt8 := Tower256ConcreteBackend.utf8 "MINIDREGG/CT/FS/V1"

/-- The deployed cSHAKE256 controller: `Sp800185Cshake256.controller` at the backend's pins --
`Tower256ConcreteBackend.cshake` by `cshakeExact` (`rfl`), but that name is `noncomputable`;
this one runs. -/
def fsHash : Cshake256 :=
  Sp800185Cshake256.controller Tower256ConcreteBackend.cshakeAlgorithmId
    Tower256ConcreteBackend.digestCodecPin

theorem fsHash_eq_backend : fsHash = Tower256ConcreteBackend.cshake := rfl

/-- **The concrete oracle** `[FS-ROM]`: the cSHAKE256 digest of the encoded query, as six
lanes.  This is the function the tree's lazy-sampling handler `Oracle` is assumed to be
realized by; the theory above never names it. -/
def cshakeOracle (encodeRoot : Root → List UInt8)
    (q : SrMove (gateReduction commit d encNat hn) 0) : Ext6L :=
  digestToExt6L (fsHash.xofDigest fsCustomization (encodeMove commit d encNat hn encodeRoot q))

/-- A carried non-interactive receipt: the proof string with the challenges the prover claims
the oracle answered.  Neutral data until `fsCheck` recomputes every draw. -/
structure FsReceipt (Root : Type) (n m : Nat) where
  root : Root
  word : Fin n → BabyBear
  messages : Fin (m + 1) → RoundMsg
  challenges : Fin (m + 1) → Ext6L

/-- The proof string of a carried receipt (salts empty, the trivial witness). -/
def FsReceipt.output (rc : FsReceipt Root n m) : SrOutput (gateReduction commit d encNat hn) 0 :=
  ⟨⟨(), rc.root, rc.word⟩, rc.messages, fun _ => fun z => Fin.elim0 z, ()⟩

/-- Every route by which the non-interactive controller refuses. -/
inductive FsFailure
  /-- Some carried challenge is not the oracle at its transcript prefix. -/
  | challengeMismatch
  /-- The interactive controller refused. -/
  | rejected (e : CommittedTerminalController.Failure)
  deriving DecidableEq, Repr

/-- The salted prefix through message `i` of a message list, in `SrOutput.query`'s shape --
computable (it enumerates `Fin (m + 1)`, not the reduction's `k`). -/
def prefixQuery (rt : Root) (y : Fin n → BabyBear) (msgs : List RoundMsg) (i : Nat) :
    SrMove (gateReduction commit d encNat hn) 0 :=
  ⟨⟨(), rt, y⟩, ((List.finRange (m + 1)).take (i + 1)).map fun j : Fin (m + 1) =>
    (msgs.getD j.val junkMsg, fun z => Fin.elim0 z)⟩

/-- The query reads the messages only through index `i`. -/
theorem prefixQuery_congr (rt : Root) (y : Fin n → BabyBear) (msgs msgs' : List RoundMsg)
    (i : Nat) (h : ∀ k, k ≤ i → msgs.getD k junkMsg = msgs'.getD k junkMsg) :
    prefixQuery commit d encNat hn rt y msgs i = prefixQuery commit d encNat hn rt y msgs' i := by
  unfold prefixQuery
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hj
  rw [List.length_take, List.length_finRange] at hidx
  rw [List.getElem_take, List.getElem_finRange]
  exact Prod.ext (h idx (by omega)) rfl

theorem getD_ofFn_succ {α : Type} (f : Fin (m + 1) → α) (i : Fin (m + 1)) (dflt : α) :
    (List.ofFn f).getD i.val dflt = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

/-- The carried receipt's designated queries (`SrOutput.query`) ARE prefix queries of its
message list. -/
theorem output_query_eq (rc : FsReceipt Root n m) (i : Fin (m + 1)) :
    (rc.output commit d encNat hn).query i =
      prefixQuery commit d encNat hn rc.root rc.word (List.ofFn rc.messages) i := by
  unfold SrOutput.query prefixQuery FsReceipt.output
  congr 1
  apply List.map_congr_left
  intro j _
  rw [getD_ofFn_succ]

/-- Every carried challenge is the oracle at its transcript prefix (`SrOutput.query`). -/
def challengesExact (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (rc : FsReceipt Root n m) : Bool :=
  (List.finRange (m + 1)).all fun i =>
    decide (rc.challenges i = O (prefixQuery commit d encNat hn rc.root rc.word (List.ofFn rc.messages) i))

theorem challengesExact_iff (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (rc : FsReceipt Root n m) :
    challengesExact commit d encNat hn O rc = true ↔
      ∀ i : Fin (m + 1), rc.challenges i = O ((rc.output commit d encNat hn).query i) := by
  simp only [challengesExact, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
    output_query_eq]

/-- **The non-interactive controller**: refuse unless every carried challenge is the oracle at
its transcript prefix, then `check`. -/
def fsCheck (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rc : FsReceipt Root n m) :
    Except FsFailure (Receipt Root m) :=
  if challengesExact commit d encNat hn O rc then
    match check commit d encNat (gammaOf rc.challenges) rc.root
        (openingOf d encNat rc.word rc.challenges) (transcriptOf rc.messages rc.challenges) with
    | .ok r => .ok r
    | .error e => .error (.rejected e)
  else .error .challengeMismatch

/-- **Reflection**: an accepted carried receipt is accepted by the tree's `fiatShamir` at this
oracle -- the challenges were recomputed, so `check` ran at the derived ones. -/
theorem fsCheck_ok_fiatShamir (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (rc : FsReceipt Root n m) (r : Receipt Root m)
    (h : fsCheck commit d encNat hn O rc = .ok r) :
    fiatShamir (gateReduction commit d encNat hn) 0 O (rc.output commit d encNat hn) =
      some ((), fun _ => ()) := by
  unfold fsCheck at h
  by_cases hO : challengesExact commit d encNat hn O rc = true
  · rw [if_pos hO] at h
    have hchal : (fun i => O ((rc.output commit d encNat hn).query i)) = rc.challenges :=
      funext fun i => ((challengesExact_iff commit d encNat hn O rc).mp hO i).symm
    have hrew : fiatShamir (gateReduction commit d encNat hn) 0 O (rc.output commit d encNat hn) =
        gateVerify commit d encNat rc.root rc.word rc.messages rc.challenges := by
      unfold fiatShamir
      exact congrArg (gateVerify commit d encNat rc.root rc.word rc.messages) hchal
    rw [hrew]
    unfold gateVerify
    cases hch : check commit d encNat (gammaOf rc.challenges) rc.root
        (openingOf d encNat rc.word rc.challenges) (transcriptOf rc.messages rc.challenges) with
    | ok r' => rfl
    | error e =>
      rw [hch] at h
      exact absurd h (by simp)
  · rw [if_neg hO] at h
    exact absurd h (by simp)

/-- **The falsifier's shape**: a receipt carrying a challenge that is NOT the oracle at its
prefix is refused before any arithmetic, whatever `check` would have said at those challenges. -/
theorem fsCheck_refuses_mismatch (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (rc : FsReceipt Root n m)
    (h : ∃ i, rc.challenges i ≠ O ((rc.output commit d encNat hn).query i)) :
    fsCheck commit d encNat hn O rc = .error .challengeMismatch := by
  unfold fsCheck
  rw [if_neg]
  intro hO
  obtain ⟨i, hi⟩ := h
  exact hi ((challengesExact_iff commit d encNat hn O rc).mp hO i)

/-! ### The causal honest prover -/

/-- Round `i`'s honest message at the challenges collected so far (junk past `m`). -/
def stepMsg (y : Fin n → BabyBear) (st : List RoundMsg × List Ext6L) (i : Nat) : RoundMsg :=
  if h : i < m then
    laneRound d (traceOf y) (st.2.getD 0 ext6Zero) (fun j => st.2.getD (j.val + 1) ext6Zero)
      encNat ⟨i, h⟩
  else junkMsg

/-- One causal step: append round `i`'s message, then the oracle's answer at the prefix
through it. -/
def fsStep (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (st : List RoundMsg × List Ext6L) (i : Nat) :
    List RoundMsg × List Ext6L :=
  let msgs := st.1 ++ [stepMsg d encNat y st i]
  (msgs, st.2 ++ [O (prefixQuery commit d encNat hn rt y msgs (i + 1))])

/-- **The causal schedule**: stage `0` is the junk message and `γ`; stage `i + 1` extends stage
`i`.  Structural in the stage: each message is computed ONCE, at the challenges already drawn
(linear work; the exponential re-derivation of a fixed-point formulation never happens). -/
def fsStage (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) : Nat → List RoundMsg × List Ext6L
  | 0 => ([junkMsg], [O (prefixQuery commit d encNat hn rt y [junkMsg] 0)])
  | i + 1 => fsStep commit d encNat hn O rt y (fsStage O rt y i) i

theorem fsStage_length (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (i : Nat) :
    (fsStage commit d encNat hn O rt y i).1.length = i + 1 ∧
      (fsStage commit d encNat hn O rt y i).2.length = i + 1 := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    simp only [fsStage, fsStep, List.length_append, List.length_singleton, ih.1, ih.2, and_self]

/-- Later stages extend earlier ones: the messages below a stage are that stage's. -/
theorem fsStage_getD_fst (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (i j : Nat) (hij : i ≤ j) (k : Nat) (hk : k ≤ i) :
    (fsStage commit d encNat hn O rt y j).1.getD k junkMsg =
      (fsStage commit d encNat hn O rt y i).1.getD k junkMsg := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((fsStage commit d encNat hn O rt y j).1 ++ _).getD k junkMsg = _
    rw [List.getD_append _ _ _ _ (by rw [(fsStage_length commit d encNat hn O rt y j).1]; omega)]

theorem fsStage_getD_snd (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (i j : Nat) (hij : i ≤ j) (k : Nat) (hk : k ≤ i) :
    (fsStage commit d encNat hn O rt y j).2.getD k ext6Zero =
      (fsStage commit d encNat hn O rt y i).2.getD k ext6Zero := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((fsStage commit d encNat hn O rt y j).2 ++ _).getD k ext6Zero = _
    rw [List.getD_append _ _ _ _ (by rw [(fsStage_length commit d encNat hn O rt y j).2]; omega)]

/-- **The honest non-interactive prover**: the carried receipt after the `m` sumcheck rounds. -/
def fsProve (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) : FsReceipt Root n m :=
  let st := fsStage commit d encNat hn O rt y m
  ⟨rt, y, fun i => st.1.getD i junkMsg, fun i => st.2.getD i ext6Zero⟩

/-- **Every carried challenge is the oracle at its prefix** -- the causal schedule hashed
exactly the prefix `SrOutput.query` names. -/
theorem fsProve_challenge (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (i : Fin (m + 1)) :
    (fsProve commit d encNat hn O rt y).challenges i =
      O (((fsProve commit d encNat hn O rt y).output commit d encNat hn).query i) := by
  rw [output_query_eq]
  have him : i.val ≤ m := Nat.lt_succ_iff.mp i.isLt
  show (fsStage commit d encNat hn O rt y m).2.getD i.val ext6Zero =
    O (prefixQuery commit d encNat hn rt y
      (List.ofFn fun j : Fin (m + 1) => (fsStage commit d encNat hn O rt y m).1.getD j.val junkMsg) i.val)
  rw [prefixQuery_congr commit d encNat hn rt y _ (fsStage commit d encNat hn O rt y i.val).1 i.val
      (fun k hk => by
        rw [getD_ofFn_succ (m := m) _ ⟨k, by omega⟩]
        exact fsStage_getD_fst commit d encNat hn O rt y i.val m him k hk),
    fsStage_getD_snd commit d encNat hn O rt y i.val m him i.val le_rfl]
  cases hi : i.val with
  | zero => rfl
  | succ k =>
    show ((fsStage commit d encNat hn O rt y k).2 ++
        [O (prefixQuery commit d encNat hn rt y (fsStage commit d encNat hn O rt y (k + 1)).1 (k + 1))]).getD
        (k + 1) ext6Zero = _
    rw [List.getD_append_right _ _ _ _ (by rw [(fsStage_length commit d encNat hn O rt y k).2]),
      (fsStage_length commit d encNat hn O rt y k).2, Nat.sub_self]
    rfl

/-- The prefix chi reads the challenges only below its cut. -/
theorem lanePrefixChi_congr (b : Fin m → Bool) (x x' : Fin m → Ext6L) (k : Nat)
    (h : ∀ j : Fin m, j.val < k → x j = x' j) : lanePrefixChi b x k = lanePrefixChi b x' k := by
  unfold lanePrefixChi
  congr 1
  apply congrArg List.ofFn
  funext j
  by_cases hj : j.val < k
  · rw [if_pos hj, if_pos hj, h j hj]
  · rw [if_neg hj, if_neg hj]

theorem roundWalk_congr (gamma : Ext6L) (r r' : Fin m → Ext6L) (i : Fin m)
    (h : ∀ j : Fin m, j.val < i.val → r j = r' j) :
    ∀ (l : List BabyBear) (k : Nat) (gpow : Ext6L) (acc : RoundMsg),
      roundWalk gamma r encNat i l k gpow acc = roundWalk gamma r' encNat i l k gpow acc := by
  intro l
  induction l with
  | nil => intro k gpow acc; rfl
  | cons c rest ih =>
    intro k gpow acc
    simp only [roundWalk, lanePrefixChi_congr (encNat k) r r' i.val h]
    exact ih _ _ _

/-- **Prefix-measurability of the honest lane prover**: round `i`'s message reads the
challenges only below `i`. -/
theorem laneRound_congr (wv : Nat → BabyBear) (gamma : Ext6L) (r r' : Fin m → Ext6L) (i : Fin m)
    (h : ∀ j : Fin m, j.val < i.val → r j = r' j) :
    laneRound d wv gamma r encNat i = laneRound d wv gamma r' encNat i :=
  roundWalk_congr encNat gamma r r' i h _ _ _ _

/-- **The prover's messages are the honest lane messages at the derived challenges.** -/
theorem fsProve_message (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L) (rt : Root)
    (y : Fin n → BabyBear) (i : Fin m) :
    (fsProve commit d encNat hn O rt y).messages i.succ =
      laneRound d (traceOf y) (gammaOf (fsProve commit d encNat hn O rt y).challenges)
        (roundsOf (fsProve commit d encNat hn O rt y).challenges) encNat i := by
  have him : i.val + 1 ≤ m := i.isLt
  show (fsStage commit d encNat hn O rt y m).1.getD (i.val + 1) junkMsg =
    laneRound d (traceOf y) ((fsStage commit d encNat hn O rt y m).2.getD 0 ext6Zero)
      (fun j => (fsStage commit d encNat hn O rt y m).2.getD (j.val + 1) ext6Zero) encNat i
  rw [fsStage_getD_fst commit d encNat hn O rt y (i.val + 1) m him (i.val + 1) le_rfl]
  show ((fsStage commit d encNat hn O rt y i.val).1 ++
      [stepMsg d encNat y (fsStage commit d encNat hn O rt y i.val) i.val]).getD (i.val + 1) junkMsg = _
  rw [List.getD_append_right _ _ _ _ (by rw [(fsStage_length commit d encNat hn O rt y i.val).1]),
    (fsStage_length commit d encNat hn O rt y i.val).1, Nat.sub_self]
  show stepMsg d encNat y (fsStage commit d encNat hn O rt y i.val) i.val = _
  rw [stepMsg, dif_pos i.isLt,
    fsStage_getD_snd commit d encNat hn O rt y i.val m (le_of_lt i.isLt) 0 (Nat.zero_le _)]
  apply laneRound_congr
  intro j hj
  exact (fsStage_getD_snd commit d encNat hn O rt y i.val m (le_of_lt i.isLt) (j.val + 1) hj).symm

/-- **Completeness of the non-interactive prover**: for a satisfying word, the honest carried
receipt is accepted by `fsCheck` under the oracle it was run against -- `receipt_complete`
(REUSED) at the derived challenges, the carried challenges exact by `fsProve_challenge`. -/
theorem fsProve_complete (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (y : Fin n → BabyBear)
    (enc : Fin (descriptorResiduals d (traceOf y)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hd : descriptorHolds d (traceOf y)) :
    fsCheck commit d encNat hn O (fsProve commit d encNat hn O (commit y) y) =
      .ok ⟨commit y, gammaOf (fsProve commit d encNat hn O (commit y) y).challenges,
        transcriptOf (fsProve commit d encNat hn O (commit y) y).messages
          (fsProve commit d encNat hn O (commit y) y).challenges,
        laneTerminal (gammaOf (fsProve commit d encNat hn O (commit y) y).challenges)
          (roundsOf (fsProve commit d encNat hn O (commit y) y).challenges) encNat
          (descriptorResiduals d (traceOf y))⟩ := by
  unfold fsCheck
  rw [if_pos ((challengesExact_iff commit d encNat hn O _).mpr
    (fsProve_challenge commit d encNat hn O (commit y) y))]
  have htr : transcriptOf (fsProve commit d encNat hn O (commit y) y).messages
      (fsProve commit d encNat hn O (commit y) y).challenges =
      honestTranscript d (traceOf y) (gammaOf (fsProve commit d encNat hn O (commit y) y).challenges)
        (roundsOf (fsProve commit d encNat hn O (commit y) y).challenges) encNat := by
    unfold transcriptOf honestTranscript
    congr 1
    funext i
    exact fsProve_message commit d encNat hn O (commit y) y i
  have hroot : (fsProve commit d encNat hn O (commit y) y).root = commit y := rfl
  have hword : (fsProve commit d encNat hn O (commit y) y).word = y := rfl
  have hop : openingOf d encNat y (fsProve commit d encNat hn O (commit y) y).challenges =
      ⟨y, laneTerminal (gammaOf (fsProve commit d encNat hn O (commit y) y).challenges)
        (roundsOf (fsProve commit d encNat hn O (commit y) y).challenges) encNat
        (descriptorResiduals d (traceOf y))⟩ := rfl
  rw [htr, hroot, hword, hop, receipt_complete commit d encNat _ _ y enc hEnc hd]

/-- **The honest FS receipt is accepted by the tree's `fiatShamir`** at any oracle. -/
theorem fsProve_fiatShamir (O : SrMove (gateReduction commit d encNat hn) 0 → Ext6L)
    (y : Fin n → BabyBear)
    (enc : Fin (descriptorResiduals d (traceOf y)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hd : descriptorHolds d (traceOf y)) :
    fiatShamir (gateReduction commit d encNat hn) 0 O
        ((fsProve commit d encNat hn O (commit y) y).output commit d encNat hn) =
      some ((), fun _ => ()) :=
  fsCheck_ok_fiatShamir commit d encNat hn O _ _ (fsProve_complete commit d encNat hn O y enc hEnc hd)

/-- A satisfying trace's honest lane message is `(0, 0)` at EVERY challenge: its table is zero. -/
theorem laneRound_of_holds (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (hd : descriptorHolds d wv) (gamma : Ext6L) (r : Fin m → Ext6L) (i : Fin m) :
    laneRound d wv gamma r encNat i = (ext6Zero, ext6Zero) := by
  obtain ⟨h0, h1⟩ := read_laneRound d wv enc encNat hEnc gamma r i
  have hz : ∀ b, gammaResidualTable d wv enc (readExt6 gamma) b = 0 :=
    gammaResidualTable_zero_of_descriptorHolds d wv enc (readExt6 gamma) hd
  have hmle : mle (gammaResidualTable d wv enc (readExt6 gamma)) = fun _ => 0 := by
    funext x
    simp [mle, hz]
  rw [hmle] at h0 h1
  simp only [roundSum, Finset.sum_const_zero] at h0 h1
  ext
  · exact readExt6_injective (h0.trans read_zero.symm)
  · exact readExt6_injective (h1.trans read_zero.symm)

/-- The all-zero lane transcript at challenges `r`. -/
def zeroTranscript (r : Fin m → Ext6L) : LaneTranscript m := ⟨fun _ => (ext6Zero, ext6Zero), r⟩

/-- **A satisfying word's all-zero transcript is accepted at EVERY challenge vector** (the
honest transcript IS the zero transcript for it) -- so a challenge that is not the hash of the
prefix is exactly what `fsCheck` refuses and `check` alone cannot. -/
theorem check_zero_of_holds (y : Fin n → BabyBear)
    (enc : Fin (descriptorResiduals d (traceOf y)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hd : descriptorHolds d (traceOf y)) (gamma : Ext6L)
    (r : Fin m → Ext6L) :
    check commit d encNat gamma (commit y)
        ⟨y, laneTerminal gamma r encNat (descriptorResiduals d (traceOf y))⟩ (zeroTranscript r) =
      .ok ⟨commit y, gamma, zeroTranscript r,
        laneTerminal gamma r encNat (descriptorResiduals d (traceOf y))⟩ := by
  have h := receipt_complete commit d encNat gamma r y enc hEnc hd
  have hz : honestTranscript d (traceOf y) gamma r encNat = zeroTranscript r := by
    unfold honestTranscript zeroTranscript
    congr 1
    funext i
    exact laneRound_of_holds d encNat (traceOf y) enc hEnc hd gamma r i
  rw [hz] at h
  exact h

end Oracle

/-! ## §9. ATLAS fields on the emitted demo descriptor, decided -/

namespace DemoInstance

open CommittedTerminalRealizer.DemoInstance

/-- The canonical oracle realizing `(γ, r)` -- `fsOracle`'s computable shape for this
reduction: it answers by the prefix length (round `i`'s query has prefix length `i + 1`,
`SrOutput.query_pfx_length`), so it realizes the challenge vector on every proof string. -/
def oracleOfChallenges (gamma : Ext6L) (r : Fin 5 → Ext6L)
    (q : SrMove (gateReduction S.commit demoDescriptor (bitCorner 5) (by norm_num)) 0) : Ext6L :=
  match q.pfx.length with
  | 0 => ext6Zero
  | 1 => gamma
  | j + 2 => if h : j < 5 then r ⟨j, h⟩ else ext6Zero

/-- The challenge vector `(γ, r)` as the carried challenges. -/
def demoChallenges (gamma : Ext6L) (r : Fin 5 → Ext6L) : Fin 6 → Ext6L :=
  fun i => match i with
    | 0 => gamma
    | ⟨j + 1, h⟩ => r ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The honest carried receipt of the demo: the zero messages (a satisfying trace's honest
messages, `laneRound_of_holds`) and the challenges `(γ, r)`. -/
def demoReceipt : FsReceipt (Fin 23 → BabyBear) 23 5 :=
  ⟨demoWord, demoWord, fun _ => junkMsg, demoChallenges gamma r⟩

/-- **Satisfiable, decided**: the honest carried receipt is accepted by the non-interactive
controller under the canonical oracle of its challenges -- the 6 challenge recomputations, the
realizer, the 5 round checks, and the terminal, all in the kernel. -/
theorem fsCheck_complete_demo :
    fsCheck S.commit demoDescriptor (bitCorner 5) (by norm_num) (oracleOfChallenges gamma r)
        demoReceipt =
      .ok ⟨demoWord, gamma, ⟨fun _ => junkMsg, r⟩, ext6Zero⟩ := by
  decide +kernel

/-- **Teeth, decided (the falsifier)**: the same receipt with `γ` off by one is refused as
`challengeMismatch` -- although `check` ACCEPTS its transcript at the altered `γ`
(`check_zero_of_holds`: a satisfying trace's zero transcript passes at every challenge).  The
FS binding is load-bearing beyond `check`. -/
theorem fsCheck_refuses_forged_gamma_demo :
    fsCheck S.commit demoDescriptor (bitCorner 5) (by norm_num) (oracleOfChallenges gamma r)
        ⟨demoWord, demoWord, fun _ => junkMsg, demoChallenges (ext6Add gamma ext6One) r⟩ =
      .error .challengeMismatch := by
  decide +kernel

theorem check_accepts_forged_gamma_demo :
    check S.commit demoDescriptor (bitCorner 5) (ext6Add gamma ext6One) (S.commit demoWord)
        ⟨demoWord, laneTerminal (ext6Add gamma ext6One) r (bitCorner 5)
          (descriptorResiduals demoDescriptor (traceOf demoWord))⟩ (zeroTranscript r) =
      .ok ⟨demoWord, ext6Add gamma ext6One, zeroTranscript r,
        laneTerminal (ext6Add gamma ext6One) r (bitCorner 5)
          (descriptorResiduals demoDescriptor (traceOf demoWord))⟩ :=
  check_zero_of_holds S.commit demoDescriptor (bitCorner 5) demoWord
    (residualEmbedding demoDescriptor (traceOf demoWord) demo_residuals_fit) (fun _ => rfl)
    demoWord_holds _ _

/-- `2⁻¹` in BabyBear: `(p + 1)/2`. -/
def halfLane : Ext6L := ⟨1006632961, 0, 0, 0, 0, 0⟩

/-- The demo challenges with `r₀ := 1/2`. -/
def rHalf : Fin 5 → Ext6L := fun i => if i = 0 then halfLane else r i

/-- A proof string whose verdict is the ORACLE's: message `1` is `(1, −1)` (it passes round
`0`'s check against the zero claim), the rest zero.  Round `1`'s check then reads
`0 = 1 − 2·r₀`: true iff `r₀ = 1/2`. -/
def teethOutput : SrOutput (gateReduction S.commit demoDescriptor (bitCorner 5) (by norm_num)) 0 :=
  ⟨⟨(), demoWord, demoWord⟩,
    fun i => if i.val = 1 then (ext6One, ext6Sub ext6Zero ext6One) else junkMsg,
    fun _ => fun z => Fin.elim0 z, ()⟩

/-- **Teeth in `fiatShamir_teeth`'s shape, decided**: ONE proof string, REJECTED under the
oracle answering `(γ, r)` and ACCEPTED under the oracle answering `(γ, r[0 ↦ 1/2])`.  The
challenge derivation is load-bearing: the non-interactive verifier is the oracle's doing. -/
theorem fiatShamir_teeth_demo :
    fiatShamir (gateReduction S.commit demoDescriptor (bitCorner 5) (by norm_num)) 0
        (oracleOfChallenges gamma r) teethOutput = none ∧
      ∃ v, fiatShamir (gateReduction S.commit demoDescriptor (bitCorner 5) (by norm_num)) 0
        (oracleOfChallenges gamma rHalf) teethOutput = some v := by
  constructor
  · decide +kernel
  · apply Option.isSome_iff_exists.mp
    decide +kernel

end DemoInstance

/-! ## §10. Stage 0: the non-interactive 4,131-wire receipt (compiled exhibit) -/

namespace Stage0Exhibit

open CommittedTerminalRealizer.Stage0Exhibit
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.EvmAddAir
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec)

/-- The ideal root IS the word; its bytes are the word's limbs. -/
def encodeRoot (rt : Fin 4131 → BabyBear) : List UInt8 :=
  (StreamCodec.list StreamCodec.nat).encode (List.ofFn fun i => (rt i).val)

/-- The Stage-0 oracle: cSHAKE256 over the encoded transcript prefix. -/
def O := cshakeOracle S.commit evmAddDescriptor (bitCorner 13) (by norm_num) encodeRoot

/-- The honest `(1, 2)` candidate's non-interactive receipt: `γ` and the thirteen challenges
derived by cSHAKE256 from the transcript prefixes (the word, the root, the messages so far),
the thirteen honest messages computed causally; accepted end to end.  Then the two falsifiers:
one derived challenge altered (refused before any arithmetic), and the forged `Z = 4` word's own
honest FS run at its own root (refused at a round check -- its zero claim is false at its
derived `γ`; the exhibit throws if the gamma event happened to occur).  Throws on any
deviation. -/
def exhibit : IO Unit := do
  let honest := wordOf (evmAddCandidate 1 2)
  let rc := fsProve S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O (S.commit honest) honest
  match fsCheck S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O rc with
  | .ok r =>
      if r.terminal = ext6Zero then
        IO.println "stage0 fs: honest (1, 2) non-interactive receipt accepted: gamma and 13 challenges derived by cSHAKE256 from the transcript prefixes, 13 rounds, terminal 0"
      else throw (IO.userError "stage0 fs: honest receipt has a nonzero terminal")
  | .error e => throw (IO.userError s!"stage0 fs: honest FS receipt refused: {repr e}")
  IO.println s!"stage0 fs: derived gamma {repr (rc.challenges 0)}, derived r_0 {repr (rc.challenges 1)}"
  let rcBad : FsReceipt (Fin 4131 → BabyBear) 4131 13 :=
    { rc with challenges := Function.update rc.challenges 3 (ext6Add (rc.challenges 3) ext6One) }
  match fsCheck S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O rcBad with
  | .error .challengeMismatch =>
      IO.println "stage0 fs: receipt with one challenge not the hash of its prefix refused (challengeMismatch)"
  | _ => throw (IO.userError "stage0 fs: altered challenge not refused")
  let forged := wordOf (evmAddClaimed 1 2 4)
  let rcF := fsProve S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O (S.commit forged) forged
  match fsCheck S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O rcF with
  | .error (.rejected .roundCheck) =>
      IO.println "stage0 fs: forged word's own FS proof at its own root refused at a round check (zero claim false at its derived gamma)"
  | .error e => throw (IO.userError s!"stage0 fs: forged word refused on another route: {repr e}")
  | .ok _ => throw (IO.userError "stage0 fs: forged word's FS proof ACCEPTED: the gamma event occurred at the derived gamma")

#eval exhibit

end Stage0Exhibit

#check @gateReduction
#check @gateRbr
#check @gateProof_fs_sound
#check @gateProof_fs_sound_reading
#check @gateProof_joint_price
#check @Stage0.stage0Receipt_price
#check @fsCheck_ok_fiatShamir
#check @fsProve_complete
#check @encodeMove_injective

/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.gateProof_fs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof_fs_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.gateProof_fs_sound_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof_fs_sound_reading
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.stage_bad_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage_bad_zero
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.stage_bad_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage_bad_succ
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.gateProof_joint_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof_joint_price
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.Stage0.stage0Receipt_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Stage0.stage0Receipt_price
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.Stage0.stage0Price_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Stage0.stage0Price_value
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.fsCheck_ok_fiatShamir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fsCheck_ok_fiatShamir
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.fsProve_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fsProve_complete
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.fsProve_fiatShamir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fsProve_fiatShamir
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.encodeMove_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeMove_injective
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.DemoInstance.fsCheck_complete_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.fsCheck_complete_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.DemoInstance.fsCheck_refuses_forged_gamma_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.fsCheck_refuses_forged_gamma_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.DemoInstance.check_accepts_forged_gamma_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.check_accepts_forged_gamma_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFiatShamir.DemoInstance.fiatShamir_teeth_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.fiatShamir_teeth_demo

end Minidregg.Compiler.CommittedTerminalFiatShamir
