/-
# `Assurance/SpeculativePrefillAudit.lean` — Causal Speculative-Prefill Rollout Equivalence & Depth-Looped Weight-Opening Collapse

**Substrate, said out loud: this is Lean-authored protocol & denotational assurance.** Composes
directly over `Assurance/ZkmlGruenSumcheck.lean`, `Assurance/ZkmlEinSumcheck.lean`,
`Assurance/ZkmlMatmulCommitment.lean`, `Theory/ZkmlEinsum.lean`, and `Theory/ZkmlMatmulSum.lean`.
Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.

## What this file proves

Modern `80–110 tok/s` float serving engines (e.g. Apple Metal `llama.cpp` on `Qwen3.8-27B`) emit an
untrusted `T`-token draft `draft : List Tok` fast in hardware float, while exact-integer `zkML`
trajectory verification (`BabyBear Ext4` `Gruen` Mode-2 + `IntWY` + `D1b` LogUp) is `12×–35×`
faster per token in **batched parallel prefill (`1 × T`)** than in **sequential autoregressive
decode (`T × 1`)**. Meanwhile, 2026 depth-looped MoE architectures (`thinkingmachines/Inkling-2-Mini`:
middle layers `6..18` looped `R = 3` times with shared weights `W`) apply the same committed weight
matrix across `R` sequential passes.

Two AFP-grade theorem families establish exact soundness and completeness of both primitives:

1. **Causal Speculative-Prefill Rollout Equivalence & Exact First-Divergence Recovery (§1–§3)**:
   * **`IsGreedyDom` & `greedyTok` (`greedyTok_spec`, `greedyTok_unique`)**: over any finite
     non-empty linearly ordered vocabulary `Tok` and linearly ordered logit carrier `L` (including
     `ℤ`), canonical index-tie-broken dominance (`logits v < logits y` for `v < y`, and
     `logits v ≤ logits y` for `y ≤ v`) is **always inhabited** by `greedyTok logits` and
     **uniquely determines** `y`.
   * **`speculativePrefill_iff_greedyRollout`**: for any causal sequence-to-logits transducer
     `F : List Tok → ℕ → (Tok → L)` (`Causal F`: position `pos`'s logit map depends only on
     `xs.take (pos + 1)`), any non-empty `prompt`, and **any** untrusted draft `draft` of length
     `T`, `T` sequential autoregressive steps `greedyRollout F prompt T = draft` holds **if and
     only if** a **single parallel prefill evaluation** `F (prompt ++ draft.dropLast)` satisfies
     `IsGreedyDom` locally at every offset `t < T`.
   * **`speculativePrefill_firstDivergence`**: whenever `draft ≠ greedyRollout F prompt T`, the
     single parallel prefill pass on `prompt ++ draft.dropLast` deterministically identifies the
     **exact first diverging index `t* < T`** (`draft.take t* = rollout.take t*`,
     `draft[t*] ≠ rollout[t*]`) **AND** recovers the true next token
     `greedyTok (prefill (prompt.length - 1 + t*)) = rollout[t*]` (`1` free corrected token on
     mismatch, extending the verified prefix to `t* + 1` with zero wasted prefix work!).
   * **Exact `ℤ` / `ZMod p` `D1b` Positive-Gap Bridge (`isGreedyDom_iff_tieBrokenGap_nonneg`,
     `zmod_gap_range_implies_isGreedyDom`)**: connects `IsGreedyDom` over `ℤ` directly to our
     `BabyBear Ext4` `D1b` LogUp-GKR range check `Δ_{t,v} = (logit_{t,ŷ} - logit_{t,v}) - 1[v < ŷ] ∈ [0, B)`.
   * **Three Constructive Falsifier Teeth (`by decide`)**:
     - `tieBreak_omission_admits_canberra_drift`: dropping strict `<` on `v < y` (`NaiveWeakGreedyDom`)
       accepts **both** `"Canberra."` and `"Canberra"` on flat ties (`VERDICTS.md` §8/§9);
     - `nonCausal_lookahead_breaks_prefill_iff`: a 1-token lookahead transducer satisfies every
       parallel prefill dominance check while diverging from `greedyRollout`;
     - `mod_gap_without_range_forges_argmax`: modular gap arithmetic in `ZMod 17` without `[0, B)`
       range enforcement lets a losing token forge argmax via wraparound.

2. **Depth-Looped MoE / Recurrent Weight-Opening Collapse (`loopedPass_eq_stackedEinsum`, §4)**:
   * Over any `[CommRing α]`, connects `R` sequential passes `Y^{(r)} = X^{(r)} W` (`r : Fin R`,
     e.g. `R = 3` in `Inkling-2-Mini`) directly to `Theory.ZkmlMatmulSum.contract`,
     `Theory.ZkmlEinsum.einsumContract`, and `Assurance.ZkmlMatmulSumcheck.mle₂`:
     - **`loopedPass_eq_stackedEinsum`**: `R` passes equal one stacked `(R · T) × K × N`
       `einsumContract`, AND at any loop-folding challenge `ρ ∈ α`,
       `∑_{r < R} ρ^r · contract (X r) W = contract (∑_{r < R} ρ^r · X r) W` — collapsing **`R`
       sumchecks and `R` expensive PCS openings of `W` into ONE sumcheck and ONE opening of `W`**!
     - **`loopFold_soundness_roots_le` & `loopFold_soundness_prob_le`**: over `[Field F]`, if any
       pass `r* < R` (`R ≥ 1`) has a false claimed output `Y_claim r* ≠ contract (X r*) W`, loop
       folding accepts on **at most `R - 1` challenges** (`≤ (R - 1) / |F|`, i.e. `2 / |Ext4|` for
       `Inkling-2-Mini` `R = 3`).
     - **`loopFold_postChallenge_forgery_tooth` (`∀ ρ` + `ZMod 7` `R = 3` witness)**: if `Y^{(r)}`
       is chosen *after* seeing `ρ` (`Y'_0 = Y_0 - ρ Δ, Y'_1 = Y_1 + Δ, Y'_2 = Y_2`), pass `1` is
       forged (`Y'_1 ≠ contract (X 1) W`) yet passes the folded equation for **every** `ρ` with
       probability `1` — proving pre-`ρ` commitment of `Y^{(0..R-1)}` is load-bearing.
-/
import Assurance.ZkmlGruenSumcheck

namespace Minidregg.Assurance.SpeculativePrefillAudit

open Minidregg.Selvage Minidregg.Theory.ZkmlTensorOps Minidregg.Theory.ZkmlEinsum

/-! ## §1. Canonical Index-Tie-Broken Greedy Argmax (`IsGreedyDom`, `greedyTok`, `greedyTok_unique`) -/

section GreedyArgmax

/-- **Canonical index-tie-broken greedy dominance (`IsGreedyDom`):**
Token `y : Tok` strictly beats every smaller token `v < y` (`logits v < logits y`) and weakly
beats every token `v ≥ y` (`logits v ≤ logits y`), selecting the unique minimum-index global
maximizer of `logits`. -/
def IsGreedyDom {Tok L : Type*} [LT Tok] [LE Tok] [LT L] [LE L]
    (logits : Tok → L) (y : Tok) : Prop :=
  (∀ v, v < y → logits v < logits y) ∧ (∀ v, y ≤ v → logits v ≤ logits y)

instance instDecidableIsGreedyDom {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [LinearOrder L]
    (logits : Tok → L) (y : Tok) : Decidable (IsGreedyDom logits y) := by
  unfold IsGreedyDom
  infer_instance

/-- Any token satisfying `IsGreedyDom` is a global maximizer of `logits`. -/
theorem isGreedyDom_le_all {Tok L : Type*} [LinearOrder Tok] [LinearOrder L]
    {logits : Tok → L} {y : Tok} (h : IsGreedyDom logits y) (v : Tok) :
    logits v ≤ logits y := by
  rcases lt_or_ge v y with hlt | hge
  · exact le_of_lt (h.1 v hlt)
  · exact h.2 v hge

/-- **Uniqueness of canonical tie-broken dominance (`isGreedyDom_unique`):**
At most one token `y` can satisfy `IsGreedyDom logits y`. -/
theorem isGreedyDom_unique {Tok L : Type*} [LinearOrder Tok] [LinearOrder L]
    {logits : Tok → L} {y₁ y₂ : Tok}
    (h₁ : IsGreedyDom logits y₁) (h₂ : IsGreedyDom logits y₂) :
    y₁ = y₂ := by
  rcases lt_trichotomy y₁ y₂ with hlt | rfl | hgt
  · exact False.elim (not_lt_of_ge (h₁.2 y₂ (le_of_lt hlt)) (h₂.1 y₁ hlt))
  · rfl
  · exact False.elim (not_lt_of_ge (h₂.2 y₁ (le_of_lt hgt)) (h₁.1 y₂ hgt))

/-- **Canonical computable deterministic greedy argmax (`greedyTok`):**
Selects the minimum token index among all global maximizers of `logits`. -/
def greedyTok {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [Nonempty Tok] [LinearOrder L]
    (logits : Tok → L) : Tok :=
  let maxLogit := (Finset.univ.image logits).max' (Finset.univ_nonempty.image logits)
  let maximizers := Finset.univ.filter (fun v : Tok => logits v = maxLogit)
  have hMax : maximizers.Nonempty := by
    rcases Finset.mem_image.mp
        (Finset.max'_mem (Finset.univ.image logits) (Finset.univ_nonempty.image logits)) with
      ⟨v, hv, hvm⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvm⟩⟩
  maximizers.min' hMax

/-- `greedyTok logits` always satisfies the canonical tie-broken dominance certificate. -/
theorem greedyTok_spec {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [Nonempty Tok]
    [LinearOrder L] (logits : Tok → L) :
    IsGreedyDom logits (greedyTok logits) := by
  let maxLogit := (Finset.univ.image logits).max' (Finset.univ_nonempty.image logits)
  let maximizers := Finset.univ.filter (fun v : Tok => logits v = maxLogit)
  have hMax : maximizers.Nonempty := by
    rcases Finset.mem_image.mp
        (Finset.max'_mem (Finset.univ.image logits) (Finset.univ_nonempty.image logits)) with
      ⟨v, hv, hvm⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvm⟩⟩
  have hy_mem : greedyTok logits ∈ maximizers := Finset.min'_mem maximizers hMax
  have hy_eq : logits (greedyTok logits) = maxLogit := (Finset.mem_filter.mp hy_mem).2
  have hall_le : ∀ v : Tok, logits v ≤ logits (greedyTok logits) := fun v => by
    rw [hy_eq]
    exact Finset.le_max' (Finset.univ.image logits) (logits v)
      (Finset.mem_image_of_mem logits (Finset.mem_univ v))
  refine ⟨fun v hlt => ?_, fun v _ => hall_le v⟩
  refine lt_of_le_of_ne (hall_le v) (fun heq => ?_)
  have hv_mem : v ∈ maximizers :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, heq.trans hy_eq⟩
  exact not_le_of_gt hlt (Finset.min'_le maximizers v hv_mem)

/-- **Unique characterization of `greedyTok` (`greedyTok_unique`):**
`IsGreedyDom logits y` holds if and only if `y = greedyTok logits`. -/
theorem greedyTok_unique {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [Nonempty Tok]
    [LinearOrder L] (logits : Tok → L) (y : Tok) :
    IsGreedyDom logits y ↔ y = greedyTok logits :=
  ⟨fun hy => isGreedyDom_unique hy (greedyTok_spec logits),
   fun h => h ▸ greedyTok_spec logits⟩

end GreedyArgmax

/-! ## §2. Causal Sequence-to-Logits Transducers, Parallel Prefill, and First-Divergence Recovery -/

section CausalSpeculativePrefill

/-- Prefix-slice helper: for `t < xs.length`, `xs.dropLast` agrees with `xs` on the first `t` items. -/
theorem take_dropLast_of_lt {α : Type*} :
    ∀ (xs : List α) (t : ℕ), t < xs.length → xs.dropLast.take t = xs.take t
  | [], _, ht => by simp at ht
  | [_], 0, _ => rfl
  | [_], _ + 1, ht => by simp at ht
  | _ :: b :: rest, 0, _ => rfl
  | a :: b :: rest, t + 1, ht => by
      have ht' : t < (b :: rest).length := by simp at ht ⊢; omega
      change (a :: (b :: rest).dropLast).take (t + 1) = a :: (b :: rest).take t
      simp [take_dropLast_of_lt (b :: rest) t ht']

/-- Prefix of `xs ++ ys` at length `xs.length + t` is `xs ++ ys.take t`. -/
theorem take_append_add_length {α : Type*} :
    ∀ (xs ys : List α) (t : ℕ), (xs ++ ys).take (xs.length + t) = xs ++ ys.take t
  | [], ys, t => by simp
  | a :: xs, ys, t => by
      have hlen : (a :: xs).length + t = (xs.length + t) + 1 := by simp; omega
      rw [hlen]
      simp [take_append_add_length xs ys t]

/-- **Core Speculative-Prefill Prefix Identity (`take_prompt_append_dropLast`):**
For any `prompt`, `draft`, and step `t < draft.length`, the `(prompt.length + t)`-token prefix of
`prompt ++ draft.dropLast` is **identical** to `prompt ++ draft.take t` (never needing the last
drafted token `draft[T - 1]`). -/
theorem take_prompt_append_dropLast {α : Type*} (prompt draft : List α) {t : ℕ}
    (ht : t < draft.length) :
    (prompt ++ draft.dropLast).take (prompt.length + t) = prompt ++ draft.take t := by
  rw [take_append_add_length, take_dropLast_of_lt draft t ht]

/-- **Causality of a parallel sequence-to-logits transducer (`Causal`):**
Given `F : List Tok → ℕ → (Tok → L)` (mapping a token sequence `xs` and 0-based position `pos`
to position `pos`'s logit vector), `Causal F` asserts that `F xs pos` depends **only** on the
causal prefix `xs.take (pos + 1)` — covering causal `GQA`, `QSA`, `SWA`, and `Gated DeltaNet` WY. -/
def Causal {Tok L : Type*} (F : List Tok → ℕ → (Tok → L)) : Prop :=
  ∀ (xs ys : List Tok) (pos : ℕ), xs.take (pos + 1) = ys.take (pos + 1) → F xs pos = F ys pos

/-- Canonical lift of any context-to-next-logits transducer `g : List Tok → (Tok → L)` into a
parallel sequence-to-logits operator `ofContextMap g xs pos := g (xs.take (pos + 1))`. -/
def ofContextMap {Tok L : Type*} (g : List Tok → (Tok → L)) : List Tok → ℕ → (Tok → L) :=
  fun xs pos => g (xs.take (pos + 1))

theorem causal_ofContextMap {Tok L : Type*} (g : List Tok → (Tok → L)) :
    Causal (ofContextMap g) := by
  intro xs ys pos h
  simp [ofContextMap, h]

/-- **Sequential `T`-step autoregressive greedy rollout (`greedyRollout`):**
Starting from `prompt`, repeatedly evaluates `F` at the last context position `ctx.length - 1`,
selects `y = greedyTok (...)`, appends `[y]`, and continues for `T` sequential steps. -/
def greedyRollout {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [Nonempty Tok] [LinearOrder L]
    (F : List Tok → ℕ → (Tok → L)) (prompt : List Tok) : ℕ → List Tok
  | 0 => []
  | T + 1 =>
    let y := greedyTok (F prompt (prompt.length - 1))
    y :: greedyRollout F (prompt ++ [y]) T

@[simp] theorem greedyRollout_length {Tok L : Type*} [Fintype Tok] [LinearOrder Tok] [Nonempty Tok]
    [LinearOrder L] (F : List Tok → ℕ → (Tok → L)) :
    ∀ (prompt : List Tok) (T : ℕ), (greedyRollout F prompt T).length = T
  | _, 0 => rfl
  | prompt, T + 1 => by
      simp [greedyRollout, greedyRollout_length F _ T]

/-- **Single-Pass Parallel Prefill Dominance Certificate (`PrefillDominates`):**
Evaluates `F (prompt ++ draft.dropLast)` **once** in parallel and checks `IsGreedyDom`
locally at every position `prompt.length - 1 + t` against `draft[t]` (`0 ≤ t < draft.length`). -/
def PrefillDominates {Tok L : Type*} [LT Tok] [LE Tok] [LT L] [LE L]
    (F : List Tok → ℕ → (Tok → L)) (prompt draft : List Tok) : Prop :=
  ∀ (t : Fin draft.length),
    IsGreedyDom (F (prompt ++ draft.dropLast) (prompt.length - 1 + t.1)) (draft.get t)

instance instDecidablePrefillDominates {Tok L : Type*} [Fintype Tok] [LinearOrder Tok]
    [LinearOrder L] (F : List Tok → ℕ → (Tok → L)) (prompt draft : List Tok) :
    Decidable (PrefillDominates F prompt draft) := by
  unfold PrefillDominates
  infer_instance

/-- **Causal Prefill Slice Lemma (`causal_prefill_logit_eq`):**
Under `Causal F` and `prompt ≠ []`, position `prompt.length - 1 + t` of the single parallel prefill
pass on `prompt ++ draft.dropLast` produces the **exact** endpoint logit vector of
`prompt ++ draft.take t`. -/
theorem causal_prefill_logit_eq {Tok L : Type*} {F : List Tok → ℕ → (Tok → L)}
    (hCausal : Causal F) {prompt : List Tok} (hPrompt : prompt ≠ [])
    (draft : List Tok) {t : ℕ} (ht : t < draft.length) :
    F (prompt ++ draft.dropLast) (prompt.length - 1 + t) =
      F (prompt ++ draft.take t) ((prompt ++ draft.take t).length - 1) := by
  have hp_pos : 0 < prompt.length := List.length_pos_iff.mpr hPrompt
  have hpos_succ : (prompt.length - 1 + t) + 1 = prompt.length + t := by omega
  have hctx_len : (prompt ++ draft.take t).length = prompt.length + t := by
    rw [List.length_append, List.length_take_of_le (Nat.le_of_lt ht)]
  have hidx : (prompt ++ draft.take t).length - 1 = prompt.length - 1 + t := by
    omega
  rw [hidx]
  apply hCausal
  rw [hpos_succ, take_prompt_append_dropLast prompt draft ht, ← hctx_len, List.take_length]

/-- Inductive core over `draft`: `greedyRollout` equals `draft` iff every prefix step matches `greedyTok`. -/
private theorem greedyRollout_eq_iff_prefix_greedy {Tok L : Type*} [Fintype Tok] [LinearOrder Tok]
    [Nonempty Tok] [LinearOrder L] (F : List Tok → ℕ → (Tok → L)) :
    ∀ (draft prompt : List Tok),
      greedyRollout F prompt draft.length = draft ↔
        ∀ (t : Fin draft.length),
          draft.get t =
            greedyTok (F (prompt ++ draft.take t.1) ((prompt ++ draft.take t.1).length - 1))
  | [], prompt => by simp [greedyRollout]
  | d :: ds, prompt => by
      simp only [List.length_cons, greedyRollout, List.cons.injEq]
      constructor
      · rintro ⟨hd, htail⟩ t
        refine Fin.cases ?_ ?_ t
        · simp [hd]
        · intro j
          have ih := (greedyRollout_eq_iff_prefix_greedy F ds (prompt ++ [d])).mp
            (hd ▸ htail) j
          simpa [List.take_succ_cons, List.append_assoc] using ih
      · intro hall
        have hd0 : d = greedyTok (F prompt (prompt.length - 1)) := by
          simpa using hall ⟨0, Nat.zero_lt_succ _⟩
        refine ⟨hd0.symm, ?_⟩
        rw [← hd0]
        refine (greedyRollout_eq_iff_prefix_greedy F ds (prompt ++ [d])).mpr (fun j => ?_)
        simpa [List.take_succ_cons, List.append_assoc] using hall j.succ

/-- **Theorem 1a (`speculativePrefill_iff_greedyRollout`):**
For ANY causal sequence-to-logits transducer `F`, ANY non-empty `prompt`, and ANY untrusted
float-drafted continuation `draft` of length `T` (`draft.length = T`), `T` sequential
autoregressive greedy steps `greedyRollout F prompt T = draft` hold **if and only if** ONE
parallel prefill pass on `prompt ++ draft.dropLast` satisfies `PrefillDominates F prompt draft`! -/
theorem speculativePrefill_iff_greedyRollout {Tok L : Type*} [Fintype Tok] [LinearOrder Tok]
    [Nonempty Tok] [LinearOrder L] {F : List Tok → ℕ → (Tok → L)}
    (hCausal : Causal F) {prompt : List Tok} (hPrompt : prompt ≠ [])
    {draft : List Tok} {T : ℕ} (hLen : draft.length = T) :
    greedyRollout F prompt T = draft ↔ PrefillDominates F prompt draft := by
  subst hLen
  rw [greedyRollout_eq_iff_prefix_greedy]
  unfold PrefillDominates
  constructor
  · intro h t
    rw [causal_prefill_logit_eq hCausal hPrompt draft t.2, greedyTok_unique]
    exact h t
  · intro h t
    have hdom := h t
    rw [causal_prefill_logit_eq hCausal hPrompt draft t.2, greedyTok_unique] at hdom
    exact hdom

/-- Prefix-rollout inductive core for `speculativePrefill_firstDivergence`. -/
private theorem firstDivergence_core {Tok L : Type*} [Fintype Tok] [LinearOrder Tok]
    [Nonempty Tok] [LinearOrder L] (F : List Tok → ℕ → (Tok → L)) :
    ∀ (draft prompt : List Tok),
      draft ≠ greedyRollout F prompt draft.length →
      ∃ (tStar : Fin draft.length),
        let rollout := greedyRollout F prompt draft.length
        (∀ j : Fin draft.length, j < tStar →
          draft.get j =
            greedyTok (F (prompt ++ draft.take j.1) ((prompt ++ draft.take j.1).length - 1))) ∧
        draft.get tStar ≠
          greedyTok (F (prompt ++ draft.take tStar.1) ((prompt ++ draft.take tStar.1).length - 1)) ∧
        draft.take tStar.1 = rollout.take tStar.1 ∧
        draft.get tStar ≠ rollout[tStar.1]'(by rw [greedyRollout_length]; exact tStar.2) ∧
        greedyTok (F (prompt ++ draft.take tStar.1) ((prompt ++ draft.take tStar.1).length - 1)) =
          rollout[tStar.1]'(by rw [greedyRollout_length]; exact tStar.2) ∧
        draft.take tStar.1 ++
          [greedyTok (F (prompt ++ draft.take tStar.1) ((prompt ++ draft.take tStar.1).length - 1))] =
          rollout.take (tStar.1 + 1)
  | [], prompt, hNe => absurd rfl hNe
  | d :: ds, prompt, hNe => by
      let y₀ := greedyTok (F prompt (prompt.length - 1))
      by_cases hd : d = y₀
      · have hTailNe : ds ≠ greedyRollout F (prompt ++ [d]) ds.length := by
          intro hEq
          apply hNe
          simp [greedyRollout, ← hd, y₀, ← hEq]
        rcases firstDivergence_core F ds (prompt ++ [d]) hTailNe with
          ⟨jStar, hPrev, hFail, hTake, hGetNe, hCorr, hBonus⟩
        refine ⟨jStar.succ, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          refine Fin.cases ?_ ?_ j
          · intro _; simp [hd, y₀]
          · intro k hk
            have hk_lt : k < jStar := Fin.succ_lt_succ_iff.mp hk
            simpa [List.take_succ_cons, List.append_assoc] using hPrev k hk_lt
        · simpa [List.take_succ_cons, List.append_assoc] using hFail
        · simp [greedyRollout, ← hd, y₀, hTake]
        · simpa [greedyRollout, ← hd, y₀] using hGetNe
        · simpa [List.take_succ_cons, List.append_assoc, greedyRollout, ← hd, y₀] using hCorr
        · simpa [List.take_succ_cons, List.append_assoc, greedyRollout, ← hd, y₀] using hBonus
      · refine ⟨⟨0, Nat.zero_lt_succ _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j.1)
        · simpa [y₀] using hd
        · simp
        · simpa [greedyRollout, y₀] using hd
        · simp [greedyRollout]
        · simp [greedyRollout]

/-- **Theorem 1b (`speculativePrefill_firstDivergence`):**
Whenever `draft ≠ greedyRollout F prompt T` (`draft.length = T`), the **single parallel prefill
pass** `prefill := F (prompt ++ draft.dropLast)` deterministically pinpoints the **exact first
diverging index `tStar < T`** such that:
1. Every earlier position `j < tStar` passes `IsGreedyDom (prefill (prompt.length - 1 + j))` while
   `tStar` fails `IsGreedyDom`,
2. `draft.take tStar = rollout.take tStar` and `draft[tStar] ≠ rollout[tStar]`, AND
3. `greedyTok (prefill (prompt.length - 1 + tStar)) = rollout[tStar]` (`1` **free exact corrected
   token** extending the verified prefix to `rollout.take (tStar + 1)` with zero wasted work!). -/
theorem speculativePrefill_firstDivergence {Tok L : Type*} [Fintype Tok] [LinearOrder Tok]
    [Nonempty Tok] [LinearOrder L] {F : List Tok → ℕ → (Tok → L)}
    (hCausal : Causal F) {prompt : List Tok} (hPrompt : prompt ≠ [])
    {draft : List Tok} {T : ℕ} (hLen : draft.length = T)
    (hNe : draft ≠ greedyRollout F prompt T) :
    let prefill := F (prompt ++ draft.dropLast)
    let rollout := greedyRollout F prompt T
    ∃ (tStar : Fin draft.length),
      (∀ j : Fin draft.length, j < tStar →
        IsGreedyDom (prefill (prompt.length - 1 + j.1)) (draft.get j)) ∧
      ¬ IsGreedyDom (prefill (prompt.length - 1 + tStar.1)) (draft.get tStar) ∧
      draft.take tStar.1 = rollout.take tStar.1 ∧
      draft.get tStar ≠ rollout[tStar.1]'(by subst hLen; rw [greedyRollout_length]; exact tStar.2) ∧
      greedyTok (prefill (prompt.length - 1 + tStar.1)) =
        rollout[tStar.1]'(by subst hLen; rw [greedyRollout_length]; exact tStar.2) ∧
      draft.take tStar.1 ++ [greedyTok (prefill (prompt.length - 1 + tStar.1))] =
        rollout.take (tStar.1 + 1) := by
  subst hLen
  rcases firstDivergence_core F draft prompt hNe with
    ⟨tStar, hPrev, hFail, hTake, hGetNe, hCorr, hBonus⟩
  refine ⟨tStar, ?_, ?_, hTake, hGetNe, ?_, ?_⟩
  · intro j hj
    rw [causal_prefill_logit_eq hCausal hPrompt draft j.2, greedyTok_unique]
    exact hPrev j hj
  · rw [causal_prefill_logit_eq hCausal hPrompt draft tStar.2, greedyTok_unique]
    exact hFail
  · rw [causal_prefill_logit_eq hCausal hPrompt draft tStar.2]
    exact hCorr
  · rw [causal_prefill_logit_eq hCausal hPrompt draft tStar.2]
    exact hBonus

end CausalSpeculativePrefill

/-! ## §3. `D1b` Integer Positive-Gap Bridge & Constructive Falsifier Teeth (`Canberra`, Lookahead, Wraparound) -/

section GapBridgeAndTeeth

/-- **Shifted Integer Dominance Gap (`tieBrokenGap`):**
`Δ(y, v) = (logits y - logits v) - 1[v < y]`, matching `spec_prefill.rs`'s `D1b` LogUp witness! -/
def tieBrokenGap {Tok : Type*} [LinearOrder Tok] (logits : Tok → ℤ) (y v : Tok) : ℤ :=
  (logits y - logits v) - (if v < y then 1 else 0)

/-- **Exact `ℤ` Equivalence (`isGreedyDom_iff_tieBrokenGap_nonneg`):**
Over `ℤ`, `IsGreedyDom logits y` holds if and only if `0 ≤ tieBrokenGap logits y v` for every `v`. -/
theorem isGreedyDom_iff_tieBrokenGap_nonneg {Tok : Type*} [LinearOrder Tok]
    (logits : Tok → ℤ) (y : Tok) :
    IsGreedyDom logits y ↔ ∀ v : Tok, 0 ≤ tieBrokenGap logits y v := by
  unfold IsGreedyDom tieBrokenGap
  constructor
  · rintro ⟨hlt, hge⟩ v
    by_cases hv : v < y
    · have h1 := hlt v hv; simp [hv]; omega
    · have h2 := hge v (le_of_not_gt hv); simp [hv]; omega
  · intro hgap
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have h1 := hgap v; simp [hv] at h1; omega
    · have hnv : ¬ v < y := not_lt_of_ge hv
      have h2 := hgap v; simp [hnv] at h2; omega

/-- **Modular `ZMod p` → Exact `ℤ` Soundness Bridge (`zmod_gap_range_implies_isGreedyDom`):**
If every true integer gap satisfies `-(p - B : ℤ) < tieBrokenGap logits y v < p` (e.g. bounded
`i16` logits with `B = 2^16`, `p = 2013265921` BabyBear) and the prover exhibits `[0, B)` range-checked
witnesses `w : Tok → ℕ` (`w v < B`, discharged via `D1b` LogUp-GKR) matching `tieBrokenGap` modulo `p`,
then `IsGreedyDom logits y` holds **over `ℤ` with zero modular wraparound**! -/
theorem zmod_gap_range_implies_isGreedyDom {Tok : Type*} [LinearOrder Tok]
    {p B : ℕ} (logits : Tok → ℤ) (y : Tok) (w : Tok → ℕ)
    (hRange : ∀ v, w v < B)
    (hHeadroomLo : ∀ v, -((p : ℤ) - (B : ℤ)) < tieBrokenGap logits y v)
    (hHeadroomHi : ∀ v, tieBrokenGap logits y v < (p : ℤ))
    (hMod : ∀ v, ((w v : ℤ) : ZMod p) = (tieBrokenGap logits y v : ZMod p)) :
    IsGreedyDom logits y := by
  rw [isGreedyDom_iff_tieBrokenGap_nonneg]
  intro v
  have hdvd : (p : ℤ) ∣ ((w v : ℤ) - tieBrokenGap logits y v) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hMod v, sub_self]
  rcases hdvd with ⟨k, hk⟩
  have hw_lt : (w v : ℤ) < (B : ℤ) := Int.ofNat_lt.mpr (hRange v)
  have hw_nonneg : (0 : ℤ) ≤ (w v : ℤ) := Int.natCast_nonneg (w v)
  have hlo := hHeadroomLo v
  have hhi := hHeadroomHi v
  have hp_pos : (0 : ℤ) < (p : ℤ) := by omega
  have hk0 : k = 0 := by
    by_contra hk_ne
    rcases lt_or_gt_of_ne hk_ne with hneg | hpos
    · have hkp : (p : ℤ) * k ≤ -(p : ℤ) := by
        have hk1 : k ≤ -1 := by omega
        nlinarith
      omega
    · have hkp : (p : ℤ) ≤ (p : ℤ) * k := by
        have hk1 : 1 ≤ k := by omega
        nlinarith
      omega
  rw [hk0, mul_zero] at hk
  omega

/-- Naive weak greedy dominance WITHOUT index tie-breaking (`logits v ≤ logits y` for all `v`). -/
def NaiveWeakGreedyDom {Tok L : Type*} [LE L] (logits : Tok → L) (y : Tok) : Prop :=
  ∀ v, logits v ≤ logits y

/-- **Falsifier Tooth 1 (`tieBreak_omission_admits_canberra_drift`, `VERDICTS.md` §8/§9):**
On `Fin 3` (`0 = "Canberra."`, `1 = "Canberra"`, `2 = "<eos>"`) with flat top logits `![42, 42, 7]`,
`NaiveWeakGreedyDom` accepts **two distinct tokens** (`0 ≠ 1`), permitting silent `"Canberra." → "Canberra"`
steering, whereas `IsGreedyDom` uniquely accepts `0` (`"Canberra."`) and rejects `1` (`"Canberra"`). -/
theorem tieBreak_omission_admits_canberra_drift :
    let flatLogits : Fin 3 → ℤ := ![42, 42, 7]
    let tokCanberraDot : Fin 3 := 0
    let tokCanberra : Fin 3 := 1
    tokCanberraDot ≠ tokCanberra ∧
    NaiveWeakGreedyDom flatLogits tokCanberraDot ∧
    NaiveWeakGreedyDom flatLogits tokCanberra ∧
    IsGreedyDom flatLogits tokCanberraDot ∧
    ¬ IsGreedyDom flatLogits tokCanberra := by
  refine ⟨by decide, ?_, ?_, by decide, by decide⟩
  · unfold NaiveWeakGreedyDom; decide
  · unfold NaiveWeakGreedyDom; decide

/-- **Positive Premise-Inhabitation & `speculativePrefill_firstDivergence` Firing (`causal_prefill_positive_witness`):**
Inhabits `Causal`, `greedyRollout`, `PrefillDominates`, and explicitly invokes BOTH
`speculativePrefill_iff_greedyRollout` and `speculativePrefill_firstDivergence` on a concrete
4-token `Fin 4` causal Markov transducer (`T = 3`), verifying accepted honest draft `[2, 3, 0]`
and steered draft `[2, 1, 0]` (`t* = 1`, free corrected token `3`!). -/
def demoCausalTransducer : List (Fin 4) → ℕ → (Fin 4 → ℤ) :=
  ofContextMap fun ctx v =>
    match ctx.getLast? with
    | none => 0
    | some last =>
      let target : Fin 4 := ⟨(last.1 + 1) % 4, Nat.mod_lt _ (by decide)⟩
      if v = target then 10 else 1

theorem causal_prefill_positive_witness :
    let prompt : List (Fin 4) := [1]
    let honestDraft : List (Fin 4) := [2, 3, 0]
    let steeredDraft : List (Fin 4) := [2, 1, 0] -- steered at index t* = 1 (`1` instead of `3`)!
    Causal demoCausalTransducer ∧
    greedyRollout demoCausalTransducer prompt 3 = honestDraft ∧
    PrefillDominates demoCausalTransducer prompt honestDraft ∧
    (∃ tStar : Fin steeredDraft.length,
      steeredDraft.take tStar.1 =
        (greedyRollout demoCausalTransducer prompt 3).take tStar.1 ∧
      steeredDraft.take tStar.1 ++
        [greedyTok (demoCausalTransducer (prompt ++ steeredDraft.dropLast)
          (prompt.length - 1 + tStar.1))] =
        (greedyRollout demoCausalTransducer prompt 3).take (tStar.1 + 1)) := by
  have hC : Causal demoCausalTransducer := causal_ofContextMap _
  have hP : ([1] : List (Fin 4)) ≠ [] := by decide
  have hSteerNe : ([2, 1, 0] : List (Fin 4)) ≠ greedyRollout demoCausalTransducer [1] 3 := by decide
  rcases speculativePrefill_firstDivergence hC hP (T := 3) rfl hSteerNe with
    ⟨tStar, _, _, hTake, _, _, hBonus⟩
  exact ⟨hC, by decide, (speculativePrefill_iff_greedyRollout hC hP rfl).mp (by decide),
    ⟨tStar, hTake, hBonus⟩⟩

/-- **Falsifier Tooth 2 (`nonCausal_lookahead_breaks_prefill_iff`):**
Dropping `Causal F` breaks `speculativePrefill_iff_greedyRollout`: a transducer `badLookaheadF`
that peeks 1 token ahead (`xs[pos + 1]?`) accepts `draft = [1, 0]` in parallel prefill while
sequential `greedyRollout` produces `[0, 0] ≠ [1, 0]`. -/
def badLookaheadF : List (Fin 2) → ℕ → (Fin 2 → ℤ) :=
  fun xs pos v =>
    match xs[pos + 1]? with
    | some nextTok => if v = nextTok then 5 else 0
    | none => if v = 0 then 5 else 0

theorem nonCausal_lookahead_breaks_prefill_iff :
    let prompt : List (Fin 2) := [0]
    let draft : List (Fin 2) := [1, 0]
    ¬ Causal badLookaheadF ∧
    PrefillDominates badLookaheadF prompt draft ∧
    greedyRollout badLookaheadF prompt draft.length ≠ draft := by
  refine ⟨?_, by decide, by decide⟩
  intro hC
  have h := congrFun (hC [0, 1] [0, 0] 0 rfl) 1
  simp [badLookaheadF] at h

/-- **Falsifier Tooth 3a (`mod_gap_without_range_forges_argmax`):**
Over `ZMod 17` without the `w v < B` (`D1b`) range check, losing token `1` (`logit = 0` vs token `0`'s
`logit = 5`) exhibits modular "gaps" `w = ![11, 0]` matching `tieBrokenGap` mod `17`, yet
`¬ IsGreedyDom ![5, 0] 1`. -/
theorem mod_gap_without_range_forges_argmax :
    let logits : Fin 2 → ℤ := ![5, 0]
    let forgedTok : Fin 2 := 1
    let forgedWit : Fin 2 → ℕ := ![11, 0] -- `0 - 5 - 1 = -6 ≡ 11 (mod 17)`!
    (∀ v : Fin 2, ((forgedWit v : ℤ) : ZMod 17) = (tieBrokenGap logits forgedTok v : ZMod 17)) ∧
    ¬ IsGreedyDom logits forgedTok := by
  refine ⟨by decide, by decide⟩

/-- **Falsifier Tooth 3b (`mod_gap_without_headroom_forges_argmax`):**
Dropping `hHeadroomLo` (`-(p - B) < tieBrokenGap`) in `zmod_gap_range_implies_isGreedyDom` ALSO
breaks soundness even when `w v < B` holds! Over `ZMod 17` with `B = 4`, `logits = ![0, 15]` has
true winner `1`, yet losing token `0` exhibits `w = ![0, 2]` satisfying BOTH `w v < 4` AND
`w v ≡ tieBrokenGap (mod 17)` (`0 - 15 = -15 ≡ 2 (mod 17)`), while `zmod_gap_range_implies_isGreedyDom`
succeeds when logits are `[0, B)`-bounded (`shiftedLogit ∈ [0, B)`, `2 * B < p`). -/
theorem mod_gap_without_headroom_forges_argmax :
    let logitsWrap : Fin 2 → ℤ := ![0, 15]
    let wWrap : Fin 2 → ℕ := ![0, 2]
    let logitsBounded : Fin 2 → ℤ := ![3, 1]
    ((∀ v : Fin 2, wWrap v < 4) ∧
      (∀ v : Fin 2, ((wWrap v : ℤ) : ZMod 17) = (tieBrokenGap logitsWrap 0 v : ZMod 17)) ∧
      ¬ IsGreedyDom logitsWrap 0) ∧
    IsGreedyDom logitsBounded 0 := by
  intro logitsWrap wWrap logitsBounded
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  exact zmod_gap_range_implies_isGreedyDom (p := 17) (B := 4) logitsBounded 0 ![0, 2]
    (by decide) (by decide) (by decide) (by decide)

end GapBridgeAndTeeth

/-! ## §4. Depth-Looped MoE Weight-Opening Collapse (`loopedPass_eq_stackedEinsum`, `Inkling-2-Mini` `R = 3`) -/

section LoopedWeightCollapse

/-- Stack `R` sequential loop-pass activation matrices `X : Fin R → Fin T → Fin K → α` into one
`(R * T) × K` matrix (`thinkingmachines/Inkling-2-Mini`: `R = 3` passes sharing weight matrix `W`). -/
def stackLoopAct {α : Type*} {R T K : ℕ} (X : Fin R → Fin T → Fin K → α) :
    Fin (R * T) → Fin K → α :=
  fun rt k => X (finProdFinEquiv.symm rt).1 (finProdFinEquiv.symm rt).2 k

/-- Fold `R` loop-pass activation matrices along powers `1, ρ, …, ρ^{R-1}` into a **single**
`T × K` matrix `∑_{r < R} ρ^r · X^{(r)}`. -/
def foldLoopAct {α : Type*} [Semiring α] {R T K : ℕ} (ρ : α)
    (X : Fin R → Fin T → Fin K → α) : Fin T → Fin K → α :=
  fun t k => ∑ r : Fin R, ρ ^ (r : ℕ) * X r t k

/-- Fold `R` claimed loop-pass output matrices along `1, ρ, …, ρ^{R-1}` into `∑_{r < R} ρ^r · Y^{(r)}`. -/
def foldLoopOut {α : Type*} [Semiring α] {R T N : ℕ} (ρ : α)
    (Y : Fin R → Fin T → Fin N → α) : Fin T → Fin N → α :=
  fun t j => ∑ r : Fin R, ρ ^ (r : ℕ) * Y r t j

/-- **Theorem 2a (`loopedPass_eq_stackedEinsum`):**
Over ANY commutative ring `α` (including `ℤ`, `BabyBear`, `Ext4`, and `HoistedB61`):
1. **Stacked `ZkmlEinsum` Equivalence**: `R` sequential passes `contract (X r) W` equal ONE stacked
   `einsumContract` (`mL = R * T, mR = N, mS = 1, sL = 1, sM = K, sR = 1`) against the **single**
   shared weight matrix `W`; AND
2. **`ρ`-Folded Single-Contraction Collapse**: for ANY loop-folding challenge `ρ : α`,
   `∑_{r : Fin R} ρ^r · contract (X r) W t j = contract (foldLoopAct ρ X) W t j`,
   reducing **`R` sumchecks and `R` weight-matrix PCS openings of `W` to ONE single contraction
   and ONE opening of `W`** (`3×` weight-proving collapse for `Inkling-2-Mini` `R = 3`)! -/
theorem loopedPass_eq_stackedEinsum {α : Type} [CommRing α] {R T K N : ℕ}
    (X : Fin R → Fin T → Fin K → α) (W : Fin K → Fin N → α) (ρ : α) :
    (∀ (r : Fin R) (t : Fin T) (j : Fin N),
      contract (X r) W t j =
        einsumContract (mL := R * T) (mR := N) (mS := 1) (sL := 1) (sM := K) (sR := 1)
          (fun rt _ _ k => stackLoopAct X rt k)
          (fun j' _ k _ => W k j')
          (finProdFinEquiv (r, t)) j 0) ∧
    (∀ (t : Fin T) (j : Fin N),
      (∑ r : Fin R, ρ ^ (r : ℕ) * contract (X r) W t j) =
        contract (foldLoopAct ρ X) W t j) := by
  refine ⟨fun r t j => ?_, fun t j => ?_⟩
  · unfold contract einsumContract stackLoopAct
    simp
  · unfold contract foldLoopAct
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
    ring

/-- **Multilinear Extension (`mle₂`) Loop-Folding Identity (`mle₂_loopFold_eq_single_matmulTable`):**
Over any field `F`, at every outer challenge `(x, y) ∈ F^μ × F^ν` and loop challenge `ρ ∈ F`, the
`ρ`-weighted combination of `R` honest cube-indexed contractions `matmulTable (X r) W` equals ONE
`mle₂` evaluation of `matmulTable` on the `ρ`-folded activation cube against **the single weight
table `W`**! -/
theorem mle₂_loopFold_eq_single_matmulTable {F : Type} [Field F] {R μ κ ν : ℕ}
    (X : Fin R → (Fin μ → Bool) → (Fin κ → Bool) → F)
    (W : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (ρ : F) (x : Fin μ → F) (y : Fin ν → F) :
    (∑ r : Fin R, ρ ^ (r : ℕ) * mle₂ (matmulTable (X r) W) x y) =
      mle₂ (matmulTable (fun i p => ∑ r : Fin R, ρ ^ (r : ℕ) * X r i p) W) x y := by
  simp only [mle₂_contraction, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hfactor :
      (∑ r : Fin R, ρ ^ (r : ℕ) * (rowPartial (X r) x p * colPartial W y p)) =
        (∑ r : Fin R, ρ ^ (r : ℕ) * rowPartial (X r) x p) * colPartial W y p := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => (mul_assoc _ _ _).symm
  rw [hfactor]
  congr 1
  unfold rowPartial mle
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => (mul_assoc _ _ _).symm

/-- Univariate loop-defect polynomial `D(X) = ∑_{r < R} d_r X^r` at a disagreed entry `(t, j)`. -/
noncomputable def loopDefectPoly {R_ring : Type*} [Semiring R_ring] {R : ℕ}
    (d : Fin R → R_ring) : Polynomial R_ring :=
  ∑ r : Fin R, Polynomial.monomial (r : ℕ) (d r)

theorem loopDefectPoly_eval {R_ring : Type*} [CommSemiring R_ring] {R : ℕ}
    (d : Fin R → R_ring) (ρ : R_ring) :
    (loopDefectPoly d).eval ρ = ∑ r : Fin R, ρ ^ (r : ℕ) * d r := by
  unfold loopDefectPoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_monomial, mul_comm]

theorem loopDefectPoly_coeff {R_ring : Type*} [Semiring R_ring] {R : ℕ}
    (d : Fin R → R_ring) (r : Fin R) :
    (loopDefectPoly d).coeff (r : ℕ) = d r := by
  unfold loopDefectPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hne
    have hval : (b : ℕ) ≠ (r : ℕ) := fun hv => hne (Fin.ext hv)
    simp [hval]
  · intro hr; exact absurd (Finset.mem_univ r) hr

theorem loopDefectPoly_natDegree_le {R_ring : Type*} [Semiring R_ring] {R : ℕ}
    (hR : 1 ≤ R) (d : Fin R → R_ring) :
    (loopDefectPoly d).natDegree ≤ R - 1 := by
  unfold loopDefectPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun r _ => ?_⟩
  exact (Polynomial.natDegree_monomial_le (d r)).trans (by omega)

/-- **Loop-Folding Soundness Root Bound (`loopFold_soundness_roots_le`):**
Over any `[Field F]` (`R ≥ 1`), if **any** pass `rStar : Fin R` has a false claimed output matrix
`Y_claim rStar ≠ contract (X rStar) W`, then across any finite challenge pool `S : Finset F`, at
most **`R - 1`** challenges `ρ ∈ S` satisfy `foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W`! -/
theorem loopFold_soundness_roots_le {F : Type} [Field F] [DecidableEq F]
    {R T K N : ℕ} (hR : 1 ≤ R)
    (X : Fin R → Fin T → Fin K → F) (W : Fin K → Fin N → F)
    (Y_claim : Fin R → Fin T → Fin N → F)
    {rStar : Fin R} (hWrong : Y_claim rStar ≠ contract (X rStar) W)
    (S : Finset F) :
    (S.filter (fun ρ => foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W)).card ≤ R - 1 := by
  have hex : ∃ (t : Fin T) (j : Fin N), Y_claim rStar t j ≠ contract (X rStar) W t j := by
    by_contra hall
    simp only [not_exists, Decidable.not_not] at hall
    exact hWrong (funext fun t => funext fun j => hall t j)
  rcases hex with ⟨t, j, hne_tj⟩
  let d : Fin R → F := fun r => Y_claim r t j - contract (X r) W t j
  have hd_ne : loopDefectPoly d ≠ 0 := by
    intro hzero
    have hc := loopDefectPoly_coeff d rStar
    rw [hzero, Polynomial.coeff_zero] at hc
    exact hne_tj (sub_eq_zero.mp hc.symm)
  have hsub :
      S.filter (fun ρ => foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W) ⊆
        (loopDefectPoly d).roots.toFinset := by
    intro ρ hmem
    have heq := congrFun (congrFun (Finset.mem_filter.mp hmem).2 t) j
    have heval : (loopDefectPoly d).eval ρ = 0 := by
      rw [loopDefectPoly_eval]
      have hlin :
          (∑ r : Fin R, ρ ^ (r : ℕ) * d r) =
            foldLoopOut ρ Y_claim t j -
              ∑ r : Fin R, ρ ^ (r : ℕ) * contract (X r) W t j := by
        simp only [d, foldLoopOut, mul_sub, Finset.sum_sub_distrib]
      rw [hlin, (loopedPass_eq_stackedEinsum X W ρ).2 t j, heq, sub_self]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd_ne).mpr heval)
  calc
    (S.filter (fun ρ => foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W)).card
      ≤ (loopDefectPoly d).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (loopDefectPoly d).roots := Multiset.toFinset_card_le _
    _ ≤ (loopDefectPoly d).natDegree := Polynomial.card_roots' (loopDefectPoly d)
    _ ≤ R - 1 := loopDefectPoly_natDegree_le hR d

/-- **Uniform-Probability Loop-Folding Soundness (`loopFold_soundness_prob_le`):**
For `Inkling-2-Mini` (`R = 3`), loop folding accepts a forged pass with probability at most
`(R - 1) / |F| = 2 / |F|` (`< 2^{-122.6}` over `BabyBear Ext4`) while cutting weight-matrix PCS
openings `3×` (`3 → 1`)! -/
theorem loopFold_soundness_prob_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {R T K N : ℕ} (hR : 1 ≤ R)
    (X : Fin R → Fin T → Fin K → F) (W : Fin K → Fin N → F)
    (Y_claim : Fin R → Fin T → Fin N → F)
    {rStar : Fin R} (hWrong : Y_claim rStar ≠ contract (X rStar) W) :
    uniformProb F (fun ρ => foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W) ≤
      ((R - 1 : ℕ) : ℝ) / Fintype.card F := by
  have hcard := loopFold_soundness_roots_le hR X W Y_claim hWrong Finset.univ
  have hconv :
      uniformProb F (fun ρ => foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W) =
        uniformProb F (fun ρ => ρ ∈ Finset.univ.filter
          (fun x => foldLoopOut x Y_claim = contract (foldLoopAct x X) W)) :=
    uniformProb_congr (fun x => by simp)
  rw [hconv, uniformProb_mem_finset]
  gcongr

/-- **Falsifier Tooth 4 (`loopFold_postChallenge_forgery_tooth`, `R = 3` `Inkling-2-Mini` Loop Count):**
Fiat–Shamir ordering (`commit Y^{(0)}, Y^{(1)}, Y^{(2)} BEFORE drawing ρ`) is load-bearing!
Over ANY `[CommRing α]`, if an adversary sees `ρ` before choosing `Y_forged` and sets
`Y_forged 0 = Y_true 0 - ρ • Δ`, `Y_forged 1 = Y_true 1 + Δ`, `Y_forged 2 = Y_true 2` for ANY
non-zero perturbation `Δ ≠ 0`:
1. Pass `1` is genuinely forged (`Y_forged 1 ≠ contract (X 1) W`), YET
2. `foldLoopOut ρ Y_forged = contract (foldLoopAct ρ X) W` holds **identically for EVERY `ρ`**! -/
theorem loopFold_postChallenge_forgery_tooth {α : Type} [CommRing α] {T K N : ℕ}
    (X : Fin 3 → Fin T → Fin K → α) (W : Fin K → Fin N → α)
    (Δ : Fin T → Fin N → α) (hΔ : Δ ≠ 0) (ρ : α) :
    let Y_forged : Fin 3 → Fin T → Fin N → α := fun r t j =>
      if r = 0 then contract (X 0) W t j - ρ * Δ t j
      else if r = 1 then contract (X 1) W t j + Δ t j
      else contract (X 2) W t j
    Y_forged 1 ≠ contract (X 1) W ∧
    foldLoopOut ρ Y_forged = contract (foldLoopAct ρ X) W := by
  intro Y_forged
  refine ⟨?_, ?_⟩
  · intro hEq
    apply hΔ
    funext t j
    have hij : contract (X 1) W t j + Δ t j = contract (X 1) W t j := by
      simpa [Y_forged] using congrFun (congrFun hEq t) j
    exact add_left_cancel (hij.trans (add_zero _).symm)
  · funext t j
    rw [← (loopedPass_eq_stackedEinsum X W ρ).2 t j]
    have hlhs :
        foldLoopOut ρ Y_forged t j =
          Y_forged 0 t j + ρ * Y_forged 1 t j + ρ ^ 2 * Y_forged 2 t j := by
      unfold foldLoopOut
      rw [Fin.sum_univ_three]
      simp [pow_zero, pow_one]
    have hrhs :
        (∑ r : Fin 3, ρ ^ (r : ℕ) * contract (X r) W t j) =
          contract (X 0) W t j + ρ * contract (X 1) W t j + ρ ^ 2 * contract (X 2) W t j := by
      rw [Fin.sum_univ_three]
      simp [pow_zero, pow_one]
    rw [hlhs, hrhs]
    have hy0 : Y_forged 0 t j = contract (X 0) W t j - ρ * Δ t j := rfl
    have hy1 : Y_forged 1 t j = contract (X 1) W t j + Δ t j := rfl
    have hy2 : Y_forged 2 t j = contract (X 2) W t j := rfl
    rw [hy0, hy1, hy2]
    ring

/-- **Sequential Depth-Looped Layer Trajectory (`loopTrajectory`):**
Models `thinkingmachines/Inkling-2-Mini`'s true recurrent depth loop (`X^{(0)} = X₀`,
`X^{(r + 1)} = stepPost (X^{(r)}) (contract (X^{(r)}) W)`, where `stepPost` applies residual
addition + RMSNorm/activation between loop passes) and proves `loopedPass_eq_stackedEinsum`
applies directly to the coupled `R`-step recurrent trajectory! -/
def loopTrajectory {α : Type} [Semiring α] {T K N : ℕ}
    (X₀ : Fin T → Fin K → α) (W : Fin K → Fin N → α)
    (stepPost : (Fin T → Fin K → α) → (Fin T → Fin N → α) → (Fin T → Fin K → α)) :
    ℕ → (Fin T → Fin K → α)
  | 0 => X₀
  | r + 1 =>
    let Xr := loopTrajectory X₀ W stepPost r
    stepPost Xr (contract Xr W)

theorem loopedTrajectory_fold_eq_single_contract {α : Type} [CommRing α] {R T K N : ℕ}
    (X₀ : Fin T → Fin K → α) (W : Fin K → Fin N → α)
    (stepPost : (Fin T → Fin K → α) → (Fin T → Fin N → α) → (Fin T → Fin K → α))
    (ρ : α) (t : Fin T) (j : Fin N) :
    let X_seq : Fin R → Fin T → Fin K → α := fun r => loopTrajectory X₀ W stepPost r.1
    (∑ r : Fin R, ρ ^ (r : ℕ) * contract (X_seq r) W t j) =
      contract (foldLoopAct ρ X_seq) W t j :=
  (loopedPass_eq_stackedEinsum _ W ρ).2 t j

/-- Concrete `ZMod 7` (`R = 3`) kernel-decided instance: a pre-committed forgery on pass `2`
with defect polynomial `(X - 2)(X - 3) ≡ 6 + 2X + X^2 (mod 7)` survives on **exactly `2 = R - 1`**
challenges (`{2, 3}`) out of `7`! -/
theorem loopFold_r3_sharp_two_roots_f7 :
    let X : Fin 3 → Fin 1 → Fin 1 → ZMod 7 := fun _ _ _ => 1
    let W : Fin 1 → Fin 1 → ZMod 7 := fun _ _ => 1
    let Y_claim : Fin 3 → Fin 1 → Fin 1 → ZMod 7 :=
      fun r _ _ => if r = 0 then 1 + 6 else if r = 1 then 1 + 2 else 1 + 1
    Y_claim 2 ≠ contract (X 2) W ∧
    (Finset.univ.filter (fun ρ : ZMod 7 =>
      foldLoopOut ρ Y_claim = contract (foldLoopAct ρ X) W)).card = 2 := by
  refine ⟨by decide, ?_⟩
  decide

end LoopedWeightCollapse

/-! ## Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.greedyTok_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms greedyTok_spec
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.greedyTok_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms greedyTok_unique
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.speculativePrefill_iff_greedyRollout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms speculativePrefill_iff_greedyRollout
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.speculativePrefill_firstDivergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms speculativePrefill_firstDivergence
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.isGreedyDom_iff_tieBrokenGap_nonneg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isGreedyDom_iff_tieBrokenGap_nonneg
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.zmod_gap_range_implies_isGreedyDom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod_gap_range_implies_isGreedyDom
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.tieBreak_omission_admits_canberra_drift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tieBreak_omission_admits_canberra_drift
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.causal_prefill_positive_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms causal_prefill_positive_witness
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.nonCausal_lookahead_breaks_prefill_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonCausal_lookahead_breaks_prefill_iff
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.mod_gap_without_range_forges_argmax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mod_gap_without_range_forges_argmax
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.mod_gap_without_headroom_forges_argmax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mod_gap_without_headroom_forges_argmax
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopedPass_eq_stackedEinsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopedPass_eq_stackedEinsum
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopedTrajectory_fold_eq_single_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopedTrajectory_fold_eq_single_contract
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.mle₂_loopFold_eq_single_matmulTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_loopFold_eq_single_matmulTable
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopFold_soundness_roots_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopFold_soundness_roots_le
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopFold_soundness_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopFold_soundness_prob_le
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopFold_postChallenge_forgery_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopFold_postChallenge_forgery_tooth
/-- info: 'Minidregg.Assurance.SpeculativePrefillAudit.loopFold_r3_sharp_two_roots_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loopFold_r3_sharp_two_roots_f7

end Minidregg.Assurance.SpeculativePrefillAudit
