/-
# Loom.Depth — [OB-2] depth composition: the audit finding and the proof tower.

Target: `OB2_depth_composition` (Loom/Rbr.lean), WARP (ePrint 2025/753) Thm B.4
via Construction B.5 + Claim B.6 + the union bound over the `t + k` unique
moves of the full trace.

**Audit finding first (teeth):** the audited statement is REFUTABLE, and this
file proves that (`OB2_depth_composition_false`). The hole is the degenerate
corner `Z = ∅`: the SR bad event's first conjunct `o.stmt ∈ Z` empties the
event, so its probability is `0`, while `εrbr` is constrained by the hypothesis
only ON `Z` — so `εrbr := fun _ => -1` satisfies the (vacuous) hypothesis and
the conclusion demands `0 ≤ (t + r.k) · (-1) < 0` (note `k_pos` forces
`t + k ≥ 1`). The paper never meets this corner: its `ε_rbr(δ)` is a `max` over
a tacitly-nonempty statement set of quantities each dominating a probability
(hence `≥ 0`). Specialization 7 of Loom/Rbr.lean ("`ε_rbr` as an arbitrary
uniform bound") opened the hole. The one-line repair is a nonnegativity guard
on `εrbr`; `OB2_depth_composition_nonneg` below is the repaired obligation, and
the rest of the file is its proof tower.

What lands here:
* elementary counting lemmas for `uniformProb` (monotonicity, finite union
  bound, product slicing, transport along equivalences) — no measure theory;
* `wAt`/`srExtract` — Construction B.5, the backwards straightline extractor
  (`w_k := w'`, `w_{i-1} := E_rbr(tr_i, w_i)`, output `w_0`);
* `RoundBad` — the per-move RBR bad event of Def 4.2's `extract_sound`;
* `exists_roundBad_of_event` — Claim B.6, deterministic and pointwise: on ANY
  coin outcome, if the verifier accepts with `w'` in `R'_{≤δ}` while the chain
  output fails `R_{≤δ}`, some slot `a ∈ [k]` fires the per-move bad event;
* the fresh/log-hit attribution of the `k` final-prefix moves to the `t + k`
  unique-move budget, and the closed probability bound for the FRESH slots;
* `OB2_depth_composition_false` — the machine-checked refutation;
* `OB2_depth_composition_nonneg` — the repaired [OB-2′] — assembled from all
  of the above by `OB2_nonneg_of_gameSlotBound`, conditional on exactly ONE
  named seam, `GameSlotBound` [OB-2a]: the per-game-slot probability bound,
  which in the lazy-sampling rendering is the standard deferred-decisions /
  random-oracle argument (see its doc comment and the ledger at the bottom).
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Loom.Rbr

namespace Minidregg.Loom

/-! ## Elementary counting toolkit for `uniformProb` -/

section UniformProb

variable {C : Type} [Fintype C]

/-- The counted set, as a `Nat.card` inequality against the whole space. -/
lemma card_le_of_subtype (p : C → Prop) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Fintype.card C : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_subtype_le p

lemma uniformProb_nonneg (p : C → Prop) : 0 ≤ uniformProb C p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma uniformProb_le_one (p : C → Prop) : uniformProb C p ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    calc (Nat.card {c : C // p c} : ℝ) / (Fintype.card C : ℝ)
        ≤ (Fintype.card C : ℝ) / (Fintype.card C : ℝ) := by
          gcongr
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_subtype_le p
      _ = 1 := div_self (ne_of_gt hpos')

lemma uniformProb_congr {p q : C → Prop} (h : ∀ c, p c ↔ q c) :
    uniformProb C p = uniformProb C q := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeEquivRight h)]

lemma uniformProb_false {p : C → Prop} (h : ∀ c, ¬ p c) :
    uniformProb C p = 0 := by
  unfold uniformProb
  have : IsEmpty {c : C // p c} := ⟨fun x => h x.1 x.2⟩
  rw [Nat.card_of_isEmpty]
  simp

/-- Monotone counting: pointwise implication gives a card inequality. -/
lemma card_mono_of_imp {p q : C → Prop} (h : ∀ c, p c → q c) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Nat.card {c : C // q c} : ℝ) := by
  classical
  have : Nat.card {c : C // p c} ≤ Nat.card {c : C // q c} :=
    Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)
  exact_mod_cast this

lemma uniformProb_mono {p q : C → Prop} (h : ∀ c, p c → q c) :
    uniformProb C p ≤ uniformProb C q := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    gcongr
    · exact Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)

/-- Counting form of `Pr[p ∨ q] ≤ Pr[p] + Pr[q]`. -/
lemma uniformProb_or_le (p q : C → Prop) :
    uniformProb C (fun c => p c ∨ q c) ≤ uniformProb C p + uniformProb C q := by
  classical
  unfold uniformProb
  rw [← add_div]
  have hle : Nat.card {c : C // p c ∨ q c} ≤
      Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
    have hunion : {c : C | p c ∨ q c} = {c : C | p c} ∪ {c : C | q c} := rfl
    calc Nat.card {c : C // p c ∨ q c}
        = ({c : C | p c} ∪ {c : C | q c} : Set C).ncard := by
          rw [← Nat.card_coe_set_eq, ← hunion]; rfl
      _ ≤ ({c : C | p c} : Set C).ncard + ({c : C | q c} : Set C).ncard :=
          Set.ncard_union_le _ _
      _ = Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; rfl
  gcongr
  exact_mod_cast hle

/-- The finite union bound over `Fin m` — the `Finset` card arithmetic behind
Thm B.4's "union bound over the at most `t + k` unique moves". -/
lemma uniformProb_exists_le : ∀ {m : ℕ} (p : Fin m → C → Prop),
    uniformProb C (fun c => ∃ i, p i c) ≤ ∑ i : Fin m, uniformProb C (p i) := by
  intro m
  induction m with
  | zero =>
    intro p
    rw [uniformProb_false (by rintro c ⟨i, -⟩; exact i.elim0)]
    simp
  | succ m ih =>
    intro p
    calc uniformProb C (fun c => ∃ i, p i c)
        = uniformProb C (fun c => p 0 c ∨ ∃ i : Fin m, p i.succ c) :=
          uniformProb_congr fun c => Fin.exists_fin_succ
      _ ≤ uniformProb C (p 0) + uniformProb C (fun c => ∃ i : Fin m, p i.succ c) :=
          uniformProb_or_le _ _
      _ ≤ uniformProb C (p 0) + ∑ i : Fin m, uniformProb C (p i.succ) := by
          have := ih (fun i => p i.succ)
          linarith
      _ = ∑ i : Fin (m + 1), uniformProb C (p i) :=
          (Fin.sum_univ_succ (fun i => uniformProb C (p i))).symm

/-- Transport along an equivalence: `uniformProb` only counts. -/
lemma uniformProb_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B)
    (p : B → Prop) : uniformProb A (fun a => p (e a)) = uniformProb B p := by
  unfold uniformProb
  rw [Nat.card_congr (e.subtypeEquiv fun a => Iff.rfl), Fintype.card_congr e]

/-- Product slicing: if every fibre over the first coordinate has conditional
probability at most `ε`, so does the whole event. The counting rendering of
"condition on everything but the fresh coin". -/
lemma uniformProb_prod_le {A B : Type} [Fintype A] [Fintype B]
    {p : A × B → Prop} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a, uniformProb B (fun b => p (a, b)) ≤ ε) :
    uniformProb (A × B) p ≤ ε := by
  classical
  unfold uniformProb at *
  rcases Nat.eq_zero_or_pos (Fintype.card B) with hB0 | hBpos
  · have hAB : Fintype.card (A × B) = 0 := by simp [Fintype.card_prod, hB0]
    simp [hAB, hε]
  rcases Nat.eq_zero_or_pos (Fintype.card A) with hA0 | hApos
  · have hAB : Fintype.card (A × B) = 0 := by simp [Fintype.card_prod, hA0]
    simp [hAB, hε]
  have hBpos' : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast hBpos
  have hABpos : (0 : ℝ) < (Fintype.card (A × B) : ℝ) := by
    rw [Fintype.card_prod]
    exact_mod_cast Nat.mul_pos hApos hBpos
  -- fibrewise decomposition of the counted set
  have hsplit : Nat.card {x : A × B // p x} =
      ∑ a : A, Nat.card {b : B // p (a, b)} := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_congr
      (⟨fun x => ⟨x.1.1, ⟨x.1.2, by cases x with | mk v hv => exact hv⟩⟩,
        fun s => ⟨(s.1, s.2.1), s.2.2⟩,
        fun x => by cases x with | mk v hv => rfl,
        fun s => rfl⟩ :
        {x : A × B // p x} ≃ (a : A) × {b : B // p (a, b)})]
    rw [Fintype.card_sigma]
    simp [Nat.card_eq_fintype_card]
  have hfib : ∀ a : A, (Nat.card {b : B // p (a, b)} : ℝ) ≤
      ε * Fintype.card B := by
    intro a
    have ha := h a
    rw [div_le_iff₀ hBpos'] at ha
    exact ha
  rw [div_le_iff₀ hABpos, hsplit, Nat.cast_sum]
  calc (∑ a : A, (Nat.card {b : B // p (a, b)} : ℝ))
      ≤ ∑ _a : A, ε * (Fintype.card B : ℝ) := Finset.sum_le_sum fun a _ => hfib a
    _ = (Fintype.card A : ℝ) * (ε * (Fintype.card B : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ε * ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := mul_left_comm _ _ _
    _ = ε * (Fintype.card (A × B) : ℝ) := by
        rw [Fintype.card_prod, Nat.cast_mul]

end UniformProb

/-! ## Splitting one coordinate out of a tuple of coins

Hand-rolled (rather than `Equiv.funSplitAt`) so the `symm` direction reduces
definitionally at both the split coordinate and the others. -/

/-- Split coordinate `i` out of a `Fin n`-indexed tuple. -/
def splitCoord {n : ℕ} {β : Type} (i : Fin n) :
    (Fin n → β) ≃ (({j : Fin n // j ≠ i} → β) × β) where
  toFun f := (fun j => f j.1, f i)
  invFun x j := if h : j = i then x.2 else x.1 ⟨j, h⟩
  left_inv f := by
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [j.2]
    · simp

@[simp] lemma splitCoord_symm_apply_self {n : ℕ} {β : Type} (i : Fin n)
    (x : ({j : Fin n // j ≠ i} → β) × β) : (splitCoord i).symm x i = x.2 := by
  simp [splitCoord]

@[simp] lemma splitCoord_symm_apply_ne {n : ℕ} {β : Type} {i j : Fin n}
    (h : j ≠ i) (x : ({j : Fin n // j ≠ i} → β) × β) :
    (splitCoord i).symm x j = x.1 ⟨j, h⟩ := by
  simp [splitCoord, h]

/-! ## Construction B.5 — the backwards straightline extractor -/

section Extractor

variable {r : Reduction}

/-- The Construction B.5 witness chain, indexed from the top:
`wAt rbr st rounds w' i` is `w_i`, with `w_i := w'` for `i ≥ rounds.length`
(the seed `w_k := w'` — the prover's own target-relation candidate) and
`w_i := E_rbr(st, tr_{i+1}, w_{i+1})` below it, where `tr_{i+1}` is the
transcript of the first `i + 1` completed rounds. The extractor outputs
`w_0`. -/
def wAt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) (i : ℕ) : r.W :=
  if h : rounds.length ≤ i then w'
  else rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1))
  termination_by rounds.length - i
  decreasing_by omega

lemma wAt_of_le (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) {i : ℕ}
    (h : rounds.length ≤ i) : wAt rbr st rounds w' i = w' := by
  unfold wAt
  simp [h]

lemma wAt_of_lt (rbr : RbrKnowledgeSoundness r) (st : Stmt r)
    (rounds : List (r.PMsg × r.Chal)) (w' : r.W) {i : ℕ}
    (h : i < rounds.length) :
    wAt rbr st rounds w' i =
      rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1)) := by
  conv_lhs => unfold wAt
  simp [Nat.not_le.mpr h]

/-- **Construction B.5**: the straightline state-restoration extractor. It
reads only the output statement, the prover messages, the candidate witness
`w'`, and the final challenges — the game trace argument is unused, exactly as
in the paper. `w_k := w'`; `w_{i-1} := E_rbr(𝕚, 𝕩, 𝕪, (π₁,ρ₁,…,π_i,ρ_i), w_i)`;
output `w_0`. -/
def srExtract (rbr : RbrKnowledgeSoundness r) (s : ℕ) : SrExtractor r s :=
  fun o ρs _log => wAt rbr o.stmt (List.ofFn fun i => (o.πs i, ρs i)) o.w' 0

/-! ## The per-move RBR bad event, and Claim B.6 -/

/-- The per-move RBR bad event — the event of Def 4.2's `extract_sound`, as a
predicate of the prefix `rs`, the pending prover message `π`, and the fresh
challenge `ρ`: SOME knowledge-state witness survives at the extended transcript
while the round extractor's output dies at the shorter one. -/
def RoundBad (rbr : RbrKnowledgeSoundness r) (δ : ℝ) (st : Stmt r)
    (rs : List (r.PMsg × r.Chal)) (π : r.PMsg) (ρ : r.Chal) : Prop :=
  ∃ w : r.W,
    rbr.kstate.state δ st ⟨rs, some π⟩
      (rbr.extract st ⟨rs ++ [(π, ρ)], none⟩ w) = false ∧
    rbr.kstate.state δ st ⟨rs ++ [(π, ρ)], none⟩ w = true

/-- Def 4.2's round bound, re-stated against `RoundBad`. -/
lemma uniformProb_roundBad_le (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r) (i : Fin r.k)
    {rs : List (r.PMsg × r.Chal)} (hlen : rs.length = (i : ℕ)) (π : r.PMsg) :
    uniformProb r.Chal (RoundBad rbr δ st rs π) ≤ rbr.err i st δ :=
  rbr.extract_sound δ hδ st i rs hlen π

/-- Per-round knowledge errors are nonnegative on the paper's `δ` range: each
dominates a `uniformProb` (Def 4.2 at any prefix of the right length). This is
why the paper never needs the nonnegativity guard explicitly — and why the
repaired [OB-2′] guard is free for every nonempty `Z`
(`εrbr_nonneg_of_nonempty`). -/
lemma err_nonneg (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (i : Fin r.k) (st : Stmt r) :
    0 ≤ rbr.err i st δ := by
  obtain ⟨π₀⟩ := r.pmsgNonempty
  obtain ⟨ρ₀⟩ := r.chalNonempty
  exact le_trans (uniformProb_nonneg _)
    (rbr.extract_sound δ hδ st i (List.replicate (i : ℕ) (π₀, ρ₀))
      (List.length_replicate) π₀)

/-- For nonempty `Z`, any uniform bound on the per-round errors over `Z` is
automatically nonnegative on `δ ∈ (0, δ*)` — the repaired [OB-2′] guard costs
nothing outside the refutable `Z = ∅` corner. -/
lemma εrbr_nonneg_of_nonempty (rbr : RbrKnowledgeSoundness r)
    {Z : Set (Stmt r)} (hZ : Z.Nonempty) {εrbr : ℝ → ℝ}
    (hdom : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ := by
  intro δ hδ
  obtain ⟨st, hst⟩ := hZ
  exact le_trans (err_nonneg rbr hδ ⟨0, r.k_pos⟩ st)
    (hdom ⟨0, r.k_pos⟩ st hst δ hδ)

/-- **Claim B.6, the backwards descent** (deterministic, pointwise). From a
knowledge-state witness alive at level `i` of the chain, either some completed
round `a` fires the per-move bad event (with the chain witness `w_{a+1}` as the
existential witness), or the chain walks all the way down and `w_0` is alive at
the empty transcript. Uses `prover_monotone` at every step — the one clause of
Def 4.1 the union bound leans on. -/
lemma chain_descend (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r)
    {rounds : List (r.PMsg × r.Chal)} (hlen : rounds.length = r.k) (w' : r.W) :
    ∀ i : ℕ, i ≤ r.k →
      rbr.kstate.state δ st ⟨rounds.take i, none⟩ (wAt rbr st rounds w' i) = true →
      (∃ (a : Fin r.k) (π : r.PMsg) (ρ : r.Chal),
          rounds[(a : ℕ)]? = some (π, ρ) ∧
          RoundBad rbr δ st (rounds.take (a : ℕ)) π ρ) ∨
        rbr.kstate.state δ st ⟨rounds.take 0, none⟩ (wAt rbr st rounds w' 0) = true := by
  intro i
  induction i with
  | zero => exact fun _ h0 => Or.inr h0
  | succ i ih =>
    intro hik htrue
    have hi : i < rounds.length := by omega
    have hik' : i ≤ r.k := by omega
    have htake : rounds.take (i + 1) = rounds.take i ++ [rounds[i]'hi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    have hw : wAt rbr st rounds w' i =
        rbr.extract st ⟨rounds.take (i + 1), none⟩ (wAt rbr st rounds w' (i + 1)) :=
      wAt_of_lt rbr st rounds w' hi
    cases hval : rbr.kstate.state δ st ⟨rounds.take i, some (rounds[i]'hi).1⟩
        (wAt rbr st rounds w' i) with
    | false =>
      -- the per-move bad event fires at slot `i`, witnessed by `w_{i+1}`
      refine Or.inl ⟨⟨i, by omega⟩, (rounds[i]'hi).1, (rounds[i]'hi).2,
        by rw [List.getElem?_eq_getElem hi], ⟨wAt rbr st rounds w' (i + 1), ?_, ?_⟩⟩
      · rw [← htake, ← hw]
        exact hval
      · rw [← htake]
        exact htrue
    | true =>
      -- prover monotonicity walks the truth down past the pending message
      have hlt : (rounds.take i).length < r.k := by
        rw [List.length_take]
        omega
      have hmon := rbr.kstate.prover_monotone δ hδ st (rounds.take i)
        (wAt rbr st rounds w' i) hlt
      cases h0 : rbr.kstate.state δ st ⟨rounds.take i, none⟩
          (wAt rbr st rounds w' i) with
      | false =>
        have := hmon h0 (rounds[i]'hi).1
        rw [hval] at this
        exact absurd this (by simp)
      | true => exact ih hik' h0

/-- **Claim B.6** (pointwise): on ANY outcome where the verifier accepts the
full transcript with the prover's candidate `w'` in `R'_{≤δ}` while the
Construction B.5 output `w_0` fails `R_{≤δ}`, some slot `a ∈ [k]` fires the
per-move bad event at the length-`a` prefix of the final transcript. -/
lemma exists_roundBad_of_event (rbr : RbrKnowledgeSoundness r) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r)
    (πs : Fin r.k → r.PMsg) (ρs : Fin r.k → r.Chal) (w' : r.W)
    (hacc : ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
      r.verify st.idx st.x st.y πs ρs = some (x', y') ∧
      RelaxedMem r.R' δ st.idx x' y' w')
    (hfail : ¬ RelaxedMem r.R δ st.idx st.x st.y
      (wAt rbr st (List.ofFn fun i => (πs i, ρs i)) w' 0)) :
    ∃ a : Fin r.k,
      RoundBad rbr δ st ((List.ofFn fun i => (πs i, ρs i)).take (a : ℕ))
        (πs a) (ρs a) := by
  set rounds := List.ofFn fun i => (πs i, ρs i) with hrounds
  have hlen : rounds.length = r.k := by simp [hrounds]
  have htop : rbr.kstate.state δ st ⟨rounds.take r.k, none⟩
      (wAt rbr st rounds w' r.k) = true := by
    rw [wAt_of_le rbr st rounds w' (le_of_eq hlen), ← hlen, List.take_length]
    exact (rbr.kstate.full_iff δ hδ st πs ρs w').mpr hacc
  rcases chain_descend rbr hδ st hlen w' r.k (le_refl _) htop with
    ⟨a, π, ρ, hget, hbad⟩ | h0
  · have hgetfn : rounds[(a : ℕ)]? = some (πs a, ρs a) := by
      rw [hrounds]
      rw [List.getElem?_eq_getElem (by simp [a.isLt])]
      simp
    rw [hgetfn] at hget
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj hget
    exact ⟨a, h1.symm ▸ h2.symm ▸ hbad⟩
  · have h0' : rbr.kstate.state δ st Transcript.empty
        (wAt rbr st rounds w' 0) = true := by
      simpa [Transcript.empty] using h0
    exact absurd ((rbr.kstate.empty_iff δ hδ st (wAt rbr st rounds w' 0)).mp h0')
      hfail

end Extractor

/-! ## Teeth: the audited [OB-2] statement is refutable

`OB2_depth_composition` quantifies over ALL statement sets `Z` and ALL bound
functions `εrbr`, constraining `εrbr` only ON `Z`. At `Z = ∅` the hypothesis is
vacuous, so `εrbr := fun _ => -1` qualifies — and the conclusion then demands
`Pr[..] ≤ (t + k) · (-1) < 0` (`k_pos` forces `t + k ≥ 1`), against a
probability that is nonnegative by construction. Any single inhabited
`Reduction` + `RbrKnowledgeSoundness` pair therefore refutes the statement; we
exhibit the smallest one. The paper never meets this corner: its
`ε_rbr(δ) = max_{i,(𝕚,𝕩,𝕪) ∈ Z} ε_i ` is a max over a tacitly nonempty `Z` of
quantities that each dominate a probability (Def 4.2), hence are `≥ 0`.
Specialization 7 of Loom/Rbr.lean (arbitrary uniform bound in place of the max)
opened the hole; `OB2_depth_composition_nonneg` below is the one-guard
repair. -/

section Teeth

/-- `Δ(u, u) = 0` — the disagreement set of a word with itself is empty. -/
lemma fracHamming_self {A : Type} {n : ℕ} (u : Fin n → A) :
    fracHamming u u = 0 := by
  unfold fracHamming
  have : IsEmpty {i : Fin n // u i ≠ u i} := ⟨fun x => x.2 rfl⟩
  rw [Nat.card_of_isEmpty]
  simp

/-- The smallest `Reduction`: all types `Unit`, one round, boolean challenges,
both relations `True`, verifier always accepting. -/
def trivialReduction : Reduction where
  Idx := Unit
  X := Unit
  A := Unit
  X' := Unit
  A' := Unit
  W := Unit
  n := 1
  n' := 1
  n_pos := one_pos
  n'_pos := one_pos
  R := fun _ _ _ _ => True
  R' := fun _ _ _ _ => True
  k := 1
  k_pos := one_pos
  PMsg := Unit
  Chal := Bool
  pmsgNonempty := ⟨()⟩
  chalFintype := inferInstance
  chalNonempty := ⟨true⟩
  δstar := 1
  δstar_pos := one_pos
  δstar_le_one := le_refl 1
  verify := fun _ _ _ _ _ => some ((), fun _ => ())

/-- The constant-`true` knowledge state function for `trivialReduction`:
both relations are `True`, so every clause of Def 4.1 is satisfied. -/
def trivialKState : KStateFn trivialReduction where
  state := fun _ _ _ _ => true
  empty_iff := by
    intro δ hδ st w
    refine ⟨fun _ => ⟨st.y, trivial, ?_⟩, fun _ => rfl⟩
    rw [fracHamming_self]
    exact le_of_lt hδ.1
  prover_monotone := by
    intro δ hδ st rs w hlen h
    simp at h
  full_iff := by
    intro δ hδ st πs ρs w
    refine ⟨fun _ => ⟨(), fun _ => (), rfl, ⟨fun _ => (), trivial, ?_⟩⟩,
      fun _ => rfl⟩
    rw [fracHamming_self]
    exact le_of_lt hδ.1

/-- RBR knowledge soundness for `trivialReduction`, with error `1` — every
probability is at most `1`. -/
def trivialRbr : RbrKnowledgeSoundness trivialReduction where
  kstate := trivialKState
  extract := fun _ _ w => w
  err := fun _ _ _ => 1
  extractTime := fun _ => 0
  extract_sound := by
    intro δ hδ st i rs hlen π
    exact uniformProb_le_one _

/-- A statement of the trivial reduction. -/
def trivialStmt : Stmt trivialReduction := ⟨(), (), fun _ => ()⟩

/-- The do-nothing state-restoration prover at salt size 0. -/
def trivialProver : SrProver trivialReduction 0 where
  move := fun _ => ⟨trivialStmt, []⟩
  out := fun _ => ⟨trivialStmt, fun _ => (), fun _ => Fin.elim0, ()⟩

/-- **The audited [OB-2] statement is FALSE.** Instantiate at `Z = ∅`,
`εrbr = -1` (the hypothesis is vacuous off `Z`), move budget `t = 0`: the
claimed bound is `(0 + 1) · (-1) = -1`, but `uniformProb` is nonnegative.
The repaired obligation is `OB2_depth_composition_nonneg` below. -/
theorem OB2_depth_composition_false : ¬ OB2_depth_composition := by
  intro h
  obtain ⟨E, hE⟩ := h trivialReduction trivialRbr ∅ (fun _ => -1)
    (fun i st hst => ((Set.mem_empty_iff_false st).mp hst).elim)
  have hbound := hE 0 0 (1 / 2)
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 2 < (1 : ℝ); norm_num⟩)
    trivialProver
  have hcontra := le_trans (uniformProb_nonneg _) hbound
  norm_num [show trivialReduction.k = 1 from rfl] at hcontra

end Teeth

/-! ## The state-restoration side: naming the moving parts

`srTrace`/`srFinalChal` are fixed by the audited statement; here we name the
derived objects the proof walks over: the adversary's output `srOut`, the final
full-transcript rounds `srRounds`, and — for each final-prefix slot `a ∈ [k]` —
whether its lazily-sampled response was FRESH (`find?` misses the trace: the
response is the coin `d a`) or a LOG HIT (first answered at game move `j`).
This is exactly Thm B.4's attribution of the `k` output-prefix moves to the
`t + k` unique moves of the full trace. -/

section StateRestoration

open Classical

variable {r : Reduction} {s t : ℕ}

/-- The adversary's final output on game coins `c` (Def B.1, step 2) — the
`o := P.out (log.map Prod.snd)` of the audited event, named. -/
noncomputable def srOut (P : SrProver r s) (c : Fin t → r.Chal) : SrOutput r s :=
  P.out ((srTrace P c).map Prod.snd)

/-- The final full-transcript rounds `(π_i, ρ_i)_{i ∈ [k]}` on coins `(c, d)`. -/
noncomputable def srRounds (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) : List (r.PMsg × r.Chal) :=
  List.ofFn fun i => ((srOut P c).πs i, srFinalChal P c d i)

/-- `srFinalChal`, unfolded against the named `srOut`. -/
lemma srFinalChal_def (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k) :
    srFinalChal P c d i =
      match (srTrace P c).find?
          (fun e => decide (e.1 = (srOut P c).query i)) with
      | some e => e.2
      | none => d i := rfl

/-- A never-queried final prefix is answered by its own fresh coin. -/
lemma srFinalChal_of_none (P : SrProver r s) (c : Fin t → r.Chal)
    (d : Fin r.k → r.Chal) (i : Fin r.k)
    (h : (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query i)) =
      none) : srFinalChal P c d i = d i := by
  rw [srFinalChal_def, h]

/-- `srFinalChal P c d i` reads `d` only at index `i`. -/
lemma srFinalChal_congr (P : SrProver r s) (c : Fin t → r.Chal)
    {d d' : Fin r.k → r.Chal} (i : Fin r.k) (h : d i = d' i) :
    srFinalChal P c d i = srFinalChal P c d' i := by
  cases hf : (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query i)) with
  | some e => rw [srFinalChal_def, srFinalChal_def, hf]
  | none => rw [srFinalChal_def, srFinalChal_def, hf, h]

/-- Auxiliary: a fold that appends one entry per step grows by the step
count. -/
lemma foldl_length_aux {α β : Type} (f : List α → β → List α)
    (hf : ∀ L b, (f L b).length = L.length + 1) :
    ∀ (js : List β) (L : List α), (js.foldl f L).length = L.length + js.length := by
  intro js
  induction js with
  | nil => intro L; simp
  | cons j js ih =>
    intro L
    rw [List.foldl_cons, ih, hf]
    simp only [List.length_cons]
    omega

/-- The game trace records exactly `t` move–response pairs (repeats
included). -/
lemma srTrace_length (P : SrProver r s) (c : Fin t → r.Chal) :
    (srTrace P c).length = t := by
  unfold srTrace
  rw [foldl_length_aux _ ?_ _ _]
  · simp
  · intro L j
    dsimp only
    simp

/-- `find?` hit gives a first-occurrence index (within the list length). -/
lemma exists_findIdx?_of_find? {α : Type} (p : α → Bool) :
    ∀ (l : List α) (e : α), l.find? p = some e →
      ∃ n : ℕ, l.findIdx? p = some n ∧ n < l.length := by
  intro l
  induction l with
  | nil => intro e h; simp at h
  | cons x l ih =>
    intro e h
    by_cases hpx : p x
    · exact ⟨0, by simp [List.findIdx?_cons, hpx], by simp⟩
    · rw [List.find?_cons_of_neg (by simpa using hpx)] at h
      obtain ⟨n, hn, hlt⟩ := ih e h
      refine ⟨n + 1, ?_, by simp; omega⟩
      rw [List.findIdx?_cons]
      simp [hpx, hn]

/-! ### The union-cover events -/

/-- The per-slot bad event at final-prefix slot `a`: the output statement lands
in `Z` and the per-move RBR bad event fires at the length-`a` prefix of the
final transcript, with pending message `π_{a+1}` and response `ρ_{a+1}`. -/
def slotBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (a : Fin r.k)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  (srOut P ω.1).stmt ∈ Z ∧
  RoundBad rbr δ (srOut P ω.1).stmt ((srRounds P ω.1 ω.2).take (a : ℕ))
    ((srOut P ω.1).πs a) (srFinalChal P ω.1 ω.2 a)

/-- Slot `a`'s final-prefix query was never made during the game: its response
is the fresh coin `d a`. -/
def freshAt (P : SrProver r s) (a : Fin r.k) (c : Fin t → r.Chal) : Prop :=
  (srTrace P c).find? (fun e => decide (e.1 = (srOut P c).query a)) = none

/-- Slot `a`'s final-prefix query WAS made during the game, first at move `j`:
its response is the coin that answered move `j`. -/
def hitAt (P : SrProver r s) (a : Fin r.k) (j : Fin t)
    (c : Fin t → r.Chal) : Prop :=
  (srTrace P c).findIdx? (fun e => decide (e.1 = (srOut P c).query a)) =
    some (j : ℕ)

/-- Cover event, fresh side: slot `a` fires and its response coin `d a` is
fresh — one of the `k` "output prefix" unique moves of Thm B.4. -/
def FreshBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (a : Fin r.k)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  freshAt P a ω.1 ∧ slotBad rbr Z δ P a ω

/-- Cover event, log-hit side: SOME slot fires whose response was first
sampled at game move `j` — one of the `t` "game move" unique moves of
Thm B.4. -/
def HitBad (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) (δ : ℝ)
    (P : SrProver r s) (j : Fin t)
    (ω : (Fin t → r.Chal) × (Fin r.k → r.Chal)) : Prop :=
  ∃ a : Fin r.k, hitAt P a j ω.1 ∧ slotBad rbr Z δ P a ω

/-- **The pointwise cover** (Claim B.6 + unique-move attribution): every
outcome in the Def B.2 bad event lies in some `FreshBad a` or some
`HitBad j`. -/
lemma cover (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (P : SrProver r s) :
    ∀ ω : (Fin t → r.Chal) × (Fin r.k → r.Chal),
      ((srOut P ω.1).stmt ∈ Z ∧
        ¬ RelaxedMem r.R δ (srOut P ω.1).stmt.idx (srOut P ω.1).stmt.x
          (srOut P ω.1).stmt.y
          (srExtract rbr s (srOut P ω.1) (srFinalChal P ω.1 ω.2)
            (srTrace P ω.1)) ∧
        ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
          r.verify (srOut P ω.1).stmt.idx (srOut P ω.1).stmt.x
            (srOut P ω.1).stmt.y (srOut P ω.1).πs (srFinalChal P ω.1 ω.2) =
            some (x', y') ∧
          RelaxedMem r.R' δ (srOut P ω.1).stmt.idx x' y' (srOut P ω.1).w') →
      (∃ a : Fin r.k, FreshBad rbr Z δ P a ω) ∨
        (∃ j : Fin t, HitBad rbr Z δ P j ω) := by
  rintro ω ⟨hz, hfail, hacc⟩
  obtain ⟨a, hbad⟩ := exists_roundBad_of_event rbr hδ (srOut P ω.1).stmt
    (srOut P ω.1).πs (srFinalChal P ω.1 ω.2) (srOut P ω.1).w' hacc hfail
  cases hfind : (srTrace P ω.1).find?
      (fun e => decide (e.1 = (srOut P ω.1).query a)) with
  | none => exact Or.inl ⟨a, hfind, hz, hbad⟩
  | some e =>
    obtain ⟨n, hn, hlt⟩ := exists_findIdx?_of_find? _ _ _ hfind
    rw [srTrace_length] at hlt
    exact Or.inr ⟨⟨n, hlt⟩, a, hn, hz, hbad⟩

/-! ### The fresh-slot bound -/

/-- **The fresh-slot bound**: `Pr[FreshBad a] ≤ εrbr δ`. Counting rendering of
the easy half of Thm B.4's per-unique-move argument: condition on everything
except the fresh coin `d a` (the trace, the output, the pending message, and
the earlier final challenges are all determined by the other coordinates), and
the response at slot `a` IS `d a` — Def 4.2's round bound applies with fixed
statement, prefix, and pending message. -/
lemma freshBad_le (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r)) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) {εrbr : ℝ → ℝ} (hnn : 0 ≤ εrbr δ)
    (hdom : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → rbr.err i st δ ≤ εrbr δ)
    (P : SrProver r s) (a : Fin r.k) :
    uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
      (FreshBad rbr Z δ P a) ≤ εrbr δ := by
  classical
  -- move the fresh coin `d a` out as the last product coordinate
  have hsplit : uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
      (FreshBad rbr Z δ P a) =
      uniformProb (((Fin t → r.Chal) × ({j : Fin r.k // j ≠ a} → r.Chal)) ×
          r.Chal)
        (fun x => FreshBad rbr Z δ P a
          (x.1.1, (splitCoord a).symm (x.1.2, x.2))) :=
    (uniformProb_equiv
      ((((Equiv.refl (Fin t → r.Chal)).prodCongr (splitCoord a)).trans
        (Equiv.prodAssoc _ _ _).symm).symm)
      (FreshBad rbr Z δ P a)).symm
  rw [hsplit]
  apply uniformProb_prod_le hnn
  intro ω₁
  by_cases hf : freshAt P a ω₁.1
  swap
  · rw [uniformProb_false (by rintro ρ ⟨hfr, -⟩; exact hf hfr)]
    exact hnn
  by_cases hz : (srOut P ω₁.1).stmt ∈ Z
  swap
  · rw [uniformProb_false (by rintro ρ ⟨-, hzz, -⟩; exact hz hzz)]
    exact hnn
  obtain ⟨ρ₀⟩ := r.chalNonempty
  -- the earlier rounds are independent of the split coordinate
  have hRS : ∀ ρ : r.Chal,
      (srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ))).take (a : ℕ) =
      (srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ) := by
    intro ρ
    apply List.ext_getElem
    · simp [srRounds]
    · intro i h1 h2
      have hia : i < (a : ℕ) := by
        simpa [srRounds] using h1
      simp only [srRounds, List.getElem_take, List.getElem_ofFn]
      refine congrArg _ (srFinalChal_congr P _ _ ?_)
      have hne : (⟨i, by omega⟩ : Fin r.k) ≠ a := by
        intro hcontra
        have := congrArg Fin.val hcontra
        simp at this
        omega
      rw [splitCoord_symm_apply_ne hne, splitCoord_symm_apply_ne hne]
  -- the response at slot `a` is exactly the split coordinate
  have hresp : ∀ ρ : r.Chal,
      srFinalChal P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ)) a = ρ := by
    intro ρ
    rw [srFinalChal_of_none P _ _ _ hf]
    simp
  have hlen : ((srRounds P ω₁.1
      ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ)).length = (a : ℕ) := by
    simp [srRounds]
  calc uniformProb r.Chal (fun ρ => FreshBad rbr Z δ P a
        (ω₁.1, (splitCoord a).symm (ω₁.2, ρ)))
      = uniformProb r.Chal (RoundBad rbr δ (srOut P ω₁.1).stmt
          ((srRounds P ω₁.1 ((splitCoord a).symm (ω₁.2, ρ₀))).take (a : ℕ))
          ((srOut P ω₁.1).πs a)) := by
        apply uniformProb_congr
        intro ρ
        constructor
        · rintro ⟨-, -, hb⟩
          rw [hresp ρ, hRS ρ] at hb
          exact hb
        · intro hb
          refine ⟨hf, hz, ?_⟩
          rw [hresp ρ, hRS ρ]
          exact hb
    _ ≤ rbr.err a (srOut P ω₁.1).stmt δ :=
        uniformProb_roundBad_le rbr hδ _ a hlen _
    _ ≤ εrbr δ := hdom a _ hz

end StateRestoration

/-! ## The repaired obligation, the remaining seam, and the assembly -/

/-- **[OB-2′] Loss-free depth composition, repaired** (WARP 2025/753, Thm B.4):
identical to the audited `OB2_depth_composition` EXCEPT for one added guard,
`0 ≤ εrbr δ` on the quantified range — the guard whose absence makes the
original refutable (`OB2_depth_composition_false`). For nonempty `Z` the guard
is free: `εrbr` dominates some `err i st δ`, which dominates a `uniformProb`,
hence is nonnegative. The paper's `ε_rbr := max_{i, Z} ε_i` always satisfies it
whenever the max exists. -/
def OB2_depth_composition_nonneg : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ),
    (∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, 0 ≤ εrbr δ) →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      ∀ δ ∈ Set.Ioo (0 : ℝ) r.δstar, rbr.err i st δ ≤ εrbr δ) →
    StraightlineSrKnowledgeSoundness r Z
      (fun _s t δ => ((t : ℝ) + (r.k : ℝ)) * εrbr δ)

/-- **OBLIGATION [OB-2a] — the game-slot bound, the one remaining seam.**

`Pr[HitBad j] ≤ εrbr δ`: if the bad slot's final-prefix query was first made
at game move `j`, the response coin `c j` was fresh AT MOVE `j` — the move
(hence the statement, the prover messages, and the pending message) is a
function of the coins `c_{<j}` alone, and Def 4.2's round bound should apply
just as in the fresh case.

What makes this the hard half — and why it is named rather than closed here —
is the lazy-sampling rendering of the game (Loom/Rbr.lean, specialization 5):
the earlier chain challenges `ρ_1 … ρ_{a-1}` are `srFinalChal` values, i.e.
EVENTUAL responses read off the final log, and the continuation of the game
after move `j` (hence which coin eventually answers each earlier prefix) does
depend on `c j`. In the paper's eager formulation (`rnd` a total random
function) the independence is immediate: `rnd(move)` is independent of
`rnd` at every other point, which is where Thm B.4's proof says "the prover's
output is independent of the response". Lazily, the same fact is the standard
principle-of-deferred-decisions argument — the joint distribution of
(fresh response at move `j`; eventual responses to any fixed family of
distinct other queries) is uniform, because each is read from a distinct coin
coordinate whose index is settled before the coin is read. This is precisely
the "standard random-oracle argument" that Loom/Rbr.lean's specialization 5
already defers for the game/uniform-function equivalence; it is a counting
induction over the trace fold, not a new probabilistic idea. Closing it means:
(i) an induction over `srTrace`'s fold showing the eventual-response vector at
fixed distinct queries is uniform conditional on any coin prefix, and
(ii) the fibrewise assembly `Σ_h Σ_v` against `extract_sound` as in
`freshBad_le`. -/
def GameSlotBound : Prop :=
  ∀ (r : Reduction) (rbr : RbrKnowledgeSoundness r) (Z : Set (Stmt r))
    (εrbr : ℝ → ℝ) (δ : ℝ), δ ∈ Set.Ioo (0 : ℝ) r.δstar →
    0 ≤ εrbr δ →
    (∀ (i : Fin r.k) (st : Stmt r), st ∈ Z → rbr.err i st δ ≤ εrbr δ) →
    ∀ (s t : ℕ) (P : SrProver r s) (j : Fin t),
      uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal))
        (HitBad rbr Z δ P j) ≤ εrbr δ

/-- **Thm B.4, assembled**: the repaired [OB-2′] holds given the game-slot
bound [OB-2a]. Everything else is closed: Construction B.5 (`srExtract`),
Claim B.6 (`exists_roundBad_of_event`), the fresh/log-hit attribution
(`cover`), the fresh-slot bound (`freshBad_le`), and the
`k · ε + t · ε = (t + k) · ε` union-bound arithmetic. -/
theorem OB2_nonneg_of_gameSlotBound (H : GameSlotBound) :
    OB2_depth_composition_nonneg := by
  intro r rbr Z εrbr hnn hdom
  refine ⟨fun s => srExtract rbr s, ?_⟩
  intro s t δ hδ P
  have hnnδ : 0 ≤ εrbr δ := hnn δ hδ
  have hdomδ : ∀ (i : Fin r.k) (st : Stmt r), st ∈ Z →
      rbr.err i st δ ≤ εrbr δ := fun i st hst => hdom i st hst δ hδ
  refine le_trans (uniformProb_mono (cover rbr Z hδ P)) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  refine le_trans (add_le_add
    (uniformProb_exists_le fun a => FreshBad rbr Z δ P a)
    (uniformProb_exists_le fun j => HitBad rbr Z δ P j)) ?_
  refine le_trans (add_le_add
    (Finset.sum_le_sum fun a _ => freshBad_le rbr Z hδ hnnδ hdomδ P a)
    (Finset.sum_le_sum fun j _ =>
      H r rbr Z εrbr δ hδ hnnδ hdomδ s t P j)) ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-! ## Ledger

* `OB2_depth_composition_false` — **PROVED**: the audited [OB-2] statement is
  refutable (`Z = ∅`, `εrbr = -1`, `t = 0`; the sign of the claimed bound).
* `OB2_depth_composition_nonneg` — **[OB-2′]**, the one-guard repair
  (`0 ≤ εrbr δ`); free for nonempty `Z` (`εrbr_nonneg_of_nonempty`, itself
  backed by `err_nonneg`).
* `srExtract` — Construction B.5, **DEFINED** (backwards chain `wAt`).
* `exists_roundBad_of_event` — Claim B.6, **PROVED** deterministically and
  pointwise (via `chain_descend`; the only Def 4.1 clauses used are exactly the
  paper's: `full_iff` at the top, `prover_monotone` per step, `empty_iff` at
  the bottom).
* `cover` — the fresh/log-hit attribution of the `k` output-prefix moves onto
  the `t + k` unique-move budget, **PROVED**.
* `freshBad_le` — the per-slot bound for the `k` fresh slots, **PROVED** by
  product slicing on the fresh coin.
* `GameSlotBound` — **[OB-2a], NAMED OBLIGATION** (the only seam): the
  per-slot bound for the `t` game slots, i.e. the lazy-sampling
  deferred-decisions argument — the same standard random-oracle argument
  Loom/Rbr.lean's specialization 5 already defers. See its doc comment for the
  exact proof plan.
* `OB2_nonneg_of_gameSlotBound` — **PROVED**: [OB-2a] ⟹ [OB-2′], i.e.
  everything of Thm B.4 except the seam is closed, with the loss-free
  `(t + k) · ε_rbr(δ)` arithmetic. -/

end Minidregg.Loom
