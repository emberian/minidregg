/-
# `Selvage/ContentCertificate.lean` — Proof-System-Independent Content-Bound Certificates & Computational Binding (W4)

Mechanizes the proof-system-independent content-certificate layer from `CERTIFICATES.md` (§§1, 2, 5:
`P1`–`P4`, `L3`, `L6`) and closes `Selvage` Foundational Weakness **W4** (`Selvage/Commitment.lean:113`),
replacing uninhabitable perfect `PositionBinding` over compressing digests with advantage-carrying
computational binding (`ContentScheme` and `AdvOpeningScheme`).

## What lands here (ATLAS statement-first + built witness + falsifier teeth)

1. **`P1` (`ContentScheme` & `BindBreak`)**:
   Variable-length content commitment `ContentScheme (Sym Digest Op : Type*)` carrying `commit`,
   `openAt`, `openLen`, `verifyOpen`, `verifyLen`, `complete`, `completeLen`, and `bindAdv : ℕ → ℝ`.
   `BindBreak S c` witnesses positional equivocation (`PosBindBreak`) or length equivocation
   (`LenBindBreak`). `commit_eq_implies_eq_or_bindBreak` proves every whole-word collision
   `commit w₁ = commit w₂ ∧ w₁ ≠ w₂` constructively induces `BindBreak`.

2. **`Selvage` W4 Bridge (`AdvOpeningScheme` & Compressing `parityScheme`)**:
   - `idealContentScheme` inhabits `ContentScheme` with `bindAdv = 0` and zero `BindBreak`
     (`idealContentScheme_no_bindBreak`), lifting to `Selvage.BindingCommitment`.
   - `AdvOpeningScheme` extends `Selvage.OpeningScheme` with `bindAdv : ℕ → ℝ` (induced at fixed
     length `n` by `ContentScheme.toAdvOpeningScheme`) and restates the `Commitment.lean` and
     FRI query-fibre seams (`committed_extract_bind_or_equivocation`,
     `decider_open_sound_or_equivocation`, `openedFriFibreAdv_pins_or_equivocation`,
     `prob_seam_with_bindAdv`) with explicit equivocation disjuncts and additive `bindAdv`.
   - Compressing `parityScheme` (`commit w := w.sum` over `ZMod 2`): `BindingCommitment` is
     provably empty (`parity_bindingCommitment_isEmpty`) by pigeonhole (`2 < 4`), whereas
     `ContentScheme` and `AdvOpeningScheme` are inhabited, `parityScheme_has_bindBreak` exhibits
     a concrete length-2 equivocation (`[0, 0]` vs `[1, 1]`), and `parity_zero_bindAdv_refuted`
     refutes `bindAdv = 0`.

3. **`P2` & `P3` / `L6` (`SubstringAt`, `OccursIn`, `Absent`, and Public-Opening Tier Collapse)**:
   - `substringAt_of_openings` & `substringAt_of_pos_openings`: for public `i` and `P`, verifying
     `|P|` positional openings plus `1` length opening implies `SubstringAt S c i P w ∨ BindBreak S c`
     with **zero proof system**.
   - Falsifiers: 6-symbol position-shift tooth (`substringAt_shift_falsifier_6sym`: true at `i = 2`,
     false at `i = 1`) and dropped-index opening tooth (`substringAt_dropped_index_falsifier`:
     `|P| - 1` openings accept a non-matching word under `idealContentScheme` with zero `BindBreak`).

4. **`P4` / `L3` (First-Order `Regex`, Brzozowski `derives`, and Padded Complement vs Whole-Word Trap)**:
   - Executable Brzozowski derivative engine `Regex.derives` proved equivalent to semantic
     `MatchesRegex` (`derives_iff_matches`).
   - `absent_iff_padded_complement` & `absent_span_iff_padded_complement`: `AbsentPlain w P` holds
     iff `w` avoids `anyStar · P · anyStar` (accepted by `paddedComplement`).
   - Sharp regression tooth `whole_word_complement_is_not_absence`: `w = ['x', 'P', 'x']` satisfies
     whole-word `neg ('P')` while containing `'P'` at slice `[1, 2)`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Selvage.Commitment
import Selvage.BindingGame

namespace Minidregg.Selvage

set_option autoImplicit false

/-! ## §1. `P1`: `ContentScheme`, `BindBreak`, and Whole-Word Collision Reduction -/

/-- **A content commitment with computational binding (`CERTIFICATES.md` §1, `P1`)**:
commits variable-length words `List Sym` to `Digest`, opens individual symbol positions and the
committed length, guarantees completeness on both, and carries query-indexed binding advantage
`bindAdv : ℕ → ℝ` replacing `OpeningScheme.PositionBinding` (`Selvage/Commitment.lean:113`). -/
structure ContentScheme (Sym Digest Op : Type*) where
  /-- Commit a word `w : List Sym` to a root/digest. -/
  commit : List Sym → Digest
  /-- Honest positional opening witness at index `i`. -/
  openAt : List Sym → ℕ → Op
  /-- Honest length opening witness for `w.length`. -/
  openLen : List Sym → Op
  /-- Executable check that `c` opens at index `i` to symbol `v`. -/
  verifyOpen : Digest → ℕ → Sym → Op → Bool
  /-- Executable check that `c` commits to word length `n`. -/
  verifyLen : Digest → ℕ → Op → Bool
  /-- Positional completeness: every in-bounds index of `w` verifies. -/
  complete : ∀ (w : List Sym) (i : ℕ) (hi : i < w.length),
    verifyOpen (commit w) i (w[i]'hi) (openAt w i) = true
  /-- Length completeness: `w.length` verifies against `commit w`. -/
  completeLen : ∀ (w : List Sym),
    verifyLen (commit w) w.length (openLen w) = true
  /-- Upper bound on a `q`-query adversary's binding-break advantage. -/
  bindAdv : ℕ → ℝ
  /-- Advantage bounds are nonnegative. -/
  bindAdv_nonneg : ∀ q : ℕ, 0 ≤ bindAdv q

/-- Positional equivocation at digest `c`: two valid openings at one index `i` disagree (`v ≠ v'`). -/
def PosBindBreak {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op) (c : Digest) : Prop :=
  ∃ (i : ℕ) (v v' : Sym) (o o' : Op),
    S.verifyOpen c i v o = true ∧ S.verifyOpen c i v' o' = true ∧ v ≠ v'

/-- Length equivocation at digest `c`: either two valid length openings disagree (`n ≠ n'`),
or a valid positional opening at `i` exceeds a valid length opening `n ≤ i`. -/
def LenBindBreak {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op) (c : Digest) : Prop :=
  (∃ (n n' : ℕ) (o o' : Op),
    S.verifyLen c n o = true ∧ S.verifyLen c n' o' = true ∧ n ≠ n') ∨
  (∃ (i n : ℕ) (v : Sym) (o oL : Op),
    S.verifyOpen c i v o = true ∧ S.verifyLen c n oL = true ∧ n ≤ i)

/-- **`BindBreak S c`**: digest `c` admits either a positional equivocation or a length equivocation. -/
def BindBreak {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op) (c : Digest) : Prop :=
  PosBindBreak S c ∨ LenBindBreak S c

/-- Any two words with the same commitment `c` are either equal or witness `BindBreak S c`
via their honest length/positional openings. -/
theorem commit_eq_implies_eq_or_bindBreak {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) {w₁ w₂ : List Sym} {c : Digest}
    (hc₁ : S.commit w₁ = c) (hc₂ : S.commit w₂ = c) :
    w₁ = w₂ ∨ BindBreak S c := by
  by_cases hlen : w₁.length = w₂.length
  · by_cases hall : ∀ (i : ℕ) (hi₁ : i < w₁.length),
        w₁[i]'hi₁ = w₂[i]'(hlen ▸ hi₁)
    · left
      exact List.ext_getElem hlen (fun i hi₁ _ => hall i hi₁)
    · right; left
      push Not at hall
      rcases hall with ⟨i, hi₁, hne⟩
      have hi₂ : i < w₂.length := hlen ▸ hi₁
      refine ⟨i, w₁[i]'hi₁, w₂[i]'hi₂, S.openAt w₁ i, S.openAt w₂ i, ?_, ?_, hne⟩
      · simpa [hc₁] using S.complete w₁ i hi₁
      · simpa [hc₂] using S.complete w₂ i hi₂
  · right; right; left
    refine ⟨w₁.length, w₂.length, S.openLen w₁, S.openLen w₂, ?_, ?_, hlen⟩
    · simpa [hc₁] using S.completeLen w₁
    · simpa [hc₂] using S.completeLen w₂

/-- Bridge to `Selvage/BindingGame.lean`: any `SameRootDifferentSubject` pair for `S.commit`
induces `BindBreak` at the shared digest. -/
theorem bindBreak_of_sameRootDifferentSubject {Sym Digest Op : Type}
    (S : ContentScheme Sym Digest Op) {pair : List Sym × List Sym}
    (h : BindingGame.SameRootDifferentSubject S.commit pair) :
    BindBreak S (S.commit pair.1) := by
  rcases commit_eq_implies_eq_or_bindBreak S rfl h.1.symm with heq | hbr
  · exact False.elim (h.2 heq)
  · exact hbr

/-! ## §2. `Selvage` W4 Closure: `idealContentScheme`, `AdvOpeningScheme`, & Compressing `parityScheme` -/

/-- **The ideal non-compressing content scheme** (`Digest := List Sym`, `bindAdv := 0`),
analogous to `Selvage.idealCommitment` (`Selvage/Commitment.lean:228`). -/
def idealContentScheme (Sym : Type*) [DecidableEq Sym] : ContentScheme Sym (List Sym) Unit where
  commit := id
  openAt := fun _ _ => ()
  openLen := fun _ => ()
  verifyOpen := fun c i v _ => decide (c[i]? = some v)
  verifyLen := fun c n _ => decide (c.length = n)
  complete := fun w i hi => by
    simp [List.getElem?_eq_getElem hi]
  completeLen := fun w => by simp
  bindAdv := fun _ => 0
  bindAdv_nonneg := fun _ => le_rfl

/-- `idealContentScheme` admits zero `BindBreak` at every digest. -/
theorem idealContentScheme_no_bindBreak (Sym : Type*) [DecidableEq Sym] (c : List Sym) :
    ¬ BindBreak (idealContentScheme Sym) c := by
  rintro (⟨i, v, v', _, _, hv, hv', hne⟩ | ⟨⟨n, n', _, _, hn, hn', hne⟩ | ⟨i, n, v, _, _, hv, hn, hle⟩⟩)
  · simp only [idealContentScheme, decide_eq_true_eq] at hv hv'
    exact hne (Option.some.inj (hv.symm.trans hv'))
  · simp only [idealContentScheme, decide_eq_true_eq] at hn hn'
    exact hne (hn.symm.trans hn')
  · simp only [idealContentScheme, decide_eq_true_eq] at hv hn
    have hi : i < c.length := by
      rcases List.getElem?_eq_some_iff.mp hv with ⟨hlt, _⟩
      exact hlt
    omega

/-- Fixed-length `Fin n → Sym` projection of any `ContentScheme` into `Selvage.OpeningScheme`. -/
def ContentScheme.toOpeningScheme {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (n : ℕ) : OpeningScheme Digest Sym (Fin n) Op where
  commit := fun f => S.commit (List.ofFn f)
  openAt := fun f i => S.openAt (List.ofFn f) i.1
  verifyOpen := fun rt i v o => S.verifyOpen rt i.1 v o = true
  verifyOpen_commit := fun f i => by
    have hi : i.1 < (List.ofFn f).length := by simp [i.2]
    have hget : (List.ofFn f)[i.1]'hi = f i := by simp
    simpa [hget] using S.complete (List.ofFn f) i.1 hi

/-- Whenever `S` has no positional equivocations (`PosBindBreak`), its fixed-length projection
is a perfect `Selvage.BindingCommitment`. -/
def ContentScheme.toBindingCommitment {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (n : ℕ) (hno : ∀ c, ¬ PosBindBreak S c) :
    BindingCommitment Digest Sym (Fin n) Op where
  toOpeningScheme := S.toOpeningScheme n
  binding := fun rt i v v' o o' hv hv' => by
    by_contra hne
    exact hno rt ⟨i.1, v, v', o, o', hv, hv', hne⟩

/-- `idealContentScheme` lifts directly to `Selvage.BindingCommitment` at every word length `n`. -/
def idealContentBindingCommitment (Sym : Type*) [DecidableEq Sym] (n : ℕ) :
    BindingCommitment (List Sym) Sym (Fin n) Unit :=
  (idealContentScheme Sym).toBindingCommitment n
    (fun c hpos => idealContentScheme_no_bindBreak Sym c (Or.inl hpos))

/-- **W4 replacement for `Selvage.BindingCommitment`**: an `OpeningScheme` over fixed index `ι`
carrying computational binding advantage `bindAdv : ℕ → ℝ` instead of perfect `PositionBinding`. -/
structure AdvOpeningScheme (Root F ι Op : Type*) extends OpeningScheme Root F ι Op where
  /-- Query-indexed computational binding advantage. -/
  bindAdv : ℕ → ℝ
  /-- Advantage bounds are nonnegative. -/
  bindAdv_nonneg : ∀ q : ℕ, 0 ≤ bindAdv q

/-- Every `ContentScheme` induces an `AdvOpeningScheme` at fixed word length `n` with the same `bindAdv`. -/
def ContentScheme.toAdvOpeningScheme {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (n : ℕ) : AdvOpeningScheme Digest Sym (Fin n) Op where
  toOpeningScheme := S.toOpeningScheme n
  bindAdv := S.bindAdv
  bindAdv_nonneg := S.bindAdv_nonneg

/-- Every legacy `Selvage.BindingCommitment` embeds into `AdvOpeningScheme` with `bindAdv := 0`. -/
def BindingCommitment.toAdvOpeningScheme {Root F ι Op : Type*}
    (B : BindingCommitment Root F ι Op) : AdvOpeningScheme Root F ι Op where
  toOpeningScheme := B.toOpeningScheme
  bindAdv := fun _ => 0
  bindAdv_nonneg := fun _ => le_rfl

section W4Seams

/-- **W4 word-binding reduction** (replacing `BindingCommitment.opened_eq_committed` at
`Commitment.lean:154`): any word `e` fully opened against `S.commit w` equals `w`, or exhibits a
concrete `PositionEquivocation` at some coordinate. -/
theorem AdvOpeningScheme.opened_eq_committed_or_equivocation {Root F ι Op : Type*}
    (S : AdvOpeningScheme Root F ι Op) {w e : ι → F} {oe : ι → Op}
    (he : ∀ i, S.verifyOpen (S.commit w) i (e i) (oe i)) :
    e = w ∨ ∃ i, S.toOpeningScheme.PositionEquivocation (S.commit w) i (e i) (oe i) w := by
  by_cases hdiff : ∃ i, e i ≠ w i
  · rcases hdiff with ⟨i, hne⟩
    exact Or.inr ⟨i, he i, S.verifyOpen_commit w i, hne⟩
  · left
    funext i
    by_contra hne
    exact hdiff ⟨i, hne⟩

/-- **W4 `[ACC-extract-bind]` seam** (replacing `Commitment.lean:269` without `PositionBinding`):
either `e = w ∧ AccClaim.Satisfies C A w`, or some coordinate exhibits `PositionEquivocation`. -/
theorem AdvOpeningScheme.committed_extract_bind_or_equivocation
    {Root F ι Op : Type*} [Field F] {r : ℕ}
    (S : AdvOpeningScheme Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w e : ι → F}
    {oe : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C A e) :
    (e = w ∧ AccClaim.Satisfies C A w) ∨
      ∃ i, S.toOpeningScheme.PositionEquivocation A.rt i (e i) (oe i) w := by
  rcases S.opened_eq_committed_or_equivocation (w := w) (e := e) (oe := oe)
      (fun i => hrt ▸ hopen i) with heq | ⟨i, heq_i⟩
  · exact Or.inl ⟨heq, heq ▸ hsat⟩
  · exact Or.inr ⟨i, hrt.symm ▸ heq_i⟩

/-- **W4 `[DEC-open]` seam** (replacing `Commitment.lean:297` without `PositionBinding`). -/
theorem AdvOpeningScheme.decider_open_sound_or_equivocation
    {Root F ι Op : Type*} [Field F] {r : ℕ}
    (S : AdvOpeningScheme Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w f : ι → F}
    {of : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (f i) (of i))
    (hdec : decider C A f) :
    (f = w ∧ decider C A w) ∨
      ∃ i, S.toOpeningScheme.PositionEquivocation A.rt i (f i) (of i) w := by
  rcases S.opened_eq_committed_or_equivocation (w := w) (e := f) (oe := of)
      (fun i => hrt ▸ hopen i) with hfw | ⟨i, heq_i⟩
  · exact Or.inl ⟨hfw, hfw ▸ hdec⟩
  · exact Or.inr ⟨i, hrt.symm ▸ heq_i⟩

/-- Three-opening FRI fold-fibre witness (`left`, `right` in parent layer, `next` in folded layer),
covering both multiplicative FRI and additive FRI (`Selvage/AdditiveFriQuery.lean:407`). -/
structure FriFibreOpening (F OpBig OpSmall : Type*) where
  left      : F
  right     : F
  next      : F
  leftPath  : OpBig
  rightPath : OpBig
  nextPath  : OpSmall

/-- Authenticated FRI fold-fibre check over `AdvOpeningScheme` (replacing `BindingCommitment` in
`Selvage/AdditiveFriQuery.lean:407`): opens two sibling positions `idx₀, idx₁` in `Sbig`, one
folded position `idxNext` in `Ssmall`, and checks `o.next = foldStep o.left o.right`. -/
def OpenedFriFibreAdv
    {F ιBig ιSmall RootBig RootSmall OpBig OpSmall : Type*}
    (Sbig : AdvOpeningScheme RootBig F ιBig OpBig)
    (Ssmall : AdvOpeningScheme RootSmall F ιSmall OpSmall)
    (rt : RootBig) (rt' : RootSmall)
    (idx₀ idx₁ : ιBig) (idxNext : ιSmall)
    (foldStep : F → F → F)
    (o : FriFibreOpening F OpBig OpSmall) : Prop :=
  Sbig.verifyOpen rt idx₀ o.left o.leftPath ∧
  Sbig.verifyOpen rt idx₁ o.right o.rightPath ∧
  Ssmall.verifyOpen rt' idxNext o.next o.nextPath ∧
  o.next = foldStep o.left o.right

/-- **W4 FRI fibre seam** (replacing `AdditiveFriQuery.lean:422` without `PositionBinding`):
either the opened fibre matches the true fold `word' idxNext = foldStep (word idx₀) (word idx₁)`,
or one of the three openings (`left`, `right`, `next`) constructively exhibits `PositionEquivocation`. -/
theorem openedFriFibreAdv_pins_or_equivocation
    {F ιBig ιSmall RootBig RootSmall OpBig OpSmall : Type*}
    (Sbig : AdvOpeningScheme RootBig F ιBig OpBig)
    (Ssmall : AdvOpeningScheme RootSmall F ιSmall OpSmall)
    {word : ιBig → F} {word' : ιSmall → F}
    {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit word) (hrt' : rt' = Ssmall.commit word')
    {idx₀ idx₁ : ιBig} {idxNext : ιSmall}
    {foldStep : F → F → F}
    {o : FriFibreOpening F OpBig OpSmall}
    (hopen : OpenedFriFibreAdv Sbig Ssmall rt rt' idx₀ idx₁ idxNext foldStep o) :
    word' idxNext = foldStep (word idx₀) (word idx₁) ∨
      Sbig.toOpeningScheme.PositionEquivocation rt idx₀ o.left o.leftPath word ∨
      Sbig.toOpeningScheme.PositionEquivocation rt idx₁ o.right o.rightPath word ∨
      Ssmall.toOpeningScheme.PositionEquivocation rt' idxNext o.next o.nextPath word' := by
  rcases hopen with ⟨hleft, hright, hnext, heq⟩
  by_cases hl : o.left = word idx₀
  · by_cases hr : o.right = word idx₁
    · by_cases hn : o.next = word' idxNext
      · left
        rw [← hn, heq, hl, hr]
      · exact Or.inr (Or.inr (Or.inr
          ⟨hnext, Ssmall.toOpeningScheme.verifyOpen_of_commit_eq hrt' idxNext, hn⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨hright, Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt idx₁, hr⟩))
  · exact Or.inr (Or.inl
      ⟨hleft, Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt idx₀, hl⟩)

/-- **Additive `bindAdv` threading over finite coin spaces** (`W4` probabilistic budget):
if `Target` fails only when either protocol soundness (`ProtoBad`, `≤ ε q`) or commitment binding
(`BindBad`, `≤ S.bindAdv q`) fails, total failure probability is at most `ε q + S.bindAdv q`. -/
theorem AdvOpeningScheme.prob_seam_with_bindAdv {Ω : Type} [Fintype Ω]
    {Root F ι Op : Type*} (S : AdvOpeningScheme Root F ι Op)
    (Accept Target ProtoBad BindBad : Ω → Prop) {q : ℕ} {ε : ℕ → ℝ}
    (hcov : ∀ ω, Accept ω → ¬ Target ω → ProtoBad ω ∨ BindBad ω)
    (hproto : BindingGame.prob ProtoBad ≤ ε q)
    (hbind : BindingGame.prob BindBad ≤ S.bindAdv q) :
    BindingGame.prob (fun ω => Accept ω ∧ ¬ Target ω) ≤ ε q + S.bindAdv q := by
  have hmono : BindingGame.prob (fun ω => Accept ω ∧ ¬ Target ω) ≤
      BindingGame.prob (fun ω => ProtoBad ω ∨ BindBad ω) :=
    BindingGame.prob_mono (fun ω h => hcov ω h.1 h.2)
  have hor := BindingGame.prob_or ProtoBad BindBad
  linarith

end W4Seams

/-! ### Compressing Parity Scheme (`P1` & `W4` Pigeonhole Falsifiers) -/

/-- **Compressing toy parity scheme (`CERTIFICATES.md` §5 `P1`)**: commits `w : List (ZMod 2)`
to its parity sum `w.sum : ZMod 2` with flat preimage openings. -/
def parityScheme : ContentScheme (ZMod 2) (ZMod 2) (List (ZMod 2)) where
  commit := fun w => w.sum
  openAt := fun w _ => w
  openLen := fun w => w
  verifyOpen := fun c i v o => decide (o.sum = c ∧ o[i]? = some v)
  verifyLen := fun c n o => decide (o.sum = c ∧ o.length = n)
  complete := fun w i hi => by
    simp [List.getElem?_eq_getElem hi]
  completeLen := fun w => by simp
  bindAdv := fun _ => 1
  bindAdv_nonneg := fun _ => by norm_num

/-- `ContentScheme` and `AdvOpeningScheme` are inhabited at the compressing 2-bit-to-1-bit
parameters (`Fin 2 → ZMod 2` into `ZMod 2`). -/
def parityAdvOpeningScheme : AdvOpeningScheme (ZMod 2) (ZMod 2) (Fin 2) (List (ZMod 2)) :=
  parityScheme.toAdvOpeningScheme 2

/-- **W4 Pigeonhole Falsifier**: NO `Selvage.BindingCommitment` exists from length-2 bit words
`Fin 2 → ZMod 2` (cardinality `4`) into `ZMod 2` (cardinality `2`), for **any** opening type `Op`. -/
theorem parity_bindingCommitment_isEmpty (Op : Type*) :
    IsEmpty (BindingCommitment (ZMod 2) (ZMod 2) (Fin 2) Op) :=
  BindingCommitment.isEmpty_of_card_lt (by simp [ZMod.card])

/-- `parityAdvOpeningScheme` refutes `PositionBinding` at index `0` via `![0, 0]` and `![1, 1]`. -/
theorem parityAdvOpeningScheme_not_positionBinding :
    ¬ parityAdvOpeningScheme.toOpeningScheme.PositionBinding := by
  intro hbind
  have h0 : parityAdvOpeningScheme.verifyOpen 0 0 0 [0, 0] := by
    change parityScheme.verifyOpen 0 0 0 [0, 0] = true; decide
  have h1 : parityAdvOpeningScheme.verifyOpen 0 0 1 [1, 1] := by
    change parityScheme.verifyOpen 0 0 1 [1, 1] = true; decide
  have heq : (0 : ZMod 2) = 1 := hbind 0 0 0 1 [0, 0] [1, 1] h0 h1
  exact absurd heq (by decide)

/-- **`P1` Constructive Equivocation Witness**: `parityScheme` exhibits a concrete positional
`BindBreak` on length-2 words `[0, 0]` and `[1, 1]` at digest `0 : ZMod 2` and index `0`. -/
theorem parityScheme_has_bindBreak : BindBreak parityScheme (0 : ZMod 2) := by
  left
  refine ⟨0, 0, 1, [0, 0], [1, 1], ?_, ?_, ?_⟩ <;> decide

/-- **`P1` Zero-Advantage Falsifier**: in `Selvage.BindingGame`, a deterministic `0`-query pair
adversary outputting `([0, 0], [1, 1])` wins `SameRootDifferentSubject parityScheme.commit` with
probability `1`, refuting `bindAdv = 0` for `parityScheme`. -/
def parityCollisionGame : BindingGame.Experiment Unit Unit (List (ZMod 2) × List (ZMod 2)) where
  run _ _ := ([0, 0], [1, 1])
  queries _ _ := 0
  steps _ _ := 1

theorem parity_zero_bindAdv_refuted :
    ¬ parityCollisionGame.SecureAt
        (fun _ => BindingGame.SameRootDifferentSubject parityScheme.commit) 0 1 0 := by
  intro hsec
  have hw : parityCollisionGame.Within () 0 1 := fun _ => ⟨le_rfl, le_rfl⟩
  have hadv := hsec () hw
  have hwin : BindingGame.SameRootDifferentSubject parityScheme.commit ([0, 0], [1, 1]) := by
    refine ⟨?_, ?_⟩ <;> decide
  have hone : parityCollisionGame.advantage
      (fun _ => BindingGame.SameRootDifferentSubject parityScheme.commit) () = 1 := by
    simp [BindingGame.Experiment.advantage, parityCollisionGame, hwin, BindingGame.prob_true]
  linarith

/-! ## §3. `P2` & `P3` / `L6`: Content Relations & Public-Opening Tier Collapse -/

/-- Word-level slice `[i, j)` (`(w.drop i).take (j - i)`). -/
def Slice {Sym : Type*} (w : List Sym) (i j : ℕ) : List Sym :=
  (w.drop i).take (j - i)

/-- Word-level `SubstringAt`: `P` occurs in `w` starting at exact index `i`. -/
def SubstringAtPlain {Sym : Type*} (w : List Sym) (i : ℕ) (P : List Sym) : Prop :=
  ∃ h : i + P.length ≤ w.length, ∀ j : Fin P.length, w[i + j.1]'(by omega) = P[j.1]'j.2

instance instDecidableSubstringAtPlain {Sym : Type*} [DecidableEq Sym]
    (w : List Sym) (i : ℕ) (P : List Sym) : Decidable (SubstringAtPlain w i P) := by
  unfold SubstringAtPlain
  infer_instance

/-- Equivalence between indexed `SubstringAtPlain` and `(w.drop i).take P.length = P`. -/
theorem substringAtPlain_iff_take_drop {Sym : Type*} (w : List Sym) (i : ℕ) (P : List Sym) :
    SubstringAtPlain w i P ↔ i + P.length ≤ w.length ∧ (w.drop i).take P.length = P := by
  constructor
  · rintro ⟨hlen, hchars⟩
    refine ⟨hlen, List.ext_getElem ?_ fun j hj₁ hj₂ => ?_⟩
    · simp [List.length_take, List.length_drop]; omega
    · rw [List.getElem_take, List.getElem_drop]
      exact hchars ⟨j, hj₂⟩
  · rintro ⟨hlen, hslice⟩
    refine ⟨hlen, fun j => ?_⟩
    have hj_take : j.1 < ((w.drop i).take P.length).length := by
      simp [List.length_take, List.length_drop, j.2]; omega
    have h1 : ((w.drop i).take P.length)[j.1]'hj_take = P[j.1]'j.2 := by simp [hslice]
    rw [List.getElem_take, List.getElem_drop] at h1
    exact h1

/-- Word-level `OccursIn`: `P` occurs at some offset `i` in `w`. -/
def OccursInPlain {Sym : Type*} (w P : List Sym) : Prop :=
  ∃ i : ℕ, SubstringAtPlain w i P

/-- Decidable check for `OccursInPlain` (checking offsets `0 .. w.length`). -/
instance instDecidableOccursInPlain {Sym : Type*} [DecidableEq Sym]
    (w P : List Sym) : Decidable (OccursInPlain w P) := by
  have heq : OccursInPlain w P ↔ ∃ i : Fin (w.length + 1), SubstringAtPlain w i.1 P := by
    constructor
    · rintro ⟨i, hi, hchars⟩
      exact ⟨⟨i, by omega⟩, hi, hchars⟩
    · rintro ⟨i, hsub⟩
      exact ⟨i.1, hsub⟩
  exact decidable_of_iff' _ heq

/-- Word-level `Absent`: `P` does not occur at any offset `i` in `w`. -/
def AbsentPlain {Sym : Type*} (w P : List Sym) : Prop :=
  ∀ i : ℕ, ¬ SubstringAtPlain w i P

instance instDecidableAbsentPlain {Sym : Type*} [DecidableEq Sym]
    (w P : List Sym) : Decidable (AbsentPlain w P) := by
  have heq : AbsentPlain w P ↔ ¬ OccursInPlain w P := by
    unfold AbsentPlain OccursInPlain
    push Not
    rfl
  exact decidable_of_iff' _ heq

/-- **`P2` Content-Bound `SubstringAt` (`CERTIFICATES.md` §1)**: L0-compliant relation carrying `c`. -/
def SubstringAt {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (i : ℕ) (P : List Sym) (w : List Sym) : Prop :=
  S.commit w = c ∧ SubstringAtPlain w i P

instance instDecidableSubstringAt {Sym Digest Op : Type*}
    [DecidableEq Sym] [DecidableEq Digest]
    (S : ContentScheme Sym Digest Op) (c : Digest) (i : ℕ) (P w : List Sym) :
    Decidable (SubstringAt S c i P w) := by
  unfold SubstringAt
  infer_instance

/-- **`P2` Content-Bound `OccursIn` (`CERTIFICATES.md` §1)**. -/
def OccursIn {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (P : List Sym) (w : List Sym) : Prop :=
  S.commit w = c ∧ OccursInPlain w P

theorem occursIn_iff_exists_substringAt {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (c : Digest) (P w : List Sym) :
    OccursIn S c P w ↔ ∃ i, SubstringAt S c i P w := by
  unfold OccursIn SubstringAt OccursInPlain
  exact exists_and_left.symm

/-- **`P2` Content-Bound `Absent` (`CERTIFICATES.md` §1)**. -/
def Absent {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (P : List Sym) (w : List Sym) : Prop :=
  S.commit w = c ∧ AbsentPlain w P

/-- **`FormOK` (`CERTIFICATES.md` §1)**: committed word belongs to formal language `lang`. -/
def FormOK {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (lang : List Sym → Prop) (w : List Sym) : Prop :=
  S.commit w = c ∧ lang w

/-- **`Framed` (`CERTIFICATES.md` §1)**: committed word is rendered from a guarded-safe datum. -/
def Framed {Sym Digest Op Data : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (render : Data → List Sym) (guardedSafe : Data → Prop) (w : List Sym) : Prop :=
  S.commit w = c ∧ ∃ d : Data, w = render d ∧ guardedSafe d

/-- **`P2` 6-Symbol Position-Shift Falsifier (`CERTIFICATES.md` §5 `P2`)**:
On 6-byte record `[10, 20, 30, 40, 50, 60]` and pattern `[30, 40]`, `SubstringAt` holds at
`i = 2` and fails at `i = 1`, catching any verifier that checks `OccursIn` without binding `i`. -/
def sixByteRecord : List UInt8 := [10, 20, 30, 40, 50, 60]
def twoBytePattern : List UInt8 := [30, 40]

theorem substringAt_shift_falsifier_6sym :
    sixByteRecord.length = 6 ∧
    SubstringAt (idealContentScheme UInt8) sixByteRecord 2 twoBytePattern sixByteRecord ∧
    ¬ SubstringAt (idealContentScheme UInt8) sixByteRecord 1 twoBytePattern sixByteRecord := by
  decide

/-- Executable Tier-1 `SubstringAt` verifier (`L6`): checks `i + |P| ≤ n`, `1` length opening,
and `|P|` positional openings — **zero proof system**. -/
def verifySubstringOpenings {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (i : ℕ) (P : List Sym) (n : ℕ)
    (os : Fin P.length → Op) (oLen : Op) : Bool :=
  decide (i + P.length ≤ n) &&
  S.verifyLen c n oLen &&
  (List.finRange P.length).all (fun j => S.verifyOpen c (i + j.1) (P[j.1]'j.2) (os j))

/-- **Tier-1 Completeness**: honest positional + length openings pass `verifySubstringOpenings`. -/
theorem verifySubstringOpenings_complete {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) {c : Digest} {i : ℕ} {P w : List Sym}
    (hsub : SubstringAt S c i P w) :
    verifySubstringOpenings S c i P w.length
      (fun j => S.openAt w (i + j.1)) (S.openLen w) = true := by
  rcases hsub with ⟨hc, hlen, hchars⟩
  unfold verifySubstringOpenings
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hlen, hc ▸ S.completeLen w⟩, fun j _ => ?_⟩
  have hij : i + j.1 < w.length := by omega
  have hcj : P[j.1]'j.2 = w[i + j.1]'hij := (hchars j).symm
  simpa [hc, hcj] using S.complete w (i + j.1) hij

/-- **`P3` / `L6` Tier-1 Positional-Opening Soundness (`CERTIFICATES.md` §5 `P3`)**:
if `|P|` positional openings verify at `i + j` and `i + |P| ≤ |w|`, then either
`SubstringAt S c i P w` holds or `BindBreak S c` occurs. -/
theorem substringAt_of_pos_openings {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (c : Digest) (i : ℕ) (P : List Sym)
    (os : Fin P.length → Op)
    (hv : ∀ j : Fin P.length, S.verifyOpen c (i + j.1) (P[j.1]'j.2) (os j) = true) :
    ∀ w : List Sym, S.commit w = c → i + P.length ≤ w.length →
      SubstringAt S c i P w ∨ BindBreak S c := by
  intro w hc hlen
  by_cases hall : ∀ j : Fin P.length, w[i + j.1]'(by omega) = P[j.1]'j.2
  · exact Or.inl ⟨hc, hlen, hall⟩
  · right; left
    push Not at hall
    rcases hall with ⟨j, hne⟩
    have hij : i + j.1 < w.length := by omega
    refine ⟨i + j.1, w[i + j.1]'hij, P[j.1]'j.2, S.openAt w (i + j.1), os j, ?_, hv j, hne⟩
    simpa [hc] using S.complete w (i + j.1) hij

/-- **`P3` / `L6` Full Tier-1 Soundness (`substringAt_of_openings`, zero proof system)**:
verifying `|P|` positional openings PLUS `1` length opening (`verifySubstringOpenings = true`)
implies `SubstringAt S c i P w ∨ BindBreak S c` for **every** committed `w` (discharging
`i + |P| ≤ |w|` automatically via `verifyLen` / `LenBindBreak`). -/
theorem substringAt_of_openings {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (c : Digest) (i : ℕ) (P : List Sym) (n : ℕ)
    (os : Fin P.length → Op) (oLen : Op)
    (hver : verifySubstringOpenings S c i P n os oLen = true) :
    ∀ w : List Sym, S.commit w = c → SubstringAt S c i P w ∨ BindBreak S c := by
  unfold verifySubstringOpenings at hver
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hver
  rcases hver with ⟨⟨hbound, hvLen⟩, hvPos⟩
  intro w hc
  by_cases hwn : w.length = n
  · refine substringAt_of_pos_openings S c i P os (fun j => hvPos j (List.mem_finRange j)) w hc ?_
    omega
  · right; right; left
    refine ⟨w.length, n, S.openLen w, oLen, ?_, hvLen, hwn⟩
    simpa [hc] using S.completeLen w

/-- **`P3` Dropped-Index Opening Falsifier (`|P| - 1` openings)**:
On `P = [30, 40]` (`|P| = 2`), checking only `j = 0` (`|P| - 1 = 1` positional opening) and
length `6` accepts corrupted word `[10, 20, 30, 99, 50, 60]` under `idealContentScheme UInt8`
with **zero `BindBreak`** while `SubstringAt` is **false**. -/
def corruptedSixByteRecord : List UInt8 := [10, 20, 30, 99, 50, 60]

theorem substringAt_dropped_index_falsifier :
    let S := idealContentScheme UInt8
    let c := S.commit corruptedSixByteRecord
    -- Length opening and 2 + |P| ≤ 6 hold:
    (2 + twoBytePattern.length ≤ 6 ∧ S.verifyLen c 6 () = true) ∧
    -- All |P| - 1 = 1 prefix indices (j = 0) verify:
    S.verifyOpen c (2 + 0) twoBytePattern[0] () = true ∧
    -- Zero BindBreak occurs:
    ¬ BindBreak S c ∧
    -- Yet SubstringAt is FALSE (and full verifySubstringOpenings rejects):
    ¬ SubstringAt S c 2 twoBytePattern corruptedSixByteRecord ∧
    verifySubstringOpenings S c 2 twoBytePattern 6 (fun _ => ()) () = false := by
  refine ⟨by decide, by decide, idealContentScheme_no_bindBreak UInt8 _, by decide, by decide⟩

/-- **Dropped-Length-Opening Falsifier**: for `P = []` at out-of-bounds offset `i = 7 > 6`,
all `|P| = 0` positional openings hold vacuously and `¬ BindBreak S c`, yet `SubstringAt` is
false — demonstrating why `verifyLen` is required alongside `verifyOpen`. -/
theorem substringAt_dropped_len_falsifier :
    let S := idealContentScheme UInt8
    let c := S.commit sixByteRecord
    (∀ j : Fin ([] : List UInt8).length, S.verifyOpen c (7 + j.1) ([][j.1]'j.2) () = true) ∧
    ¬ BindBreak S c ∧
    ¬ SubstringAt S c 7 [] sixByteRecord := by
  refine ⟨fun j => Fin.elim0 j, idealContentScheme_no_bindBreak UInt8 _, by decide⟩

/-! ## §4. `P4` / `L3`: First-Order `Regex`, Brzozowski `derives`, & Padded Complement -/

/-- First-order syntactic regular-expression AST with wildcard (`any`) and Boolean complement (`neg`),
matching `CERTIFICATES.md` §2 L3 & §5 `P4` (`PredRE` shape; zero function closures). -/
inductive Regex (Sym : Type*) where
  | empty : Regex Sym
  | eps   : Regex Sym
  | sym   : Sym → Regex Sym
  | any   : Regex Sym
  | alt   : Regex Sym → Regex Sym → Regex Sym
  | seq   : Regex Sym → Regex Sym → Regex Sym
  | star  : Regex Sym → Regex Sym
  | neg   : Regex Sym → Regex Sym
  deriving DecidableEq, Repr

/-- Non-empty Kleene closure helper for clean structural induction on `Regex.star`. -/
inductive MatchesStar {Sym : Type*} (M : List Sym → Prop) : List Sym → Prop where
  | nil : MatchesStar M []
  | cons {u v : List Sym} (hne : u ≠ []) (hu : M u) (hv : MatchesStar M v) :
      MatchesStar M (u ++ v)

/-- Unrestricted Kleene star (allowing empty pieces) is equivalent to `MatchesStar`. -/
theorem matchesStar_iff_parts {Sym : Type*} {M : List Sym → Prop} (w : List Sym) :
    MatchesStar M w ↔ ∃ parts : List (List Sym), parts.foldr (· ++ ·) [] = w ∧ ∀ u ∈ parts, M u := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl, fun _ hmem => False.elim (List.not_mem_nil hmem)⟩
    | @cons u v _ hu _ ih =>
        rcases ih with ⟨parts, hfold, hall⟩
        refine ⟨u :: parts, by simp [hfold], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hu
        · exact hall x hmem
  · rintro ⟨parts, rfl, hall⟩
    induction parts with
    | nil => exact .nil
    | cons u rest ih =>
        have hu : M u := hall u (List.mem_cons_self ..)
        have hrest : MatchesStar M (rest.foldr (· ++ ·) []) :=
          ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        by_cases hne : u = []
        · subst hne; simpa using hrest
        · exact .cons hne hu hrest

/-- Semantic language membership `MatchesRegex w r` (`w ∈ L(r)`). -/
def MatchesRegex {Sym : Type*} : List Sym → Regex Sym → Prop
  | _, .empty => False
  | w, .eps => w = []
  | w, .sym c => w = [c]
  | w, .any => w.length = 1
  | w, .alt r₁ r₂ => MatchesRegex w r₁ ∨ MatchesRegex w r₂
  | w, .seq r₁ r₂ => ∃ u v, u ++ v = w ∧ MatchesRegex u r₁ ∧ MatchesRegex v r₂
  | w, .star r => MatchesStar (fun u => MatchesRegex u r) w
  | w, .neg r => ¬ MatchesRegex w r

/-- **`MatchesAt` (`CERTIFICATES.md` §1)**: span `[i, j)` of committed `w` matches `r`. -/
def MatchesAt {Sym Digest Op : Type*} (S : ContentScheme Sym Digest Op)
    (c : Digest) (i j : ℕ) (r : Regex Sym) (w : List Sym) : Prop :=
  S.commit w = c ∧ MatchesRegex (Slice w i j) r

/-- Brzozowski nullability check (`[] ∈ L(r)`). -/
def Regex.nullable {Sym : Type*} : Regex Sym → Bool
  | .empty => false
  | .eps => true
  | .sym _ => false
  | .any => false
  | .alt r₁ r₂ => r₁.nullable || r₂.nullable
  | .seq r₁ r₂ => r₁.nullable && r₂.nullable
  | .star _ => true
  | .neg r => !r.nullable

/-- Brzozowski single-symbol derivative `∂_a r`. -/
def Regex.deriv {Sym : Type*} [DecidableEq Sym] (a : Sym) : Regex Sym → Regex Sym
  | .empty => .empty
  | .eps => .empty
  | .sym c => if a = c then .eps else .empty
  | .any => .eps
  | .alt r₁ r₂ => .alt (r₁.deriv a) (r₂.deriv a)
  | .seq r₁ r₂ =>
      if r₁.nullable then .alt (.seq (r₁.deriv a) r₂) (r₂.deriv a)
      else .seq (r₁.deriv a) r₂
  | .star r => .seq (r.deriv a) (.star r)
  | .neg r => .neg (r.deriv a)

/-- Executable Brzozowski word matcher `derives w r`. -/
def Regex.derives {Sym : Type*} [DecidableEq Sym] : List Sym → Regex Sym → Bool
  | [], r => r.nullable
  | a :: ws, r => Regex.derives ws (r.deriv a)

/-- `nullable` decides empty-word membership `MatchesRegex [] r`. -/
theorem Regex.nullable_iff_matches_nil {Sym : Type*} (r : Regex Sym) :
    r.nullable = true ↔ MatchesRegex [] r := by
  induction r with
  | empty => simp [Regex.nullable, MatchesRegex]
  | eps => simp [Regex.nullable, MatchesRegex]
  | sym _ => simp [Regex.nullable, MatchesRegex]
  | any => simp [Regex.nullable, MatchesRegex]
  | alt r₁ r₂ ih₁ ih₂ => simp [Regex.nullable, MatchesRegex, ih₁, ih₂]
  | seq r₁ r₂ ih₁ ih₂ =>
      simp only [Regex.nullable, Bool.and_eq_true, ih₁, ih₂, MatchesRegex]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨[], [], rfl, h₁, h₂⟩
      · rintro ⟨u, v, huv, h₁, h₂⟩
        rcases List.append_eq_nil_iff.mp huv with ⟨rfl, rfl⟩
        exact ⟨h₁, h₂⟩
  | star _ _ =>
      simp only [Regex.nullable, MatchesRegex, true_iff]
      exact .nil
  | neg r ih =>
      simp [Regex.nullable, MatchesRegex, ← ih]

/-- Brzozowski derivative step theorem: `MatchesRegex w (r.deriv a) ↔ MatchesRegex (a :: w) r`. -/
theorem Regex.matches_deriv_iff {Sym : Type*} [DecidableEq Sym]
    (a : Sym) (w : List Sym) (r : Regex Sym) :
    MatchesRegex w (r.deriv a) ↔ MatchesRegex (a :: w) r := by
  induction r generalizing w with
  | empty => simp [Regex.deriv, MatchesRegex]
  | eps => simp [Regex.deriv, MatchesRegex]
  | sym c =>
      by_cases hac : a = c
      · subst hac; simp [Regex.deriv, MatchesRegex]
      · simp [Regex.deriv, hac, MatchesRegex]
  | any =>
      simp only [Regex.deriv, MatchesRegex, List.length_cons]
      exact ⟨fun h => by subst h; rfl, fun h => List.length_eq_zero_iff.mp (by omega)⟩
  | alt r₁ r₂ ih₁ ih₂ =>
      simp [Regex.deriv, MatchesRegex, ih₁ w, ih₂ w]
  | seq r₁ r₂ ih₁ ih₂ =>
      by_cases hnull : r₁.nullable = true
      · have hnil₁ : MatchesRegex [] r₁ := (Regex.nullable_iff_matches_nil r₁).mp hnull
        simp only [Regex.deriv, hnull, ↓reduceIte, MatchesRegex]
        constructor
        · rintro (⟨u', v, rfl, hu', hv⟩ | hv)
          · exact ⟨a :: u', v, rfl, (ih₁ u').mp hu', hv⟩
          · exact ⟨[], a :: w, rfl, hnil₁, (ih₂ w).mp hv⟩
        · rintro ⟨u, v, huv, hu, hv⟩
          cases u with
          | nil =>
              simp only [List.nil_append] at huv
              subst huv
              exact Or.inr ((ih₂ w).mpr hv)
          | cons b u' =>
              simp only [List.cons_append, List.cons.injEq] at huv
              rcases huv with ⟨rfl, rfl⟩
              exact Or.inl ⟨u', v, rfl, (ih₁ u').mpr hu, hv⟩
      · have hnotnil₁ : ¬ MatchesRegex [] r₁ := by
          rw [← Regex.nullable_iff_matches_nil]; simp [hnull]
        simp only [Regex.deriv, hnull, Bool.false_eq_true, ↓reduceIte, MatchesRegex]
        constructor
        · rintro ⟨u', v, rfl, hu', hv⟩
          exact ⟨a :: u', v, rfl, (ih₁ u').mp hu', hv⟩
        · rintro ⟨u, v, huv, hu, hv⟩
          cases u with
          | nil => exact False.elim (hnotnil₁ hu)
          | cons b u' =>
              simp only [List.cons_append, List.cons.injEq] at huv
              rcases huv with ⟨rfl, rfl⟩
              exact ⟨u', v, rfl, (ih₁ u').mpr hu, hv⟩
  | star r ih =>
      simp only [Regex.deriv, MatchesRegex]
      constructor
      · rintro ⟨u', v, rfl, hu', hv⟩
        exact .cons (List.cons_ne_nil a u') ((ih u').mp hu') hv
      · intro hstar
        generalize htarget : (a :: w) = z at hstar
        cases hstar with
        | nil => cases htarget
        | @cons u v hne hu hv =>
            cases u with
            | nil => exact False.elim (hne rfl)
            | cons b u' =>
                simp only [List.cons_append, List.cons.injEq] at htarget
                rcases htarget with ⟨rfl, rfl⟩
                exact ⟨u', v, rfl, (ih u').mpr hu, hv⟩
  | neg r ih =>
      simp [Regex.deriv, MatchesRegex, ih w]

/-- **Brzozowski Soundness & Completeness**: `Regex.derives w r = true ↔ MatchesRegex w r`. -/
theorem Regex.derives_iff_matches {Sym : Type*} [DecidableEq Sym]
    (w : List Sym) (r : Regex Sym) :
    Regex.derives w r = true ↔ MatchesRegex w r := by
  induction w generalizing r with
  | nil => exact Regex.nullable_iff_matches_nil r
  | cons a ws ih =>
      simp only [Regex.derives]
      exact (ih (r.deriv a)).trans (Regex.matches_deriv_iff a ws r)

/-- Wildcard Kleene star `any*` (`.*`). -/
def Regex.anyStar {Sym : Type*} : Regex Sym := .star .any

/-- `anyStar` matches **every** word `w : List Sym`. -/
theorem Regex.matches_anyStar {Sym : Type*} (w : List Sym) :
    MatchesRegex w Regex.anyStar := by
  change MatchesStar (fun u => MatchesRegex u .any) w
  induction w with
  | nil => exact .nil
  | cons a ws ih =>
      exact MatchesStar.cons (u := [a]) (v := ws)
        (List.cons_ne_nil a []) (by simp [MatchesRegex]) ih

/-- Padded factor language `any* · r · any*` and its complement `neg (any* · r · any*)`. -/
def Regex.pad {Sym : Type*} (r : Regex Sym) : Regex Sym :=
  .seq .anyStar (.seq r .anyStar)

def Regex.paddedComplement {Sym : Type*} (r : Regex Sym) : Regex Sym :=
  .neg (Regex.pad r)

/-- Exact literal pattern `P : List Sym` compiled into `Regex Sym`. -/
def Regex.literal {Sym : Type*} : List Sym → Regex Sym
  | [] => .eps
  | c :: cs => .seq (.sym c) (Regex.literal cs)

/-- `Regex.literal P` matches `w` iff `w = P`. -/
theorem Regex.matches_literal_iff {Sym : Type*} (w P : List Sym) :
    MatchesRegex w (Regex.literal P) ↔ w = P := by
  induction P generalizing w with
  | nil => simp [Regex.literal, MatchesRegex]
  | cons c cs ih =>
      simp only [Regex.literal, MatchesRegex]
      constructor
      · rintro ⟨u, v, rfl, rfl, hv⟩
        rw [(ih v).mp hv]
        rfl
      · rintro rfl
        exact ⟨[c], cs, rfl, rfl, (ih cs).mpr rfl⟩

/-- `MatchesRegex w (Regex.pad r)` iff some slice `Slice w i j` matches `r`. -/
theorem Regex.matches_pad_iff_exists_slice {Sym : Type*} (w : List Sym) (r : Regex Sym) :
    MatchesRegex w (Regex.pad r) ↔ ∃ i j : ℕ, MatchesRegex (Slice w i j) r := by
  change (∃ pre rest, pre ++ rest = w ∧ MatchesRegex pre Regex.anyStar ∧
      ∃ mid suf, mid ++ suf = rest ∧ MatchesRegex mid r ∧ MatchesRegex suf Regex.anyStar) ↔
    ∃ i j : ℕ, MatchesRegex (Slice w i j) r
  constructor
  · rintro ⟨pre, rest, hpre, _, mid, suf, hmid, hr, _⟩
    refine ⟨pre.length, pre.length + mid.length, ?_⟩
    have hw : w = pre ++ (mid ++ suf) := by rw [← hpre, ← hmid]
    have hslice : Slice w pre.length (pre.length + mid.length) = mid := by
      unfold Slice
      rw [hw, Nat.add_sub_cancel_left, List.drop_left, List.take_left]
    rwa [hslice]
  · rintro ⟨i, j, hslice⟩
    refine ⟨w.take i, w.drop i, List.take_append_drop i w, Regex.matches_anyStar _,
      Slice w i j, (w.drop i).drop (j - i), ?_, hslice, Regex.matches_anyStar _⟩
    unfold Slice
    exact List.take_append_drop (j - i) (w.drop i)

/-- **`P4` / `L3` Span-Absence Equivalence (`CERTIFICATES.md` §5 `P4`)**:
no slice `[i, j)` of `w` matches `r` iff `w` matches `Regex.paddedComplement r`
(`neg (any* · r · any*)`), and equivalently `Regex.derives w (Regex.paddedComplement r) = true`. -/
theorem absent_span_iff_padded_complement {Sym : Type*} (w : List Sym) (r : Regex Sym) :
    (∀ i j : ℕ, ¬ MatchesRegex (Slice w i j) r) ↔ MatchesRegex w (Regex.paddedComplement r) := by
  change (∀ i j : ℕ, ¬ MatchesRegex (Slice w i j) r) ↔ ¬ MatchesRegex w (Regex.pad r)
  rw [Regex.matches_pad_iff_exists_slice]
  push Not
  rfl

theorem absent_span_iff_derives_padded_complement {Sym : Type*} [DecidableEq Sym]
    (w : List Sym) (r : Regex Sym) :
    (∀ i j : ℕ, Regex.derives (Slice w i j) r = false) ↔
      Regex.derives w (.neg (.seq (.star .any) (.seq r (.star .any)))) = true := by
  have hL : (∀ i j : ℕ, Regex.derives (Slice w i j) r = false) ↔
      (∀ i j : ℕ, ¬ MatchesRegex (Slice w i j) r) := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [← Regex.derives_iff_matches, Bool.eq_false_iff]
  rw [hL, absent_span_iff_padded_complement]
  exact (Regex.derives_iff_matches w (Regex.paddedComplement r)).symm

/-- **`P4` / `L3` Pattern-Absence Theorem (`absent_iff_padded_complement`)**:
`AbsentPlain w P` holds iff `w` does NOT match `any* · literal P · any*` (equivalently,
`w` is accepted by `paddedComplement (literal P)`). -/
theorem absent_iff_padded_complement {Sym : Type*} (w P : List Sym) :
    AbsentPlain w P ↔ ¬ MatchesRegex w (Regex.pad (Regex.literal P)) := by
  rw [Regex.matches_pad_iff_exists_slice]
  unfold AbsentPlain
  constructor
  · intro habs ⟨i, j, hm⟩
    have heq : Slice w i j = P := (Regex.matches_literal_iff _ P).mp hm
    have hlen : i + P.length ≤ w.length := by
      have h1 : (Slice w i j).length ≤ (w.drop i).length := List.length_take_le' _ _
      rw [heq, List.length_drop] at h1
      by_cases hiw : i ≤ w.length
      · omega
      · have hdrop0 : w.drop i = [] := List.drop_eq_nil_of_le (by omega)
        have hslice0 : Slice w i j = [] := by simp [Slice, hdrop0]
        rw [hslice0] at heq
        exact absurd ((substringAtPlain_iff_take_drop w w.length P).mpr
          ⟨by subst heq; omega, by subst heq; simp⟩) (habs w.length)
    have htake : (w.drop i).take P.length = P := by
      have hji : P.length ≤ j - i := by
        have h2 : (Slice w i j).length ≤ j - i := List.length_take_le _ _
        rwa [heq] at h2
      have h3 : (Slice w i j).take P.length = P.take P.length := congrArg (List.take P.length) heq
      unfold Slice at h3
      rwa [List.take_take, Nat.min_eq_left hji, List.take_length] at h3
    exact habs i ((substringAtPlain_iff_take_drop w i P).mpr ⟨hlen, htake⟩)
  · intro hno i hsub
    rcases (substringAtPlain_iff_take_drop w i P).mp hsub with ⟨_, htake⟩
    apply hno
    refine ⟨i, i + P.length, (Regex.matches_literal_iff _ P).mpr ?_⟩
    unfold Slice
    simpa [Nat.add_sub_cancel_left] using htake

theorem absent_iff_derives_padded_complement {Sym : Type*} [DecidableEq Sym]
    (w P : List Sym) :
    AbsentPlain w P ↔
      Regex.derives w (Regex.paddedComplement (Regex.literal P)) = true := by
  rw [absent_iff_padded_complement]
  exact (Regex.derives_iff_matches w (Regex.paddedComplement (Regex.literal P))).symm

/-- Content-bound `Absent S c P w` equivalence with `Regex.paddedComplement`. -/
theorem absent_bound_iff_padded_complement {Sym Digest Op : Type*}
    (S : ContentScheme Sym Digest Op) (c : Digest) (P w : List Sym) :
    Absent S c P w ↔
      S.commit w = c ∧ MatchesRegex w (Regex.paddedComplement (Regex.literal P)) := by
  unfold Absent
  change (S.commit w = c ∧ AbsentPlain w P) ↔
    (S.commit w = c ∧ ¬ MatchesRegex w (Regex.pad (Regex.literal P)))
  rw [absent_iff_padded_complement]

/-- **`P4` Regression Tooth (`whole_word_complement_is_not_absence`, `CERTIFICATES.md` §5 `P4`)**:
Whole-word complement `neg r` ACCEPTS `w = ['x', 'P', 'x']` at `r = .sym 'P'`, YET `'P'` occurs at
slice `[1, 2)` (`OccursInPlain ['x', 'P', 'x'] ['P']` is true, and `paddedComplement` rejects!). -/
theorem whole_word_complement_is_not_absence :
    ∃ (w : List Char) (r : Regex Char),
      Regex.derives w (.neg r) = true ∧
      (∃ i j : ℕ, Regex.derives (Slice w i j) r = true) ∧
      Regex.derives w (Regex.paddedComplement r) = false :=
  ⟨['x', 'P', 'x'], .sym 'P', by decide, ⟨1, 2, by decide⟩, by decide⟩

/-- Pattern-level form of the whole-word complement trap (`w ∉ lang P ∧ OccursInPlain w P`). -/
theorem whole_word_complement_pattern_falsifier :
    ∃ (w P : List Char),
      ¬ MatchesRegex w (Regex.literal P) ∧
      OccursInPlain w P ∧
      ¬ AbsentPlain w P := by
  refine ⟨['x', 'P', 'x'], ['P'], ?_, by decide, by decide⟩
  rw [Regex.matches_literal_iff]
  decide

/-! ## §5. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Selvage.commit_eq_implies_eq_or_bindBreak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_eq_implies_eq_or_bindBreak
/-- info: 'Minidregg.Selvage.idealContentScheme_no_bindBreak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealContentScheme_no_bindBreak
/-- info: 'Minidregg.Selvage.AdvOpeningScheme.committed_extract_bind_or_equivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdvOpeningScheme.committed_extract_bind_or_equivocation
/-- info: 'Minidregg.Selvage.openedFriFibreAdv_pins_or_equivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms openedFriFibreAdv_pins_or_equivocation
/-- info: 'Minidregg.Selvage.AdvOpeningScheme.prob_seam_with_bindAdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdvOpeningScheme.prob_seam_with_bindAdv
/-- info: 'Minidregg.Selvage.parity_bindingCommitment_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parity_bindingCommitment_isEmpty
/-- info: 'Minidregg.Selvage.parityAdvOpeningScheme_not_positionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parityAdvOpeningScheme_not_positionBinding
/-- info: 'Minidregg.Selvage.parityScheme_has_bindBreak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parityScheme_has_bindBreak
/-- info: 'Minidregg.Selvage.parity_zero_bindAdv_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parity_zero_bindAdv_refuted
/-- info: 'Minidregg.Selvage.substringAt_shift_falsifier_6sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substringAt_shift_falsifier_6sym
/-- info: 'Minidregg.Selvage.verifySubstringOpenings_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifySubstringOpenings_complete
/-- info: 'Minidregg.Selvage.substringAt_of_openings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substringAt_of_openings
/-- info: 'Minidregg.Selvage.substringAt_dropped_index_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substringAt_dropped_index_falsifier
/-- info: 'Minidregg.Selvage.Regex.derives_iff_matches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Regex.derives_iff_matches
/-- info: 'Minidregg.Selvage.absent_iff_padded_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_iff_padded_complement
/-- info: 'Minidregg.Selvage.whole_word_complement_is_not_absence' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms whole_word_complement_is_not_absence
/-- info: 'Minidregg.Selvage.whole_word_complement_pattern_falsifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_word_complement_pattern_falsifier

end Minidregg.Selvage
