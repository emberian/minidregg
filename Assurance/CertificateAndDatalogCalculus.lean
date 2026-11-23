/- Wave 11. Shared-commitment certificate rules and signed ground Datalog over a salted EDB. -/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Minidregg.Assurance.CertificateAndDatalogCalculus

set_option autoImplicit false
/-! ## Part A. The certificate judgment -/
section PartA
variable {Ω W C : Type} [Fintype Ω]

open Classical in
/-- Uniform probability over the finite verifier-coin space. -/
noncomputable def prob (p : Ω → Prop) : ℚ :=
  ((Finset.univ.filter p).card : ℚ) / (Fintype.card Ω : ℚ)
theorem prob_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : prob p ≤ prob q := by
  classical
  unfold prob
  gcongr with ω
  exact h ω
theorem prob_or_le (p q : Ω → Prop) : prob (fun ω => p ω ∨ q ω) ≤ prob p + prob q := by
  classical
  unfold prob
  rw [← add_div]; gcongr
  exact_mod_cast le_trans (Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hx ⊢
      exact hx) (Finset.card_union_le _ _)
theorem prob_def (p : Ω → Prop) [DecidablePred p] :
    prob p = ((Finset.univ.filter p).card : ℚ) / (Fintype.card Ω : ℚ) := by
  unfold prob; congr
theorem prob_eq_zero {p : Ω → Prop} (h : ∀ ω, ¬ p ω) : prob p = 0 := by
  classical
  unfold prob
  rw [Finset.filter_false_of_mem (fun x _ => h x)]; simp
/-- The opened witness opens `cm` and satisfies `R`. -/
def Good (commit : W → C) (R : W → Prop) (cm : C) (w : W) : Prop := commit w = cm ∧ R w
/-- `⊢ c : R @ (ε, Coll)`. -/
def Judg [Nonempty Ω] {K : Type} (commit : W → C) (verify : Ω → C → K → Bool) (extract : C → K → W)
    (R : W → Prop) (ε : ℚ) (Coll : C → K → Prop) : Prop :=
  ∀ cm c, prob (fun ω => verify ω cm c = true ∧ ¬ Good commit R cm (extract cm c) ∧
    ¬ Coll cm c) ≤ ε
variable [Nonempty Ω]
/-- An explicit commitment collision. -/
structure CollisionWitness (commit : W → C) where
  w₁ : W
  w₂ : W
  ne : w₁ ≠ w₂
  eq : commit w₁ = commit w₂
/-- Two different witnesses that both open `cm`. -/
def OpeningDisagreement (commit : W → C) (cm : C) (w₁ w₂ : W) : Prop :=
  w₁ ≠ w₂ ∧ commit w₁ = cm ∧ commit w₂ = cm
/-- Two different openings of one commitment ARE a collision, with those two witnesses. -/
theorem shared_commit_opening_binding {commit : W → C} {cm : C} {w₁ w₂ : W}
    (h : OpeningDisagreement commit cm w₁ w₂) :
    ∃ cw : CollisionWitness commit, cw.w₁ = w₁ ∧ cw.w₂ = w₂ :=
  ⟨⟨w₁, w₂, h.1, h.2.1.trans h.2.2.symm⟩, rfl, rfl⟩
/-- Conjunction verifier: both sub-verifiers, same coins, same commitment. -/
def pairVerify {K₁ K₂ : Type} (V₁ : Ω → C → K₁ → Bool) (V₂ : Ω → C → K₂ → Bool) :
    Ω → C → K₁ × K₂ → Bool := fun ω cm c => V₁ ω cm c.1 && V₂ ω cm c.2
/-- **Rule 1.** Conjunction over ONE commitment: errors add, and the opening disagreement of
the two extractors (a collision, by `shared_commit_opening_binding`) joins the collision set. -/
theorem cert_conj_shared_commit {K₁ K₂ : Type} {commit : W → C}
    {V₁ : Ω → C → K₁ → Bool} {V₂ : Ω → C → K₂ → Bool} {E₁ : C → K₁ → W} {E₂ : C → K₂ → W}
    {R₁ R₂ : W → Prop} {ε₁ ε₂ : ℚ} {C₁ : C → K₁ → Prop} {C₂ : C → K₂ → Prop}
    (h₁ : Judg commit V₁ E₁ R₁ ε₁ C₁) (h₂ : Judg commit V₂ E₂ R₂ ε₂ C₂) :
    Judg commit (pairVerify V₁ V₂) (fun cm c => E₁ cm c.1) (fun w => R₁ w ∧ R₂ w) (ε₁ + ε₂)
      (fun cm c => C₁ cm c.1 ∨ C₂ cm c.2 ∨
        OpeningDisagreement commit cm (E₁ cm c.1) (E₂ cm c.2)) := by
  intro cm c
  refine le_trans (prob_mono ?_) (le_trans (prob_or_le _ _) (add_le_add (h₁ cm c.1) (h₂ cm c.2)))
  rintro ω ⟨hv, hg, hc⟩; simp only [pairVerify, Bool.and_eq_true] at hv
  simp only [not_or] at hc
  obtain ⟨hc₁, hc₂, hd⟩ := hc
  by_cases g₁ : Good commit R₁ cm (E₁ cm c.1)
  · refine Or.inr ⟨hv.2, fun g₂ => hg ⟨g₁.1, g₁.2, ?_⟩, hc₂⟩
    by_cases heq : E₁ cm c.1 = E₂ cm c.2
    · show R₂ (E₁ cm c.1); rw [heq]; exact g₂.2
    · exact absurd ⟨heq, g₁.1, g₂.1⟩ hd
  · exact Or.inl ⟨hv.1, g₁, hc₁⟩
/-- **Rule 4a.** Weakening: stronger relation, larger budget, larger collision set. -/
theorem cert_implication_weaken {K : Type} {commit : W → C} {V : Ω → C → K → Bool}
    {E : C → K → W} {R R' : W → Prop} {ε ε' : ℚ} {Coll Coll' : C → K → Prop}
    (h : Judg commit V E R ε Coll) (hR : ∀ w, R w → R' w) (hε : ε ≤ ε')
    (hC : ∀ cm c, Coll cm c → Coll' cm c) : Judg commit V E R' ε' Coll' := by
  intro cm c; refine le_trans (prob_mono ?_) (le_trans (h cm c) hε)
  rintro ω ⟨hv, hg, hc⟩; exact ⟨hv, fun g => hg ⟨g.1, hR _ g.2⟩, fun h' => hc (hC _ _ h')⟩
/-- **Rule 2.** Push a judgment through a deterministic transducer `T` with zero extra loss: the
output object is `T (extract cm c)`, and the relation moves by `hT`. -/
theorem cert_transducer_pushforward {K W' : Type} {commit : W → C} {V : Ω → C → K → Bool}
    {E : C → K → W} {R₁ : W → Prop} {R₂ : W' → Prop} {ε : ℚ} {Coll : C → K → Prop}
    (T : W → W') (h : Judg commit V E R₁ ε Coll) (hT : ∀ x, R₁ x → R₂ (T x)) :
    Judg commit V E (fun w => R₂ (T w)) ε Coll :=
  cert_implication_weaken h hT le_rfl (fun _ _ h' => h')
/-- A relational transducer with unique runs moves "some run is good" to "every run is good". -/
theorem det_run_pushforward {X Y : Type} (Trel : X → Y → Prop) (R₁ : X → Prop) (R₂ : Y → Prop)
    (hdet : ∀ x y y', Trel x y → Trel x y' → y = y')
    (hsome : ∀ x, R₁ x → ∃ y, Trel x y ∧ R₂ y) : ∀ x y, R₁ x → Trel x y → R₂ y := by
  intro x y hx hxy; obtain ⟨y', hy', hR⟩ := hsome x hx
  rw [hdet x y y' hxy hy']; exact hR
/-- **Tooth.** Without unique runs a prover picks a bad run of a "some run is good" transducer. -/
theorem nondet_transducer_pushforward_fails :
    ∃ (Trel : Bool → Bool → Prop) (R₁ : Bool → Prop) (R₂ : Bool → Prop),
      (∀ x, R₁ x → ∃ y, Trel x y ∧ R₂ y) ∧ ∃ x y, R₁ x ∧ Trel x y ∧ ¬ R₂ y :=
  ⟨fun _ _ => True, fun _ => True, fun y => y = true,
    fun _ _ => ⟨true, trivial, rfl⟩, true, false, trivial, trivial, Bool.false_ne_true⟩
/-- Tagged-union verifier: the branch tag is part of the certificate (hence the transcript). -/
def sumVerify {K₁ K₂ : Type} (V₁ : Ω → C → K₁ → Bool) (V₂ : Ω → C → K₂ → Bool) :
    Ω → C → K₁ ⊕ K₂ → Bool := fun ω cm => Sum.elim (V₁ ω cm) (V₂ ω cm)
/-- **Rule 4b.** Disjunction with a transcript-bound branch tag costs `max ε₁ ε₂`. -/
theorem cert_union_or {K₁ K₂ : Type} {commit : W → C}
    {V₁ : Ω → C → K₁ → Bool} {V₂ : Ω → C → K₂ → Bool} {E₁ : C → K₁ → W} {E₂ : C → K₂ → W}
    {R₁ R₂ : W → Prop} {ε₁ ε₂ : ℚ} {C₁ : C → K₁ → Prop} {C₂ : C → K₂ → Prop}
    (h₁ : Judg commit V₁ E₁ R₁ ε₁ C₁) (h₂ : Judg commit V₂ E₂ R₂ ε₂ C₂) :
    Judg commit (sumVerify V₁ V₂) (fun cm => Sum.elim (E₁ cm) (E₂ cm)) (fun w => R₁ w ∨ R₂ w)
      (max ε₁ ε₂) (fun cm => Sum.elim (C₁ cm) (C₂ cm)) := by
  intro cm c
  cases c with
  | inl c =>
    exact le_trans (prob_mono fun ω ⟨hv, hg, hc⟩ => ⟨hv, fun g => hg ⟨g.1, Or.inl g.2⟩, hc⟩)
      (le_trans (h₁ cm c) (le_max_left _ _))
  | inr c =>
    exact le_trans (prob_mono fun ω ⟨hv, hg, hc⟩ => ⟨hv, fun g => hg ⟨g.1, Or.inr g.2⟩, hc⟩)
      (le_trans (h₂ cm c) (le_max_right _ _))
/-- The exact-opening verifier (the certificate is the witness): premise inhabitation. -/
def exactVerify [DecidableEq C] (commit : W → C) (R : W → Prop) [DecidablePred R] :
    Unit → C → W → Bool := fun _ cm w => decide (commit w = cm ∧ R w)
theorem exact_opening_judg [DecidableEq C] (commit : W → C) (R : W → Prop) [DecidablePred R] :
    Judg commit (exactVerify commit R) (fun _ w => w) R 0 (fun _ _ => False) := by
  intro cm c; refine le_of_eq (prob_eq_zero fun ω ⟨hv, hg, _⟩ => hg ?_)
  simpa [exactVerify, Good] using hv
/-- **Tooth.** "Co-location is not conjunction": two exact (ε = 0, collision-free, injective)
certificates on two DIFFERENT commitments both accept, yet no witness has both properties. -/
theorem independent_commits_allow_split_witness :
    Judg (id : Bool → Bool) (exactVerify id (· = true)) (fun _ w => w) (· = true) 0
        (fun _ _ => False) ∧
      Judg (id : Bool → Bool) (exactVerify id (· = false)) (fun _ w => w) (· = false) 0
        (fun _ _ => False) ∧
      exactVerify id (· = true) () true true = true ∧
      exactVerify id (· = false) () false false = true ∧
      (∀ w₁ w₂ : Bool, id w₁ = id w₂ → w₁ = w₂) ∧ ¬ ∃ w : Bool, w = true ∧ w = false :=
  ⟨exact_opening_judg _ _, exact_opening_judg _ _, by decide, by decide, fun _ _ h => h,
    fun ⟨w, h₁, h₂⟩ => Bool.false_ne_true (h₂.symm.trans h₁)⟩
/-- `k` uniform spot checks of an `N`-chunk log all miss the defect set `D`: exact count. -/
theorem audit_miss_prob {k N : ℕ} (D : Finset (Fin N)) :
    prob (fun ω : Fin k → Fin N => ∀ i, ω i ∉ D) = (((N - D.card : ℕ) : ℚ) / N) ^ k := by
  classical
  rw [prob_def]
  have hset : Finset.univ.filter (fun ω : Fin k → Fin N => ∀ i, ω i ∉ D) =
      Fintype.piFinset (fun _ => Dᶜ) := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_compl, Fintype.card_fin, div_pow]
  simp
theorem audit_miss_le {k N : ℕ} (hN : 0 < N) (D : Finset (Fin N)) {δ : ℚ}
    (hδ : δ * N ≤ D.card) :
    prob (fun ω : Fin k → Fin N => ∀ i, ω i ∉ D) ≤ (1 - δ) ^ k := by
  rw [audit_miss_prob]; have hDN : D.card ≤ N := by simpa using D.card_le_univ
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  apply pow_le_pow_left₀ (by positivity)
  rw [Nat.cast_sub hDN, sub_div, div_self hNq.ne']
  have : δ ≤ (D.card : ℚ) / N := by rw [le_div_iff₀ hNq]; exact hδ
  linarith
/-- The relation "fewer than `δ·N` defective chunks". -/
def FewDefects {N : ℕ} {Ch : Type} (bad : Ch → Bool) (δ : ℚ) (w : Fin N → Ch) : Prop :=
  (((Finset.univ.filter fun i => bad (w i) = true).card : ℕ) : ℚ) < δ * N
/-- The sampled-audit verifier: the opening must open `cm`, and the `k` sampled chunks pass. -/
def auditVerify {N k : ℕ} {Ch K : Type} [DecidableEq C] (commit : (Fin N → Ch) → C)
    (E : C → K → (Fin N → Ch)) (bad : Ch → Bool) : (Fin k → Fin N) → C → K → Bool :=
  fun ω cm c => decide (commit (E cm c) = cm) && decide (∀ i, bad (E cm c (ω i)) = false)
/-- **Rule 3.** Sampled audit: `⊢ c : FewDefects δ @ ((1-δ)^k, ∅)`. -/
theorem cert_sampled_audit {N k : ℕ} [NeZero N] {Ch K : Type} [DecidableEq C]
    (commit : (Fin N → Ch) → C) (E : C → K → (Fin N → Ch)) (bad : Ch → Bool) {δ : ℚ}
    (hδ1 : δ ≤ 1) :
    Judg commit (auditVerify (k := k) commit E bad) E (FewDefects bad δ) ((1 - δ) ^ k)
      (fun _ _ => False) := by
  classical
  intro cm c
  by_cases hR : FewDefects bad δ (E cm c)
  · refine le_trans (le_of_eq (prob_eq_zero ?_)) (pow_nonneg (by linarith) k)
    rintro ω ⟨hv, hg, -⟩; simp only [auditVerify, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hg ⟨hv.1, hR⟩
  · set Dset : Finset (Fin N) := Finset.univ.filter fun j => bad (E cm c j) = true
    have hb : prob (fun ω : Fin k → Fin N => ∀ i, ω i ∉ Dset) ≤ (1 - δ) ^ k :=
      audit_miss_le (NeZero.pos N) Dset (by simpa [FewDefects, Dset] using hR)
    refine le_trans (prob_mono ?_) hb
    rintro ω ⟨hv, -, -⟩ i; simp only [auditVerify, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Dset, hv.2 i]
/-- A DFA run over a byte word accepts. -/
def DfaAccepts {Q B : Type} (δ : Q → B → Q) (q₀ : Q) (acc : Q → Bool) (w : List B) : Prop :=
  acc (w.foldl δ q₀) = true
/-- **Rule 5.** A byte-level DFA certificate and a canonical BPE token-stream certificate over ONE
byte commitment compose; because `decode ∘ encode = id`, the DFA property is carried to
`decode toks`, the bytes the claimed token stream denotes. -/
theorem cert_bpe_byte_weld {B Tok Q K₁ K₂ : Type} {commit : List B → C}
    {V₁ : Ω → C → K₁ → Bool} {V₂ : Ω → C → K₂ → Bool} {E₁ : C → K₁ → List B}
    {E₂ : C → K₂ → List B} {ε₁ ε₂ : ℚ} {C₁ : C → K₁ → Prop} {C₂ : C → K₂ → Prop}
    (δ : Q → B → Q) (q₀ : Q) (acc : Q → Bool) (encode : List B → List Tok)
    (decode : List Tok → List B) (toks : List Tok) (hcanon : ∀ w, decode (encode w) = w)
    (hdfa : Judg commit V₁ E₁ (DfaAccepts δ q₀ acc) ε₁ C₁)
    (hbpe : Judg commit V₂ E₂ (fun w => encode w = toks) ε₂ C₂) :
    Judg commit (pairVerify V₁ V₂) (fun cm c => E₁ cm c.1)
      (fun w => encode w = toks ∧ DfaAccepts δ q₀ acc (decode toks)) (ε₁ + ε₂)
      (fun cm c => C₁ cm c.1 ∨ C₂ cm c.2 ∨
        OpeningDisagreement commit cm (E₁ cm c.1) (E₂ cm c.2)) :=
  cert_implication_weaken (cert_conj_shared_commit hdfa hbpe)
    (fun w ⟨hd, he⟩ => ⟨he, by rw [← he, hcanon]; exact hd⟩) le_rfl (fun _ _ h => h)

theorem audit_two_draws :
    prob (fun ω : Fin 2 → Fin 4 => ∀ i, ω i ∉ ({0} : Finset (Fin 4))) = 9/16 := by
  rw [audit_miss_prob, Finset.card_singleton]; norm_num
end PartA
/-! ## Part B. Stratified Datalog over a Merkelized EDB -/
section Semantics
variable {A : Type}

/-- A ground rule `head :- pos, ¬neg`. -/
structure GR (A : Type) where
  head : A
  pos : List A
  neg : List A
deriving DecidableEq
/-- Least derivations from `rules` over `edb`, with negation read from the oracle `N`. -/
inductive Deriv (rules : List (GR A)) (isEdb : A → Bool) (edb : A → Prop) (N : A → Prop) :
    A → Prop
  | base {a : A} : isEdb a = true → edb a → Deriv rules isEdb edb N a
  | rule (gr : GR A) : gr ∈ rules → (∀ b ∈ gr.pos, Deriv rules isEdb edb N b) →
      (∀ b ∈ gr.neg, ¬ N b) → Deriv rules isEdb edb N gr.head
/-- A stratified ground program. -/
structure Prog (A : Type) where
  rules : List (GR A)
  isEdb : A → Bool
  st : A → ℕ
  wf_head : ∀ gr ∈ rules, isEdb gr.head = false
  wf_pos : ∀ gr ∈ rules, ∀ b ∈ gr.pos, st b ≤ st gr.head
  wf_neg : ∀ gr ∈ rules, ∀ b ∈ gr.neg, st b < st gr.head
theorem deriv_congr_below (P : Prog A) (edb : A → Prop) {N N' : A → Prop} {s : ℕ}
    (hN : ∀ b, P.st b < s → (N b ↔ N' b)) {a : A} (h : Deriv P.rules P.isEdb edb N a)
    (hs : P.st a ≤ s) : Deriv P.rules P.isEdb edb N' a := by
  induction h with
  | base he hd => exact .base he hd
  | rule gr hmem _ hneg ih =>
    exact .rule gr hmem (fun b hb => ih b hb (le_trans (P.wf_pos gr hmem b hb) hs))
      (fun b hb hN' => hneg b hb ((hN b (lt_of_lt_of_le (P.wf_neg gr hmem b hb) hs)).2 hN'))
/-- The stratified model, by well-founded recursion on the stratum. -/
def SM (P : Prog A) (edb : A → Prop) (a : A) : Prop :=
  Deriv P.rules P.isEdb edb (fun b => if _h : P.st b < P.st a then SM P edb b else False) a
termination_by P.st a
theorem SM_fix (P : Prog A) (edb : A → Prop) (a : A) :
    SM P edb a ↔ Deriv P.rules P.isEdb edb (SM P edb) a := by
  conv_lhs => rw [SM]
  exact ⟨fun h => deriv_congr_below P edb (s := P.st a) (fun b hb => by simp [hb]) h le_rfl,
    fun h => deriv_congr_below P edb (s := P.st a) (fun b hb => by simp [hb]) h le_rfl⟩
/-- A stratified model: a fixed point of least derivation. -/
def IsStratModel (P : Prog A) (edb : A → Prop) (M : A → Prop) : Prop :=
  ∀ a, M a ↔ Deriv P.rules P.isEdb edb M a
theorem SM_isStratModel (P : Prog A) (edb : A → Prop) : IsStratModel P edb (SM P edb) :=
  SM_fix P edb
/-- Uniqueness: every stratified model is `SM`. -/
theorem stratModel_unique (P : Prog A) (edb : A → Prop) {M : A → Prop}
    (hM : IsStratModel P edb M) (a : A) : M a ↔ SM P edb a := by
  suffices h : ∀ n a, P.st a = n → (M a ↔ SM P edb a) from h _ a rfl
  intro n; induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have hb : ∀ b, P.st b < P.st a → (M b ↔ SM P edb b) := fun b hb => ih _ (ha ▸ hb) b rfl
    rw [hM a, SM_fix P edb a]; exact ⟨fun h => deriv_congr_below P edb hb h le_rfl,
      fun h => deriv_congr_below P edb (fun b h' => (hb b h').symm) h le_rfl⟩
/-- Minimality: `SM` lies inside every set closed under the rules (negation read from `SM`). -/
theorem stratModel_least (P : Prog A) (edb : A → Prop) (X : A → Prop)
    (hbase : ∀ a, P.isEdb a = true → edb a → X a)
    (hrule : ∀ gr ∈ P.rules, (∀ b ∈ gr.pos, X b) → (∀ b ∈ gr.neg, ¬ SM P edb b) → X gr.head)
    (a : A) (h : SM P edb a) : X a := by
  rw [SM_fix] at h; induction h with
  | base he hd => exact hbase _ he hd
  | rule gr hmem _ hneg ih => exact hrule gr hmem ih hneg
/-- **Falsifier.** `p :- ¬p`: no stratum map exists, and no fixed point of derivation exists. -/
theorem unstratified_negation_no_model (p : A) (edb : A → Prop) :
    (¬ ∃ st : A → ℕ, ∀ gr ∈ [(⟨p, [], [p]⟩ : GR A)], ∀ b ∈ gr.neg, st b < st gr.head) ∧
      ¬ ∃ M : A → Prop, ∀ a, M a ↔ Deriv [⟨p, [], [p]⟩] (fun _ => false) edb M a := by
  refine ⟨fun ⟨st, h⟩ => lt_irrefl _ (h _ (List.mem_singleton_self _) p (by simp)), ?_⟩
  rintro ⟨M, hM⟩; have hnot : ¬ M p := fun hp => by
    have hd := (hM p).1 hp
    cases hd with
    | base he _ => exact Bool.false_ne_true he
    | rule gr hmem _ hneg =>
      rw [List.mem_singleton] at hmem; rw [hmem] at hneg; exact hneg _ (by simp) hp
  exact hnot ((hM p).2 (.rule ⟨p, [], [p]⟩ (List.mem_singleton_self _) (by simp)
    (by simpa using hnot)))
end Semantics
section Merkle
variable {K S D : Type}

/-- Domain-separated hash inputs: salted leaves and internal nodes never share an input. -/
inductive HIn (K S D : Type) where
  | leaf (k : K) (s : S)
  | node (l r : D)
deriving DecidableEq
/-- A collision of the hash. -/
def HasCollision (H : HIn K S D → D) : Prop := ∃ x y, x ≠ y ∧ H x = H y
/-- Root of the `2^d`-leaf tree (MSB-first split). -/
def mroot (H : HIn K S D → D) : ℕ → (ℕ → K × S) → D
  | 0, f => H (.leaf (f 0).1 (f 0).2)
  | d + 1, f => H (.node (mroot H d f) (mroot H d fun i => f (2 ^ d + i)))
/-- Recompute a root from a leaf, its index and a top-down sibling path. -/
def recompute (H : HIn K S D → D) : ℕ → ℕ → K × S → List D → D
  | 0, _, l, _ => H (.leaf l.1 l.2)
  | _ + 1, _, l, [] => H (.leaf l.1 l.2)
  | d + 1, i, l, sib :: rest =>
    if i < 2 ^ d then H (.node (recompute H d i l rest) sib)
    else H (.node sib (recompute H d (i - 2 ^ d) l rest))
/-- The honest path. -/
def mkPath (H : HIn K S D → D) : ℕ → (ℕ → K × S) → ℕ → List D
  | 0, _, _ => []
  | d + 1, f, i =>
    if i < 2 ^ d then mroot H d (fun j => f (2 ^ d + j)) :: mkPath H d f i
    else mroot H d f :: mkPath H d (fun j => f (2 ^ d + j)) (i - 2 ^ d)
theorem mkPath_length (H : HIn K S D → D) (d : ℕ) (f : ℕ → K × S) (i : ℕ) :
    (mkPath H d f i).length = d := by
  induction d generalizing i f with
  | zero => rfl
  | succ d ih => unfold mkPath; split <;> simp [ih]
theorem recompute_mkPath (H : HIn K S D → D) :
    ∀ d f i, i < 2 ^ d → recompute H d i (f i) (mkPath H d f i) = mroot H d f
  | 0, f, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    rfl
  | d + 1, f, i, hi => by
    by_cases h : i < 2 ^ d
    · simp [mkPath, recompute, h, recompute_mkPath H d f i h, mroot]
    · have h2 : i - 2 ^ d < 2 ^ d := by rw [pow_succ] at hi; omega
      have := recompute_mkPath H d (fun j => f (2 ^ d + j)) (i - 2 ^ d) h2
      rw [Nat.add_sub_cancel' (by omega)] at this; simp [mkPath, recompute, h, this, mroot]
/-- **Position binding.** An accepted opening is the committed leaf, or a collision exists. -/
theorem merkle_position_binding (H : HIn K S D → D) :
    ∀ d f i l p, i < 2 ^ d → recompute H d i l p = mroot H d f → l = f i ∨ HasCollision H
  | 0, f, i, l, p, hi, h => by
    obtain rfl : i = 0 := by simpa using hi
    by_cases e : l = f 0
    · exact .inl e
    · refine .inr ⟨_, _, fun he => e ?_, h⟩
      injection he with h1 h2; exact Prod.ext h1 h2
  | d + 1, f, i, l, [], _, h => by
    simp only [recompute, mroot] at h
    exact .inr ⟨_, _, by simp, h⟩
  | d + 1, f, i, l, sib :: rest, hi, h => by
    simp only [recompute, mroot] at h
    split_ifs at h with hlt
    · by_cases e : HIn.node (K := K) (S := S) (recompute H d i l rest) sib =
          .node (mroot H d f) (mroot H d fun j => f (2 ^ d + j))
      · injection e with e1 _
        exact merkle_position_binding H d f i l rest hlt e1
      · exact .inr ⟨_, _, e, h⟩
    · have h2 : i - 2 ^ d < 2 ^ d := by rw [pow_succ] at hi; omega
      by_cases e : HIn.node (K := K) (S := S) sib (recompute H d (i - 2 ^ d) l rest) =
          .node (mroot H d f) (mroot H d fun j => f (2 ^ d + j))
      · injection e with _ e2
        have := merkle_position_binding H d (fun j => f (2 ^ d + j)) (i - 2 ^ d) l rest h2 e2
        rwa [Nat.add_sub_cancel' (by omega)] at this
      · exact .inr ⟨_, _, e, h⟩
end Merkle
section Certs
variable {A K S D : Type} [DecidableEq A] [LinearOrder K] [DecidableEq D]

/-- Some pair of positions `i ≤ j` is out of order. -/
def Unsorted (d : ℕ) (f : ℕ → K × S) : Prop := ∃ i j, i ≤ j ∧ j < 2 ^ d ∧ (f j).1 < (f i).1
/-- The EDB the leaf vector `f` denotes. -/
def edbOf (enc : A → K) (d : ℕ) (f : ℕ → K × S) (a : A) : Prop := ∃ j < 2 ^ d, (f j).1 = enc a
/-- Claim justifications. -/
inductive Just (A K S D : Type) where
  | memb (j : ℕ) (s : S) (path : List D)
  | rule (gr : GR A)
  | gap (i : ℕ) (lL : K × S) (pL : List D) (lR : K × S) (pR : List D)
  | unf (U : List A)
deriving DecidableEq
/-- A ranked claim `atom` / `¬atom`. -/
structure Claim (A K S D : Type) where
  atom : A
  pos : Bool
  rank : ℕ
  just : Just A K S D
deriving DecidableEq
/-- The certificate holds a claim of sign `sg` on `b` of rank strictly below `r`. -/
def hasLit (cert : List (Claim A K S D)) (b : A) (sg : Bool) (r : ℕ) : Bool :=
  cert.any fun c => decide (c.atom = b) && decide (c.pos = sg) && decide (c.rank < r)
/-- Local check of one claim. -/
def checkClaim (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ) (root : D)
    (cert : List (Claim A K S D)) (c : Claim A K S D) : Bool :=
  match c.pos, c.just with
  | true, .memb j s p => P.isEdb c.atom && decide (j < 2 ^ d) && decide (p.length = d) &&
      decide (recompute H d j (enc c.atom, s) p = root)
  | true, .rule gr => !P.isEdb c.atom && decide (gr ∈ P.rules) && decide (gr.head = c.atom) &&
      gr.pos.all (fun b => hasLit cert b true c.rank) &&
      gr.neg.all (fun b => hasLit cert b false c.rank)
  | false, .gap i lL pL lR pR => P.isEdb c.atom && decide (i + 1 < 2 ^ d) &&
      decide (pL.length = d) && decide (pR.length = d) &&
      decide (recompute H d i lL pL = root) && decide (recompute H d (i + 1) lR pR = root) &&
      decide (lL.1 < enc c.atom) && decide (enc c.atom < lR.1)
  | false, .unf U => !P.isEdb c.atom && decide (c.atom ∈ U) && U.all (fun u => !P.isEdb u) &&
      P.rules.all (fun gr => !decide (gr.head ∈ U) ||
        gr.pos.any (fun b => decide (b ∈ U) || hasLit cert b false c.rank) ||
        gr.neg.any (fun b => hasLit cert b true c.rank))
  | _, _ => false
/-- The standalone verifier: every claim checks, and the query literal is claimed. -/
def verifyDatalogCert (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ) (root : D)
    (q : A) (sg : Bool) (cert : List (Claim A K S D)) : Bool :=
  cert.all (checkClaim P H enc d root cert) &&
    cert.any fun c => decide (c.atom = q) && decide (c.pos = sg)
omit [LinearOrder K] [DecidableEq D] in theorem hasLit_iff {cert : List (Claim A K S D)} {b : A} {sg : Bool} {r : ℕ} :
    hasLit cert b sg r = true ↔ ∃ c ∈ cert, c.atom = b ∧ c.pos = sg ∧ c.rank < r := by
  simp [hasLit, and_assoc]
omit [DecidableEq A] in theorem SM_edb (P : Prog A) (edb : A → Prop) {a : A} (he : P.isEdb a = true) :
    SM P edb a ↔ edb a := by
  rw [SM_fix]; refine ⟨fun h => ?_, fun hd => .base he hd⟩
  cases h with
  | base _ hd => exact hd
  | rule gr hmem _ _ => rw [P.wf_head gr hmem] at he; exact absurd he Bool.false_ne_true
/-- Agreement with the source vector, restricted to the openings actually in this claim. -/
def Faithful (enc : A → K) (f : ℕ → K × S) (c : Claim A K S D) : Prop :=
  match c.just with
  | .memb j s _ => (enc c.atom, s) = f j
  | .gap i l _ r _ => l = f i ∧ r = f (i+1)
  | _ => True
theorem checked_opening_or_collision (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ)
    (f : ℕ → K × S) (cs : List (Claim A K S D)) (c : Claim A K S D)
    (hc : checkClaim P H enc d (mroot H d f) cs c = true) : Faithful enc f c ∨ HasCollision H := by
  obtain ⟨a, sg, rank, j⟩ := c
  cases sg <;> cases j <;> simp_all only [Faithful, checkClaim, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc, true_or]
  · rcases merkle_position_binding H d f _ _ _ (by omega) hc.2.2.2.2.1 with hl | bad
    · exact (merkle_position_binding H d f _ _ _ hc.2.1 hc.2.2.2.2.2.1).imp (fun hr => ⟨hl, hr⟩) id
    · exact .inr bad
  · exact merkle_position_binding H d f _ _ _ hc.2.1 hc.2.2.2

/-- Soundness for faithful openings on a sorted EDB, by strong induction on rank. -/
theorem claims_sound (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ)
    (f : ℕ → K × S) (cert : List (Claim A K S D)) (faith : ∀ c ∈ cert, Faithful enc f c)
    (hs : ¬ Unsorted d f) (hall : cert.all (checkClaim P H enc d (mroot H d f) cert) = true) :
    ∀ c ∈ cert, (SM P (edbOf enc d f) c.atom ↔ c.pos = true) := by
  set M := SM P (edbOf enc d f)
  rw [List.all_eq_true] at hall
  suffices h : ∀ r, ∀ c ∈ cert, c.rank = r → (M c.atom ↔ c.pos = true) from
    fun c hc => h _ c hc rfl
  intro r; induction r using Nat.strong_induction_on with
  | _ r ih =>
  have lit : ∀ b sg, hasLit cert b sg r = true → (M b ↔ sg = true) := fun b sg hl => by
    obtain ⟨c', hc', rfl, rfl, hr⟩ := hasLit_iff.1 hl
    exact ih _ hr c' hc' rfl
  rintro ⟨a, pos, r', j⟩ hc rfl; have hck := hall _ hc; have agree := faith _ hc
  cases pos <;> cases j <;>
    simp only [checkClaim, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, List.any_eq_true, and_assoc] at hck
  case true.memb j s p =>
    obtain ⟨he, hj, _, _⟩ := hck
    have eqLeaf : (enc a, s) = f j := agree
    simp only [iff_true]; exact (SM_edb P _ he).2 ⟨j, hj, by rw [← eqLeaf]⟩
  case true.rule gr =>
    obtain ⟨_, hmem, hhead, hpos, hneg⟩ := hck
    simp only [iff_true]; rw [← hhead]
    refine (SM_fix P _ _).2 (.rule gr hmem (fun b hb => (SM_fix P _ b).1 ((lit b true (hpos b hb)).2 rfl))
      (fun b hb hb' => Bool.false_ne_true ((lit b false (hneg b hb)).1 hb')))
  case false.gap i lL pL lR pR =>
    obtain ⟨he, hi, _, _, _, _, hlt1, hlt2⟩ := hck
    obtain ⟨eL, eR⟩ : lL = f i ∧ lR = f (i + 1) := agree
    subst eL eR; simp only [Bool.false_eq_true, iff_false]
    intro hMa; obtain ⟨j, hj, hjk⟩ := (SM_edb P _ he).1 hMa
    by_cases hji : j ≤ i
    · exact hs ⟨j, i, hji, by omega, by rw [hjk]; exact hlt1⟩
    · exact hs ⟨i + 1, j, by omega, hj, by rw [hjk]; exact hlt2⟩
  case false.unf U =>
    obtain ⟨_, haU, hU, hrules⟩ := hck
    simp only [Bool.false_eq_true, iff_false]; intro hMa
    replace hMa := (SM_fix P _ a).1 hMa
    suffices hU' : ∀ x, Deriv P.rules P.isEdb (edbOf enc d f) M x → x ∈ U → False from
      hU' a hMa haU
    intro x hx; induction hx with
    | base he _ => intro hxU; rw [hU _ hxU] at he; exact Bool.false_ne_true he
    | rule gr hmem hpos hneg ihd =>
      intro hxU; rcases hrules gr hmem with (h | h) | h
      · exact absurd hxU (by simpa using h)
      · obtain ⟨b, hb, hbU | hbl⟩ := h
        · exact ihd b hb hbU
        · exact Bool.false_ne_true ((lit b false hbl).1 ((SM_fix P _ b).2 (hpos b hb)))
      · obtain ⟨b, hb, hbl⟩ := h
        exact hneg b hb ((lit b true hbl).2 rfl)
/-- **Keystone (soundness).** Acceptance implies the literal holds in the stratified model of the
EDB committed by `root = mroot H d f`, or a hash collision exists, or the leaves are unsorted. -/
theorem datalog_cert_sound (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ)
    (f : ℕ → K × S) (root : D) (q : A) (sg : Bool) (cert : List (Claim A K S D))
    (hv : verifyDatalogCert P H enc d root q sg cert = true) (hroot : mroot H d f = root) :
    (SM P (edbOf enc d f) q ↔ sg = true) ∨
      (∃ c ∈ cert, ¬ Faithful enc f c ∧ HasCollision H) ∨ Unsorted d f := by
  subst root
  simp only [verifyDatalogCert, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hall, c, hc, rfl, rfl⟩ := hv
  by_cases hu : Unsorted d f
  · exact .inr (.inr hu)
  by_cases hf : ∀ x ∈ cert, Faithful enc f x
  · exact .inl (claims_sound P H enc d f cert hf hu hall c hc)
  push Not at hf
  obtain ⟨x, hx, bad⟩ := hf
  exact .inr (.inl ⟨x, hx, bad, (checked_opening_or_collision P H enc d f cert x
    (List.all_eq_true.1 hall x hx)).resolve_left bad⟩)

/-- Opened-turn specialization. The word opened with the salt determines the DFA input, the
canonical tokens and the policy query. The second root commits to the policy EDB. -/
theorem cert_opened_byte_turn {B Salt Tok Q C : Type} [DecidableEq C] [DecidableEq Tok]
    (commit : Salt × List B → C) (step : Q → B → Q) (start : Q) (acc : Q → Bool)
    (encode : List B → List Tok) (decode : List Tok → List B) (canon : ∀ w, decode (encode w) = w)
    (readQuery : List B → Option A) (q : A) (toks : List Tok)
    (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ) (f : ℕ → K × S) :
    Judg commit (fun (_ : Unit) cm (c : (Salt × List B) × List (Claim A K S D)) =>
      decide (commit c.1 = cm) && acc (c.1.2.foldl step start) && decide (encode c.1.2 = toks) &&
      decide (readQuery c.1.2 = some q) && verifyDatalogCert P H enc d (mroot H d f) q true c.2)
      (fun _ c => c.1) (fun w => encode w.2 = toks ∧ DfaAccepts step start acc (decode toks) ∧
        readQuery w.2 = some q ∧ SM P (edbOf enc d f) q) 0
      (fun _ c => (∃ x ∈ c.2, ¬ Faithful enc f x ∧ HasCollision H) ∨ Unsorted d f) := by
  intro cm c
  apply le_of_eq
  apply prob_eq_zero
  rintro _ ⟨hv, bad, clean⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨opened, run⟩, tokens⟩, query⟩, cert⟩ := hv
  have model := ((datalog_cert_sound P H enc d f _ q true c.2 cert rfl).resolve_right clean).2 rfl
  exact bad ⟨opened, tokens, by simpa [DfaAccepts, ← tokens, canon] using run, query, model⟩
/-! ### Completeness: the canonical certificate -/
section Complete
open Classical
variable (P : Prog A) (H : HIn K S D → D) (enc : A → K) (d : ℕ) (f : ℕ → K × S) (q : A)

/-- Depth-bounded derivation (negation read from `SM`). -/
def DerivN : ℕ → A → Prop
  | 0, _ => False
  | n + 1, a => (P.isEdb a = true ∧ edbOf enc d f a) ∨ ∃ gr ∈ P.rules, gr.head = a ∧
      (∀ b ∈ gr.pos, DerivN n b) ∧ ∀ b ∈ gr.neg, ¬ SM P (edbOf enc d f) b
omit [DecidableEq A] [LinearOrder K] in theorem derivN_mono : ∀ n m a, n ≤ m → DerivN P enc d f n a → DerivN P enc d f m a
  | 0, _, _, _, h => h.elim
  | n + 1, m + 1, a, hnm, h => by
    rcases h with h | ⟨gr, hg, hh, hp, hn⟩
    · exact .inl h
    · exact .inr ⟨gr, hg, hh, fun b hb => derivN_mono n m b (by omega) (hp b hb), hn⟩
  | _ + 1, 0, _, hnm, _ => absurd hnm (by omega)
omit [DecidableEq A] [LinearOrder K] in theorem derivN_of_SM {a : A} (h : SM P (edbOf enc d f) a) : ∃ n, DerivN P enc d f n a := by
  rw [SM_fix] at h; induction h with
  | base he hd => exact ⟨1, .inl ⟨he, hd⟩⟩
  | rule gr hmem _ hneg ih =>
    suffices ∀ l : List A, (∀ b ∈ l, ∃ n, DerivN P enc d f n b) →
        ∃ n, ∀ b ∈ l, DerivN P enc d f n b by
      obtain ⟨n, hn⟩ := this gr.pos ih
      exact ⟨n + 1, .inr ⟨gr, hmem, rfl, hn, hneg⟩⟩
    intro l; induction l with
    | nil => exact fun _ => ⟨0, by simp⟩
    | cons x xs ihl =>
      intro hl; obtain ⟨n₁, h₁⟩ := hl x (by simp)
      obtain ⟨n₂, h₂⟩ := ihl fun b hb => hl b (by simp [hb])
      refine ⟨max n₁ n₂, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact derivN_mono P enc d f _ _ _ (le_max_left _ _) h₁
      · exact derivN_mono P enc d f _ _ _ (le_max_right _ _) (h₂ b hb)
omit [DecidableEq A] [LinearOrder K] in theorem SM_of_derivN : ∀ n a, DerivN P enc d f n a → SM P (edbOf enc d f) a
  | 0, _, h => h.elim
  | n + 1, a, h => by
    rw [SM_fix]; rcases h with ⟨he, hd⟩ | ⟨gr, hg, rfl, hp, hn⟩
    · exact .base he hd
    · exact .rule gr hg (fun b hb => (SM_fix P _ b).1 (SM_of_derivN n b (hp b hb))) hn
/-- The least derivation depth. -/
noncomputable def lvl (a : A) : ℕ :=
  if h : ∃ n, DerivN P enc d f n a then Nat.find h else 0
/-- The atoms a canonical certificate covers. -/
def univ : List A := q :: P.rules.flatMap fun gr => gr.head :: (gr.pos ++ gr.neg)
/-- Rank-block width. -/
noncomputable def width : ℕ := (univ P q).foldr (fun a m => max (lvl P enc d f a) m) 0 + 3
/-- Rank of a positive claim. -/
noncomputable def rkPos (a : A) : ℕ := P.st a * width P enc d f q + 2 + lvl P enc d f a
/-- Rank of a negative claim. -/
noncomputable def rkNeg (a : A) : ℕ :=
  if P.isEdb a = true then 0 else P.st a * width P enc d f q + 1
/-- The unfounded set of stratum `s`. -/
noncomputable def uSet (s : ℕ) : List A :=
  (univ P q).filter fun c => P.isEdb c = false ∧ ¬ SM P (edbOf enc d f) c ∧ P.st c = s
/-- Index of a membership opening. -/
noncomputable def membIdx (a : A) : ℕ := if h : edbOf enc d f a then Classical.choose h else 0
/-- Left index of an adjacent gap. -/
noncomputable def gapIdx (a : A) : ℕ :=
  if h : ∃ i, i + 1 < 2 ^ d ∧ (f i).1 < enc a ∧ enc a < (f (i + 1)).1 then Classical.choose h
  else 0
/-- A rule instance at depth `lvl a`. -/
noncomputable def ruleOf (a : A) : GR A :=
  if h : ∃ gr ∈ P.rules, gr.head = a ∧ (∀ b ∈ gr.pos, DerivN P enc d f (lvl P enc d f a - 1) b) ∧
    ∀ b ∈ gr.neg, ¬ SM P (edbOf enc d f) b then Classical.choose h else ⟨a, [], []⟩
/-- The canonical claim for one atom. -/
noncomputable def genClaim (a : A) : Claim A K S D :=
  if SM P (edbOf enc d f) a then
    if P.isEdb a = true then
      ⟨a, true, rkPos P enc d f q a, .memb (membIdx enc d f a) (f (membIdx enc d f a)).2
        (mkPath H d f (membIdx enc d f a))⟩
    else ⟨a, true, rkPos P enc d f q a, .rule (ruleOf P enc d f a)⟩
  else
    if P.isEdb a = true then
      ⟨a, false, 0, .gap (gapIdx enc d f a) (f (gapIdx enc d f a))
        (mkPath H d f (gapIdx enc d f a)) (f (gapIdx enc d f a + 1))
        (mkPath H d f (gapIdx enc d f a + 1))⟩
    else ⟨a, false, rkNeg P enc d f q a, .unf (uSet P enc d f q (P.st a))⟩
/-- The canonical certificate. -/
noncomputable def genCert : List (Claim A K S D) := (univ P q).map (genClaim P H enc d f q)
omit [DecidableEq D] in theorem genClaim_fields (a : A) : (genClaim P H enc d f q a).atom = a ∧
    (genClaim P H enc d f q a).pos = decide (SM P (edbOf enc d f) a) ∧
    (genClaim P H enc d f q a).rank = (if SM P (edbOf enc d f) a then rkPos P enc d f q a
      else rkNeg P enc d f q a) := by
  unfold genClaim; split_ifs with h1 h2 h2 <;> simp_all [rkNeg]
variable {P H enc d f q}
omit [DecidableEq A] [LinearOrder K] in theorem membIdx_spec {a : A} (h : edbOf enc d f a) :
    membIdx enc d f a < 2 ^ d ∧ (f (membIdx enc d f a)).1 = enc a := by
  unfold membIdx; split_ifs; exact Classical.choose_spec h
omit [DecidableEq A] in theorem gapIdx_spec {a : A} (h : ∃ i, i + 1 < 2 ^ d ∧ (f i).1 < enc a ∧ enc a < (f (i + 1)).1) :
    gapIdx enc d f a + 1 < 2 ^ d ∧ (f (gapIdx enc d f a)).1 < enc a ∧
      enc a < (f (gapIdx enc d f a + 1)).1 := by
  unfold gapIdx; split_ifs; exact Classical.choose_spec h
omit [LinearOrder K] in theorem ruleOf_spec {a : A} (h : ∃ gr ∈ P.rules, gr.head = a ∧
    (∀ b ∈ gr.pos, DerivN P enc d f (lvl P enc d f a - 1) b) ∧
    ∀ b ∈ gr.neg, ¬ SM P (edbOf enc d f) b) :
    ruleOf P enc d f a ∈ P.rules ∧ (ruleOf P enc d f a).head = a ∧
      (∀ b ∈ (ruleOf P enc d f a).pos, DerivN P enc d f (lvl P enc d f a - 1) b) ∧
      ∀ b ∈ (ruleOf P enc d f a).neg, ¬ SM P (edbOf enc d f) b := by
  unfold ruleOf; split_ifs; exact Classical.choose_spec h
omit [DecidableEq A] [LinearOrder K] in theorem lvl_le_width {a : A} (ha : a ∈ univ P q) : lvl P enc d f a + 3 ≤ width P enc d f q := by
  unfold width
  suffices ∀ l : List A, a ∈ l → lvl P enc d f a ≤ l.foldr (fun a m => max (lvl P enc d f a) m) 0
    from by have := this _ ha; omega
  intro l hl; induction l with
  | nil => simp at hl
  | cons x xs ih =>
    rcases List.mem_cons.1 hl with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)
theorem rank_lt {s s' x y W : ℕ} (hs : s ≤ s') (heq : s = s' → x < y) (hx : x < W) :
    s * W + x < s' * W + y := by
  rcases Nat.lt_or_eq_of_le hs with h | rfl
  · have : (s + 1) * W ≤ s' * W := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this; omega
  · have := heq rfl; omega
omit [DecidableEq A] in theorem mem_univ_body {gr : GR A} (hg : gr ∈ P.rules) {b : A} (hb : b ∈ gr.pos ∨ b ∈ gr.neg ∨
    b = gr.head) : b ∈ univ P q := by
  simp only [univ, List.mem_cons, List.mem_flatMap, List.mem_append]
  exact .inr ⟨gr, hg, by tauto⟩
omit [DecidableEq D] in theorem genClaim_mem {a : A} (ha : a ∈ univ P q) :
    genClaim P H enc d f q a ∈ genCert P H enc d f q := List.mem_map_of_mem ha
omit [DecidableEq D] in theorem hasLit_pos {a : A} (ha : a ∈ univ P q) (hM : SM P (edbOf enc d f) a) {r : ℕ}
    (hr : rkPos P enc d f q a < r) : hasLit (genCert P H enc d f q) a true r = true := by
  obtain ⟨h1, h2, h3⟩ := genClaim_fields P H enc d f q a
  exact hasLit_iff.2 ⟨_, genClaim_mem ha, h1, by simp [h2, hM], by simp [h3, hM, hr]⟩
omit [DecidableEq D] in theorem hasLit_neg {a : A} (ha : a ∈ univ P q) (hM : ¬ SM P (edbOf enc d f) a) {r : ℕ}
    (hr : rkNeg P enc d f q a < r) : hasLit (genCert P H enc d f q) a false r = true := by
  obtain ⟨h1, h2, h3⟩ := genClaim_fields P H enc d f q a
  exact hasLit_iff.2 ⟨_, genClaim_mem ha, h1, by simp [h2, hM], by simp [h3, hM, hr]⟩
theorem discrete_ivt {g : ℕ → K} {e : K} : ∀ n, g 0 < e → e < g n → (∀ j ≤ n, g j ≠ e) →
    ∃ i, i < n ∧ g i < e ∧ e < g (i + 1)
  | 0, h0, hn, _ => absurd (lt_trans h0 hn) (lt_irrefl _)
  | n + 1, h0, hn, hne => by
    rcases lt_or_gt_of_ne (hne n (by omega)) with h | h
    · exact ⟨n, by omega, h, hn⟩
    · obtain ⟨i, hi, h1, h2⟩ := discrete_ivt n h0 h fun j hj => hne j (by omega)
      exact ⟨i, by omega, h1, h2⟩
theorem genClaim_check [OrderBot K] [OrderTop K] (hbot : (f 0).1 = ⊥)
    (htop : (f (2 ^ d - 1)).1 = ⊤) (henc : ∀ a, ⊥ < enc a ∧ enc a < ⊤) {a : A}
    (ha : a ∈ univ P q) : checkClaim P H enc d (mroot H d f) (genCert P H enc d f q)
      (genClaim P H enc d f q a) = true := by
  have hW := lvl_le_width (P := P) (enc := enc) (d := d) (f := f) ha
  by_cases hM : SM P (edbOf enc d f) a <;> by_cases hE : P.isEdb a = true
  · -- positive EDB: membership opening
    obtain ⟨j, hj, hk⟩ := (SM_edb P _ hE).1 hM
    have hs := membIdx_spec (⟨j, hj, hk⟩ : edbOf enc d f a)
    simp only [genClaim, hM, hE, ↓reduceIte, checkClaim, Bool.and_eq_true,
      decide_eq_true_eq, true_and]
    refine ⟨⟨hs.1, mkPath_length ..⟩, ?_⟩
    rw [← hs.2]; exact recompute_mkPath H d f _ hs.1
  · -- positive IDB: the rule instance at the least depth
    have hex : ∃ n, DerivN P enc d f n a := derivN_of_SM P enc d f hM
    have hlv : DerivN P enc d f (lvl P enc d f a) a := by
      unfold lvl; split_ifs; exact Nat.find_spec hex
    obtain ⟨n, hn⟩ : ∃ n, lvl P enc d f a = n + 1 :=
      Nat.exists_eq_add_one_of_ne_zero fun h => by rw [h] at hlv; exact hlv
    rw [hn] at hlv; have hr : ∃ gr ∈ P.rules, gr.head = a ∧ (∀ b ∈ gr.pos, DerivN P enc d f
        (lvl P enc d f a - 1) b) ∧ ∀ b ∈ gr.neg, ¬ SM P (edbOf enc d f) b := by
      rcases hlv with ⟨he, _⟩ | h
      · exact absurd he hE
      · rw [hn]; exact h
    obtain ⟨hg, hh, hp, hneg⟩ := ruleOf_spec hr
    simp only [genClaim, hM, hE, ↓reduceIte, Bool.false_eq_true, checkClaim, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', and_assoc]
    set gr := ruleOf P enc d f a
    refine ⟨trivial, hg, hh, fun b hb => ?_, fun b hb => ?_⟩
    · have hbd := hp b hb
      have hbu : b ∈ univ P q := mem_univ_body hg (.inl hb)
      have hlb : lvl P enc d f b ≤ n := by
        have hx : ∃ n, DerivN P enc d f n b := ⟨_, hbd⟩
        unfold lvl; split_ifs; exact Nat.find_min' hx (by rw [hn] at hbd; simpa using hbd)
      refine hasLit_pos hbu (SM_of_derivN P enc d f _ _ hbd) ?_
      have := P.wf_pos gr hg b hb; rw [hh] at this
      have := lvl_le_width (P := P) (enc := enc) (d := d) (f := f) hbu
      unfold rkPos; rw [hn]
      have := rank_lt (W := width P enc d f q) (x := 2 + lvl P enc d f b) (y := 2 + (n + 1))
        ‹P.st b ≤ P.st a› (fun _ => by omega) (by omega)
      omega
    · have hbu : b ∈ univ P q := mem_univ_body hg (.inr (.inl hb))
      refine hasLit_neg hbu (hneg b hb) ?_
      have hst := P.wf_neg gr hg b hb; rw [hh] at hst
      unfold rkNeg rkPos; split_ifs
      · omega
      · have := rank_lt (W := width P enc d f q) (x := 1) (y := 2 + lvl P enc d f a)
          hst.le (fun h => absurd h hst.ne) (by omega)
        omega
  · -- negative EDB: adjacent gap
    have hne : ∀ j ≤ 2 ^ d - 1, (f j).1 ≠ enc a := fun j hj hk =>
      hM ((SM_edb P _ hE).2 ⟨j, by have := Nat.one_le_two_pow (n := d); omega, hk⟩)
    obtain ⟨i, hi, h1, h2⟩ := discrete_ivt (g := fun j => (f j).1) (2 ^ d - 1)
      (by simp only [hbot]; exact (henc a).1) (by simp only [htop]; exact (henc a).2) hne
    have hex : ∃ i, i + 1 < 2 ^ d ∧ (f i).1 < enc a ∧ enc a < (f (i + 1)).1 :=
      ⟨i, by omega, h1, h2⟩
    have hs := gapIdx_spec hex
    simp only [genClaim, hM, hE, ↓reduceIte, checkClaim, Bool.and_eq_true,
      decide_eq_true_eq, and_assoc, true_and]
    exact ⟨hs.1, mkPath_length .., mkPath_length .., recompute_mkPath H d f _ (by omega),
      recompute_mkPath H d f _ hs.1, hs.2.1, hs.2.2⟩
  · -- negative IDB: the unfounded set of its stratum
    simp only [genClaim, hM, hE, ↓reduceIte, Bool.false_eq_true, checkClaim, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, and_assoc]
    have hEf : P.isEdb a = false := by simpa using hE
    refine ⟨trivial, ?_, fun u hu => ?_, fun gr hg => ?_⟩
    · simp [uSet, ha, hEf, hM]
    · simp only [uSet, List.mem_filter, decide_eq_true_eq] at hu; exact hu.2.1
    · by_cases hh : gr.head ∈ uSet P enc d f q (P.st a)
      · have hrk : rkNeg P enc d f q a = P.st a * width P enc d f q + 1 := by simp [rkNeg, hEf]
        rw [hrk]; simp only [uSet, List.mem_filter, decide_eq_true_eq] at hh
        obtain ⟨_, hhE, hhM, hhs⟩ := hh
        have hnd : ¬ ((∀ b ∈ gr.pos, SM P (edbOf enc d f) b) ∧
            ∀ b ∈ gr.neg, ¬ SM P (edbOf enc d f) b) := fun ⟨hp, hn⟩ =>
          hhM ((SM_fix P _ _).2 (.rule gr hg (fun b hb => (SM_fix P _ b).1 (hp b hb)) hn))
        simp only [not_and_or, not_forall, not_not] at hnd
        rcases hnd with ⟨b, hb, hbM⟩ | ⟨b, hb, hbM⟩
        · refine .inl (.inr ⟨b, hb, ?_⟩)
          have hbu : b ∈ univ P q := mem_univ_body hg (.inl hb)
          have hst := P.wf_pos gr hg b hb
          by_cases hbE : P.isEdb b = false ∧ P.st b = P.st a
          · exact .inl (by simp [uSet, hbu, hbE.1, hbM, hbE.2])
          · refine .inr (hasLit_neg hbu hbM ?_)
            unfold rkNeg; split_ifs with hb'
            · omega
            · have hlt : P.st b < P.st a := by
                rw [hhs] at hst; rcases Nat.lt_or_eq_of_le hst with h | h
                · exact h
                · exact absurd ⟨by simpa using hb', h⟩ hbE
              have := rank_lt (W := width P enc d f q) (x := 1) (y := 1) hlt.le
                (fun h => absurd h hlt.ne) (by omega)
              omega
        · refine .inr ⟨b, hb, hasLit_pos (mem_univ_body hg (.inr (.inl hb))) hbM ?_⟩
          have hst := P.wf_neg gr hg b hb; rw [hhs] at hst
          have := lvl_le_width (P := P) (enc := enc) (d := d) (f := f) (q := q)
            (mem_univ_body hg (.inr (.inl hb)))
          unfold rkPos
          have := rank_lt (W := width P enc d f q) (x := 2 + lvl P enc d f b) (y := 1) hst.le
            (fun h => absurd h hst.ne) (by omega)
          omega
      · exact .inl (.inl (by simpa using hh))
omit [DecidableEq D] in theorem genClaim_faithful (a : A) : Faithful enc f (genClaim P H enc d f q a) := by
  unfold genClaim
  split_ifs with hm he he <;> simp only [Faithful, and_self, eq_self]
  exact Prod.ext (membIdx_spec ((SM_edb P _ he).1 hm)).2.symm rfl

/-- Sentinel bounds suffice to construct a faithful certificate for either true signed literal. -/
theorem datalog_cert_complete [OrderBot K] [OrderTop K] (sg : Bool) (hbot : (f 0).1 = ⊥)
    (htop : (f (2 ^ d - 1)).1 = ⊤) (henc : ∀ a, ⊥ < enc a ∧ enc a < ⊤)
    (hq : SM P (edbOf enc d f) q ↔ sg = true) :
    ∃ cert, verifyDatalogCert P H enc d (mroot H d f) q sg cert = true ∧
      ∀ c ∈ cert, Faithful enc f c := by
  refine ⟨genCert P H enc d f q, ?_, fun c hc => ?_⟩
  case refine_2 =>
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hc
    exact genClaim_faithful ..
  simp only [verifyDatalogCert, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq]
  refine ⟨fun c hc => ?_, genClaim P H enc d f q q, genClaim_mem (by simp [univ]), ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    exact genClaim_check hbot htop henc ha
  · obtain ⟨h1, h2, _⟩ := genClaim_fields P H enc d f q q
    refine ⟨h1, ?_⟩
    rw [h2]; cases sg <;> simp_all
/-- On a sorted, sentinel-bounded tree, a faithful accepted certificate exists exactly for
a true signed literal. Works for any hash, including fixed-width digests. -/
theorem datalog_cert_sound_and_complete [OrderBot K] [OrderTop K] (sg : Bool)
    (hs : ¬ Unsorted d f) (hbot : (f 0).1 = ⊥)
    (htop : (f (2 ^ d - 1)).1 = ⊤) (henc : ∀ a, ⊥ < enc a ∧ enc a < ⊤) :
    (∃ cert, verifyDatalogCert P H enc d (mroot H d f) q sg cert = true ∧
      ∀ c ∈ cert, Faithful enc f c) ↔ (SM P (edbOf enc d f) q ↔ sg = true) := by
  refine ⟨?_, datalog_cert_complete sg hbot htop henc⟩
  rintro ⟨cert, hv, hf⟩
  rcases datalog_cert_sound P H enc d f _ q sg cert hv rfl with ok | ⟨c, hc, bad, _⟩ | hu
  exacts [ok, (bad (hf c hc)).elim, (hs hu).elim]
end Complete
end Certs
/-! ## Toy conformance vectors (shared with `prover/testdata/cert_datalog_conformance.json`) -/
section Toy
/-- Toy hash (conformance only; NOT collision resistant): `p = 2^31 - 1`. -/
def toyH : HIn (Fin 64) ℕ ℕ → ℕ
  | .leaf k s => (k.val * 1000003 + s * 7919 + 17) % 2147483647
  | .node l r => (l * 65599 + r * 31 + 3) % 2147483647
/-- Leaves: `⊥`, the EDB `{1,2,3,4,5,7,8,9}` under `enc a = a + 1`, then `⊤` padding. -/
def toyLeaves : ℕ → Fin 64 × ℕ
  | 0 => (0, 0) | 1 => (2, 1001) | 2 => (3, 1002) | 3 => (4, 1003) | 4 => (5, 1004)
  | 5 => (6, 1005) | 6 => (8, 1006) | 7 => (9, 1007) | 8 => (10, 1008) | _ => (63, 0)
def toyEnc (a : Fin 51) : Fin 64 := ⟨a.val + 1, by omega⟩
def toySt (a : Fin 51) : ℕ :=
  if a < 20 then 0 else if a < 30 then 1 else if a < 40 then 2 else if a < 50 then 3 else 1
/-- grant/member/groupGrant/revoked/request (EDB) → can (1) → allowed (2) → alert (3); `50:-50`. -/
def toyRules : List (GR (Fin 51)) :=
  [⟨20, [1], []⟩, ⟨21, [2, 3], []⟩, ⟨22, [5], []⟩, ⟨30, [20], [10]⟩, ⟨31, [21], [4]⟩,
    ⟨32, [22], [6]⟩, ⟨40, [7], [30]⟩, ⟨41, [8], [31]⟩, ⟨42, [9], [32]⟩, ⟨50, [50], []⟩]
def toyProg : Prog (Fin 51) where
  rules := toyRules
  isEdb a := decide (a < 20)
  st := toySt
  wf_head := by decide
  wf_pos := by decide
  wf_neg := by decide
/-- info: 839753907 -/
#guard_msgs in #eval mroot toyH 4 toyLeaves

/--
info: [17, 9926942, 10934864, 11942786, 12950708, 13958630, 15966555, 16974477, 17982399, 63000206, 63000206, 63000206,
  63000206, 63000206, 63000206, 63000206]
-/
#guard_msgs in #eval (List.range 16).map fun i => toyH (.leaf (toyLeaves i).1 (toyLeaves i).2)
theorem toy_sorted : ¬ Unsorted 4 toyLeaves := by
  rintro ⟨i, j, hij, hj, hlt⟩
  have sorted : ∀ a b : Fin 16, a ≤ b → (toyLeaves a).1 ≤ (toyLeaves b).1 := by decide
  exact (not_lt_of_ge (sorted ⟨i, by omega⟩ ⟨j, hj⟩ hij)) hlt

theorem toy_signed_iff (q : Fin 51) (sg : Bool) :
    (∃ cs, verifyDatalogCert toyProg toyH toyEnc 4 (mroot toyH 4 toyLeaves) q sg cs = true ∧
      ∀ c ∈ cs, Faithful toyEnc toyLeaves c) ↔ (SM toyProg (edbOf toyEnc 4 toyLeaves) q ↔ sg = true) :=
  datalog_cert_sound_and_complete sg toy_sorted rfl rfl (by decide)

def toyRoot : ℕ := 839753907
theorem toy_root : mroot toyH 4 toyLeaves = toyRoot := by decide

def mb (a : Fin 51) (j : ℕ) (r : ℕ) : Claim (Fin 51) (Fin 64) ℕ ℕ :=
  ⟨a, true, r, .memb j (toyLeaves j).2 (mkPath toyH 4 toyLeaves j)⟩

def certAlertBob : List (Claim (Fin 51) (Fin 64) ℕ ℕ) :=
  [mb 8 7 2, mb 4 4 2, mb 2 2 2, mb 3 3 2, ⟨21, true, 5, .rule ⟨21, [2, 3], []⟩⟩,
    ⟨31, false, 10, .unf [31]⟩, ⟨41, true, 20, .rule ⟨41, [8], [31]⟩⟩]

def certAlertAliceFalse : List (Claim (Fin 51) (Fin 64) ℕ ℕ) :=
  [mb 1 1 2, ⟨20, true, 5, .rule ⟨20, [1], []⟩⟩,
    ⟨10, false, 0, .gap 8 (toyLeaves 8) (mkPath toyH 4 toyLeaves 8) (toyLeaves 9)
      (mkPath toyH 4 toyLeaves 9)⟩,
    ⟨30, true, 15, .rule ⟨30, [20], [10]⟩⟩, ⟨40, false, 30, .unf [40]⟩]

def certPFalse : List (Claim (Fin 51) (Fin 64) ℕ ℕ) := [⟨50, false, 1, .unf [50]⟩]

def certCyclic : List (Claim (Fin 51) (Fin 64) ℕ ℕ) := [⟨50, true, 1, .rule ⟨50, [50], []⟩⟩]
/-- Claimed index 1 but the right opening is of leaf 3 (non-adjacent). -/
def certNonAdjacent : List (Claim (Fin 51) (Fin 64) ℕ ℕ) :=
  [⟨2, false, 0, .gap 1 (toyLeaves 1) (mkPath toyH 4 toyLeaves 1) (toyLeaves 3)
    (mkPath toyH 4 toyLeaves 3)⟩]
theorem toy_accepts :
    verifyDatalogCert toyProg toyH toyEnc 4 toyRoot 41 true certAlertBob = true ∧
      verifyDatalogCert toyProg toyH toyEnc 4 toyRoot 40 false certAlertAliceFalse = true ∧
      verifyDatalogCert toyProg toyH toyEnc 4 toyRoot 50 false certPFalse = true := by
  decide
/-- **Falsifier.** `p :- p` self-justification: the only failing check is the strict rank, and
the atom is false in the stratified model. -/
theorem toy_cyclic_rejected :
    verifyDatalogCert toyProg toyH toyEnc 4 toyRoot 50 true certCyclic = false ∧
      hasLit certCyclic 50 true 2 = true ∧ ¬ SM toyProg (edbOf toyEnc 4 toyLeaves) 50 := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  rw [SM_fix] at h
  suffices ∀ x, Deriv toyRules (fun a => decide (a < 20)) (edbOf toyEnc 4 toyLeaves)
      (SM toyProg (edbOf toyEnc 4 toyLeaves)) x → x = 50 → False from this _ h rfl
  intro x hx; induction hx with
  | base he _ => intro h; subst h; exact absurd he (by decide)
  | rule gr hmem _ _ ih =>
    intro h; simp only [toyRules, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd h (by decide) | exact ih 50 (by simp) rfl
/-- A loose gap check that accepts any `i < j`. -/
def looseGap (a : Fin 51) (i : ℕ) (lL : Fin 64 × ℕ) (pL : List ℕ) (j : ℕ) (lR : Fin 64 × ℕ)
    (pR : List ℕ) : Bool :=
  decide (i < j ∧ j < 2 ^ 4) && decide (recompute toyH 4 i lL pL = toyRoot) &&
    decide (recompute toyH 4 j lR pR = toyRoot) && decide (lL.1 < toyEnc a ∧ toyEnc a < lR.1)
/-- **Falsifier.** Openings `(1, 3)` bracket `enc 2` although `2 ∈ EDB`; the adjacent verifier
rejects the same openings. -/
theorem toy_nonadjacent_gap_falsifier :
    looseGap 2 1 (toyLeaves 1) (mkPath toyH 4 toyLeaves 1) 3 (toyLeaves 3)
        (mkPath toyH 4 toyLeaves 3) = true ∧
      edbOf toyEnc 4 toyLeaves 2 ∧
      verifyDatalogCert toyProg toyH toyEnc 4 toyRoot 2 false certNonAdjacent = false :=
  ⟨by decide, ⟨2, by decide, rfl⟩, by decide⟩
end Toy
/-! ## Axiom pins -/

/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.cert_conj_shared_commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cert_conj_shared_commit

/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.cert_sampled_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cert_sampled_audit
/-- info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.stratModel_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stratModel_unique
/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.datalog_cert_sound_and_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms datalog_cert_sound_and_complete
/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.toy_nonadjacent_gap_falsifier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms toy_nonadjacent_gap_falsifier

/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.cert_bpe_byte_weld' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cert_bpe_byte_weld
/--
info: 'Minidregg.Assurance.CertificateAndDatalogCalculus.cert_opened_byte_turn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms cert_opened_byte_turn
end Minidregg.Assurance.CertificateAndDatalogCalculus
