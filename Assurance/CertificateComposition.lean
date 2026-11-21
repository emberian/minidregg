/-
# `Assurance/CertificateComposition.lean` — Composition Laws (`L0`–`L5`, `P5`–`P8`) for Content-Bound Certificates

Mechanizes the cross-prover composition algebra from `CERTIFICATES.md` (§§1, 2, 5) over
`Selvage/ContentCertificate.lean` (`ContentScheme`, `parityScheme`, `idealContentScheme`),
`Selvage/BindingGame.lean` (`prob`), `Selvage/BabyBearExt4.lean` (`BabyBear`, `Digest8`), and
`Pred/Core.lean` (`Pred.evalWith` third-party oracle discharge).

## Laws & Adversarial Teeth

1. **Straightline Query-Indexed Soundness (`QueryEnv`, `CertSound`, `BindSound`)**:
   Matches `CERTIFICATES.md` §1 & `Selvage/FiatShamir.lean`'s straightline query-log extractor
   shape: an extractor `E : Digest → Proof → Log → List Sym` recovers a grounded witness `w` from
   the query log with failure probability `≤ ε q`. Inhabited at all three binding regimes:
   `bindAdv = 0` (`idealContentScheme`), `0 < bindAdv = 1/2 < 1` (`parityHalfScheme` over a
   sampled query-log environment), and `bindAdv = 1` (`parityScheme`).

2. **`L1` / `P5` (`cert_and` & Sharp `bindAdv` Necessity Tooth)**:
   Conjunction over one commitment `c` achieves error `ε₁ q + ε₂ q + S.bindAdv q`. On
   `parityScheme`, `cert_and_dropping_bindAdv_false` exhibits `φ₁, φ₂` and deterministic verifiers
   with `ε₁ = 0, ε₂ = 0` where `(V₁ && V₂)` accepts `c = 0` (`w₁ = [0, 0] ∈ φ₁ \ φ₂`,
   `w₂ = [1, 1] ∈ φ₂ \ φ₁`, `commit w₁ = commit w₂ = 0`) while **no** word in `φ₁ ∧ φ₂` exists —
   refuting `CertSound` at `0 + 0 = 0` against **every** hypothetical extractor.

3. **`L0` / `P6` (`BoundDfaStmt` vs Word-Free `UnboundDfaStmt` Splice Tooth)**:
   Defines `DfaTrace`, `DfaAccepts`, `UnboundDfaStmt` (`dfa_verify_sound`), and `BoundDfaStmt`
   (`dfa_bound_sound`). `unbound_dfa_splice_falsifier` proves the zero-work splice separation:
   a word-ignoring verifier (`verify stmt _ := stmt.accept stmt.q₀`) satisfies word-free
   `dfa_verify_sound` (via the empty trace `[]`) and accepts a committed forbidden word `[true]`,
   whereas `dfa_bound_sound` rejects it.

4. **`L2` / `P7` (`cert_allRecords` Corpus Union Bound & 1-Felt vs 8-Felt Collision Tooth)**:
   Proves corpus aggregation over an MMR achieves error `(N : ℝ) * ε q + mmrBindAdv q + S.bindAdv q`
   (charging `S.bindAdv q` **once**, not `N` times, by selecting the first mismatching corpus index).
   Proves `digest8_lane0_splice_falsifier` and `oneFelt_wraparound_breaks_allRecords` over
   `BabyBear` (`2013265921 ≡ 0` collides in 1 felt while `Digest8 := Fin 8 → BabyBear` separates).

5. **`L4` / `P8` (`cert_produced_weld` + `TK` Collision Tooth) & `L5` (`cert_mapScheme`)**:
   Composes `Produced(m, c_in, c_out; ε_inf)` + `Cert(c'_out, φ; ε_c)` + `Bridge` at error
   `ε_inf q + ε_c q + ε_bridge q`, proves `tk_weld_collision_tooth` + `tk_noninjective_weld_falsifier`
   (`w' ≠ window` requires `TK w' = TK window`), proves `cert_mapScheme` + target attribution
   (`ε q + ε_mor q + S.bindAdv q + S'.bindAdv q`) with both-sided binding necessity teeth, and
   connects `CertSound` to `Pred.evalWith`'s `.witnessed vk` third-party policy discharge.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Selvage.ContentCertificate
import Selvage.BindingGame
import Selvage.BabyBearExt4
import Pred.Core

namespace Minidregg.Assurance.CertificateComposition

open Minidregg.Selvage
open Minidregg.Selvage.BabyBearExt4

set_option autoImplicit false

/-! ## §1. Straightline Query-Indexed Certificate Soundness (`QueryEnv`, `CertSound`, `BindSound`) -/

/-- Query-log probability environment for straightline knowledge soundness (`CERTIFICATES.md` §1):
at each query budget `q : ℕ`, `Coins q` is a finite nonempty probability space, `Log` is the
query-log state, `ValidLog q` selects admissible `q`-query logs, and `Grounded l w` records that
candidate word `w` is extractable from query log `l` without extra oracle queries. -/
structure QueryEnv (Sym : Type) where
  Coins : ℕ → Type
  Log : Type
  coinsFintype : ∀ q, Fintype (Coins q)
  coinsNonempty : ∀ q, Nonempty (Coins q)
  ValidLog : ∀ q, (Coins q → Log) → Prop
  Grounded : Log → List Sym → Prop

attribute [instance] QueryEnv.coinsFintype QueryEnv.coinsNonempty

/-- Unrestricted deterministic/coin query environment (`Grounded _ _ := True`): every function is
admissible, used both for ideal `bindAdv = 0` schemes and to make negative/falsifier theorems
refute **all** mathematical extractors without restriction. -/
def unrestrictedEnv (Sym : Type) : QueryEnv Sym where
  Coins := fun _ => Unit
  Log := Unit
  coinsFintype := fun _ => inferInstance
  coinsNonempty := fun _ => ⟨()⟩
  ValidLog := fun _ _ => True
  Grounded := fun _ _ => True

/-- **Straightline Certificate Knowledge Soundness (`CertSound`, `CERTIFICATES.md` §1)**:
there exists a straightline extractor `ext : Digest → Proof → E.Log → List Sym` (no rewinding)
such that for every query budget `q` and admissible transcript `(c, π, log)`, the probability that
`V` accepts while `ext` fails `Grounded (log ω) w ∧ commit w = c ∧ φ w` is `≤ ε q`.
Keeping `Grounded (log ω)` inside the event ensures `CertSound` remains satisfiable even on
`0`-query empty logs (`l = []`, where `Grounded [] w` is `False`). -/
def CertSound {Sym Digest Op Proof : Type}
    (E : QueryEnv Sym) (S : ContentScheme Sym Digest Op)
    (V : Digest → Proof → Bool) (φ : List Sym → Prop) (ε : ℕ → ℝ) : Prop :=
  ∃ ext : Digest → Proof → E.Log → List Sym,
    ∀ (q : ℕ) (c : E.Coins q → Digest) (π : E.Coins q → Proof) (log : E.Coins q → E.Log),
      E.ValidLog q log →
      BindingGame.prob (fun ω =>
        V (c ω) (π ω) = true ∧
          ¬ (E.Grounded (log ω) (ext (c ω) (π ω) (log ω)) ∧
              S.commit (ext (c ω) (π ω) (log ω)) = c ω ∧
              φ (ext (c ω) (π ω) (log ω))))
        ≤ ε q

/-- **Computational Binding Soundness (`BindSound`)**: any two candidate words `w₁, w₂` collide
while both grounded in an admissible `q`-query log (`w₁ ≠ w₂`) with probability `≤ S.bindAdv q`. -/
def BindSound {Sym Digest Op : Type}
    (E : QueryEnv Sym) (S : ContentScheme Sym Digest Op) : Prop :=
  ∀ (q : ℕ) (log : E.Coins q → E.Log), E.ValidLog q log →
    ∀ (w₁ w₂ : E.Coins q → List Sym),
      BindingGame.prob (fun ω =>
        E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (w₂ ω) ∧
          S.commit (w₁ ω) = S.commit (w₂ ω) ∧ w₁ ω ≠ w₂ ω) ≤ S.bindAdv q

/-- Helper: a predicate that fails everywhere has `BindingGame.prob = 0`. -/
theorem prob_eq_zero_of_false {Ω : Type} [Fintype Ω] {p : Ω → Prop}
    (hf : ∀ ω : Ω, ¬ p ω) : BindingGame.prob p = 0 := by
  classical
  unfold BindingGame.prob
  have hsum : (∑ ω : Ω, if p ω then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun ω _ => ite_eq_right_iff.mpr fun h => False.elim (hf ω h)
  rw [hsum, zero_div]

/-- Helper: a predicate that holds everywhere on a nonempty space has `BindingGame.prob = 1`. -/
theorem prob_eq_one_of_true {Ω : Type} [Fintype Ω] [Nonempty Ω] {p : Ω → Prop}
    (ht : ∀ ω : Ω, p ω) : BindingGame.prob p = 1 := by
  have heq : p = (fun _ : Ω => True) :=
    funext fun ω => propext ⟨fun _ => trivial, fun _ => ht ω⟩
  rw [heq, BindingGame.prob_true]

/-- `idealContentScheme` satisfies `BindSound` with `bindAdv = 0` in **every** `QueryEnv`. -/
theorem idealContentScheme_bindSound {Sym : Type} [DecidableEq Sym] (E : QueryEnv Sym) :
    BindSound E (idealContentScheme Sym) := by
  intro q log _ w₁ w₂
  have hfalse : ∀ ω : E.Coins q,
      ¬ (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (w₂ ω) ∧
          (idealContentScheme Sym).commit (w₁ ω) = (idealContentScheme Sym).commit (w₂ ω) ∧
          w₁ ω ≠ w₂ ω) := fun _ h => h.2.2.2 h.2.2.1
  rw [prob_eq_zero_of_false hfalse]
  exact (idealContentScheme Sym).bindAdv_nonneg q

/-- `parityScheme` satisfies `BindSound` at `bindAdv = 1` in **every** `QueryEnv`. -/
theorem parityScheme_bindSound (E : QueryEnv (ZMod 2)) :
    BindSound E parityScheme := by
  intro q _ _ w₁ w₂
  exact BindingGame.prob_le_one _

/-- **Fractional-advantage compressing environment (`0 < bindAdv = 1/2 < 1`)**:
`Coins _ := Bool`; on `true` the `2`-query log contains `[[0, 0], [0, 1]]` (distinct parities),
while on `false` it contains `[[0, 0], [1, 1]]` (colliding parities). -/
@[reducible] def sampledParityEnv : QueryEnv (ZMod 2) where
  Coins := fun _ => Bool
  Log := List (List (ZMod 2))
  coinsFintype := fun _ => inferInstance
  coinsNonempty := fun _ => ⟨true⟩
  ValidLog := fun _ log => ∀ b : Bool, log b = if b then [[0, 0], [0, 1]] else [[0, 0], [1, 1]]
  Grounded := fun l w => w ∈ l

/-- Compressing parity scheme calibrated to `bindAdv = 1 / 2` over `sampledParityEnv`. -/
@[reducible] noncomputable def parityHalfScheme : ContentScheme (ZMod 2) (ZMod 2) (List (ZMod 2)) :=
  { parityScheme with
    bindAdv := fun _ => 1 / 2
    bindAdv_nonneg := fun _ => by norm_num }

/-- Non-vacuity at `0 < bindAdv < 1`: `parityHalfScheme` satisfies `BindSound` on `sampledParityEnv`
with nontrivial fractional advantage `1 / 2`. -/
theorem parityHalfScheme_bindSound : BindSound sampledParityEnv parityHalfScheme := by
  intro q log hlog w₁ w₂
  have hno_true : ¬ (sampledParityEnv.Grounded (log true) (w₁ true) ∧
      sampledParityEnv.Grounded (log true) (w₂ true) ∧
      parityHalfScheme.commit (w₁ true) = parityHalfScheme.commit (w₂ true) ∧
      w₁ true ≠ w₂ true) := by
    rintro ⟨h₁, h₂, hcomm, hne⟩
    change w₁ true ∈ log true at h₁
    change w₂ true ∈ log true at h₂
    rw [hlog true] at h₁ h₂
    simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hne (h₁.trans h₂.symm)
    · rw [h₁, h₂] at hcomm; exact absurd hcomm (by decide)
    · rw [h₁, h₂] at hcomm; exact absurd hcomm (by decide)
    · exact hne (h₁.trans h₂.symm)
  classical
  unfold BindingGame.prob
  rw [Fintype.sum_bool, Fintype.card_bool]
  split_ifs with ht _
  · exact False.elim (hno_true ht)
  · exact False.elim (hno_true ht)
  · norm_num
  · norm_num

/-- Error-monotonicity helper for `CertSound`. -/
theorem certSound_mono {Sym Digest Op Proof : Type}
    {E : QueryEnv Sym} {S : ContentScheme Sym Digest Op}
    {V : Digest → Proof → Bool} {φ : List Sym → Prop} {ε ε' : ℕ → ℝ}
    (hs : CertSound E S V φ ε) (hle : ∀ q, ε q ≤ ε' q) :
    CertSound E S V φ ε' := by
  rcases hs with ⟨ext, hprob⟩
  exact ⟨ext, fun q c π log hlog => le_trans (hprob q c π log hlog) (hle q)⟩

/-! ## §2. `L1` / `P5`: Conjunction Over One Commitment (`cert_and`) & Sharp `bindAdv` Tooth -/

/-- **`L1` / `P5` Conjunction Over One Commitment (`CERTIFICATES.md` §2 L1 & §5 `P5`)**:
conjoining two certificates over one commitment `c` yields a certificate for `φ₁ ∧ φ₂` with
soundness error `ε₁ q + ε₂ q + S.bindAdv q`. -/
theorem cert_and {Sym Digest Op Proof₁ Proof₂ : Type}
    {E : QueryEnv Sym} (S : ContentScheme Sym Digest Op)
    {V₁ : Digest → Proof₁ → Bool} {V₂ : Digest → Proof₂ → Bool}
    {φ₁ φ₂ : List Sym → Prop} {ε₁ ε₂ : ℕ → ℝ}
    (h₁ : CertSound E S V₁ φ₁ ε₁)
    (h₂ : CertSound E S V₂ φ₂ ε₂)
    (hbind : BindSound E S) :
    CertSound E S (fun c (π : Proof₁ × Proof₂) => V₁ c π.1 && V₂ c π.2)
      (fun w => φ₁ w ∧ φ₂ w)
      (fun q => ε₁ q + ε₂ q + S.bindAdv q) := by
  rcases h₁ with ⟨ext₁, hs₁⟩
  rcases h₂ with ⟨ext₂, hs₂⟩
  refine ⟨fun c π l => ext₁ c π.1 l, ?_⟩
  intro q c π log hlog
  let w₁ : E.Coins q → List Sym := fun ω => ext₁ (c ω) (π ω).1 (log ω)
  let w₂ : E.Coins q → List Sym := fun ω => ext₂ (c ω) (π ω).2 (log ω)
  have hb₁ := hs₁ q c (fun ω => (π ω).1) log hlog
  have hb₂ := hs₂ q c (fun ω => (π ω).2) log hlog
  have hbb := hbind q log hlog w₁ w₂
  have hcov : BindingGame.prob (fun ω =>
      (V₁ (c ω) (π ω).1 && V₂ (c ω) (π ω).2) = true ∧
        ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = c ω ∧ φ₁ (w₁ ω) ∧ φ₂ (w₁ ω))) ≤
      BindingGame.prob (fun ω =>
        (V₁ (c ω) (π ω).1 = true ∧
          ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = c ω ∧ φ₁ (w₁ ω))) ∨
        ((V₂ (c ω) (π ω).2 = true ∧
            ¬ (E.Grounded (log ω) (w₂ ω) ∧ S.commit (w₂ ω) = c ω ∧ φ₂ (w₂ ω))) ∨
          (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (w₂ ω) ∧
            S.commit (w₁ ω) = S.commit (w₂ ω) ∧ w₁ ω ≠ w₂ ω))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hacc, hfail⟩
    rw [Bool.and_eq_true] at hacc
    by_cases hg₁ : E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = c ω ∧ φ₁ (w₁ ω)
    · by_cases hg₂ : E.Grounded (log ω) (w₂ ω) ∧ S.commit (w₂ ω) = c ω ∧ φ₂ (w₂ ω)
      · right; right
        refine ⟨hg₁.1, hg₂.1, hg₁.2.1.trans hg₂.2.1.symm,
          fun heq => hfail ⟨hg₁.1, hg₁.2.1, hg₁.2.2, heq ▸ hg₂.2.2⟩⟩
      · exact Or.inr (Or.inl ⟨hacc.2, hg₂⟩)
    · exact Or.inl ⟨hacc.1, hg₁⟩
  have hu₁ := BindingGame.prob_or
    (fun ω => V₁ (c ω) (π ω).1 = true ∧
      ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = c ω ∧ φ₁ (w₁ ω)))
    (fun ω => (V₂ (c ω) (π ω).2 = true ∧
        ¬ (E.Grounded (log ω) (w₂ ω) ∧ S.commit (w₂ ω) = c ω ∧ φ₂ (w₂ ω))) ∨
      (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (w₂ ω) ∧
        S.commit (w₁ ω) = S.commit (w₂ ω) ∧ w₁ ω ≠ w₂ ω))
  have hu₂ := BindingGame.prob_or
    (fun ω => V₂ (c ω) (π ω).2 = true ∧
      ¬ (E.Grounded (log ω) (w₂ ω) ∧ S.commit (w₂ ω) = c ω ∧ φ₂ (w₂ ω)))
    (fun ω => E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (w₂ ω) ∧
      S.commit (w₁ ω) = S.commit (w₂ ω) ∧ w₁ ω ≠ w₂ ω)
  linarith

/-- Satisfying witness for `cert_and` over `idealContentScheme UInt8` (`0 + 0 + 0 = 0`):
Tier-1 `SubstringAt` openings at two positions compose with zero soundness loss. -/
theorem tier1_substringAt_certSound (i : ℕ) (P : List UInt8) :
    CertSound (unrestrictedEnv UInt8) (idealContentScheme UInt8)
      (fun c (π : ℕ × (Fin P.length → Unit) × Unit) =>
        verifySubstringOpenings (idealContentScheme UInt8) c i P π.1 π.2.1 π.2.2)
      (fun w => SubstringAtPlain w i P)
      (fun _ => 0) := by
  refine ⟨fun c _ _ => c, fun q c π log _ => ?_⟩
  have hfalse : ∀ ω : (unrestrictedEnv UInt8).Coins q,
      ¬ (verifySubstringOpenings (idealContentScheme UInt8) (c ω) i P (π ω).1 (π ω).2.1 (π ω).2.2 = true ∧
          ¬ ((unrestrictedEnv UInt8).Grounded (log ω) (c ω) ∧
              (idealContentScheme UInt8).commit (c ω) = c ω ∧ SubstringAtPlain (c ω) i P)) := by
    intro ω ⟨hver, hbad⟩
    rcases substringAt_of_openings (idealContentScheme UInt8) (c ω) i P (π ω).1 (π ω).2.1 (π ω).2.2
        hver (c ω) rfl with hsub | hbr
    · exact hbad ⟨trivial, hsub.1, hsub.2⟩
    · exact idealContentScheme_no_bindBreak UInt8 (c ω) hbr
  rw [prob_eq_zero_of_false hfalse]

abbrev Tier1Proof (P : List UInt8) : Type := ℕ × (Fin P.length → Unit) × Unit

theorem cert_and_ideal_witness :
    CertSound (unrestrictedEnv UInt8) (idealContentScheme UInt8)
      (fun c (π : Tier1Proof [10] × Tier1Proof [30, 40]) =>
        verifySubstringOpenings (idealContentScheme UInt8) c 0 [10] π.1.1 π.1.2.1 π.1.2.2 &&
        verifySubstringOpenings (idealContentScheme UInt8) c 2 [30, 40] π.2.1 π.2.2.1 π.2.2.2)
      (fun w => SubstringAtPlain w 0 [10] ∧ SubstringAtPlain w 2 [30, 40])
      (fun _ => 0) := by
  have h := cert_and (idealContentScheme UInt8)
    (tier1_substringAt_certSound 0 [10])
    (tier1_substringAt_certSound 2 [30, 40])
    (idealContentScheme_bindSound (unrestrictedEnv UInt8))
  exact certSound_mono h (fun _ => by norm_num [idealContentScheme])

/-- **Compressing `0 < bindAdv = 1/2 < 1` `CertSound` + `cert_and` Witness**:
On `sampledParityEnv` and `parityHalfScheme`, `[0, 0]` is grounded on **every** valid coin (`true`
and `false`), so `parityV0` (`c == 0`) is genuinely `CertSound` at `ε = 0` for both `w = [0, 0]`
and `w.length = 2`, and `cert_and` composes them at nontrivial error `0 + 0 + 1/2 = 1/2`. -/
def parityV0 (c : ZMod 2) (_ : Unit) : Bool := decide (c = 0)
abbrev parityPhi0 (w : List (ZMod 2)) : Prop := w = [0, 0]
abbrev parityPhi1 (w : List (ZMod 2)) : Prop := w = [1, 1]

theorem parityHalf_certSound_phi0 :
    CertSound sampledParityEnv parityHalfScheme parityV0 parityPhi0 (fun _ => 0) := by
  refine ⟨fun _ _ _ => [0, 0], fun q c π log hlog => ?_⟩
  have hfalse : ∀ ω : sampledParityEnv.Coins q,
      ¬ (parityV0 (c ω) (π ω) = true ∧
          ¬ (sampledParityEnv.Grounded (log ω) [0, 0] ∧
              parityHalfScheme.commit [0, 0] = c ω ∧ parityPhi0 [0, 0])) := by
    intro ω ⟨hv, hbad⟩
    simp only [parityV0, decide_eq_true_eq] at hv
    have hmem : ([0, 0] : List (ZMod 2)) ∈ log ω := by
      rw [hlog ω]; cases ω <;> simp
    exact hbad ⟨hmem, by simp [parityScheme, hv], rfl⟩
  rw [prob_eq_zero_of_false hfalse]

theorem cert_and_fractional_compressing_witness :
    CertSound sampledParityEnv parityHalfScheme
      (fun c (π : Unit × Unit) => parityV0 c π.1 && parityV0 c π.2)
      (fun w => parityPhi0 w ∧ parityPhi0 w)
      (fun _ => 1 / 2) := by
  have h := cert_and parityHalfScheme
    parityHalf_certSound_phi0 parityHalf_certSound_phi0 parityHalfScheme_bindSound
  exact certSound_mono h (fun _ => by norm_num)

theorem parityV0_certSound_phi0 :
    CertSound (unrestrictedEnv (ZMod 2)) parityScheme parityV0 parityPhi0 (fun _ => 0) := by
  refine ⟨fun _ _ _ => [0, 0], fun q c π log _ => ?_⟩
  have hfalse : ∀ ω : (unrestrictedEnv (ZMod 2)).Coins q,
      ¬ (parityV0 (c ω) (π ω) = true ∧
          ¬ ((unrestrictedEnv (ZMod 2)).Grounded (log ω) [0, 0] ∧
              parityScheme.commit [0, 0] = c ω ∧ parityPhi0 [0, 0])) := by
    intro ω ⟨hv, hbad⟩
    simp only [parityV0, decide_eq_true_eq] at hv
    exact hbad ⟨trivial, by simp [parityScheme, hv], rfl⟩
  rw [prob_eq_zero_of_false hfalse]

theorem parityV0_certSound_phi1 :
    CertSound (unrestrictedEnv (ZMod 2)) parityScheme parityV0 parityPhi1 (fun _ => 0) := by
  refine ⟨fun _ _ _ => [1, 1], fun q c π log _ => ?_⟩
  have hfalse : ∀ ω : (unrestrictedEnv (ZMod 2)).Coins q,
      ¬ (parityV0 (c ω) (π ω) = true ∧
          ¬ ((unrestrictedEnv (ZMod 2)).Grounded (log ω) [1, 1] ∧
              parityScheme.commit [1, 1] = c ω ∧ parityPhi1 [1, 1])) := by
    intro ω ⟨hv, hbad⟩
    simp only [parityV0, decide_eq_true_eq] at hv
    have hsum : parityScheme.commit [1, 1] = 0 := by decide
    exact hbad ⟨trivial, hsum.trans hv.symm, rfl⟩
  rw [prob_eq_zero_of_false hfalse]

/-- **`P5` Sharp `bindAdv` Necessity Tooth (`cert_and_dropping_bindAdv_false`)**:
On `parityScheme`, `w₁ = [0, 0] ∈ φ₀ \ φ₁`, `w₂ = [1, 1] ∈ φ₁ \ φ₀`, `commit w₁ = commit w₂ = 0`,
both legs have `ε = 0`, yet dropping `+ S.bindAdv q` (`0 + 0 = 0`) is **FALSE** against **every**
extractor! -/
theorem cert_and_dropping_bindAdv_false :
    ((parityPhi0 [0, 0] ∧ ¬ parityPhi1 [0, 0]) ∧
     (parityPhi1 [1, 1] ∧ ¬ parityPhi0 [1, 1]) ∧
     parityScheme.commit [0, 0] = parityScheme.commit [1, 1]) ∧
    CertSound (unrestrictedEnv (ZMod 2)) parityScheme parityV0 parityPhi0 (fun _ => 0) ∧
    CertSound (unrestrictedEnv (ZMod 2)) parityScheme parityV0 parityPhi1 (fun _ => 0) ∧
    ¬ CertSound (unrestrictedEnv (ZMod 2)) parityScheme
        (fun c (π : Unit × Unit) => parityV0 c π.1 && parityV0 c π.2)
        (fun w => parityPhi0 w ∧ parityPhi1 w)
        (fun _ => 0) := by
  refine ⟨⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩, by decide⟩,
    parityV0_certSound_phi0, parityV0_certSound_phi1, ?_⟩
  rintro ⟨ext, hsound⟩
  have h0 := hsound 0 (fun _ => 0) (fun _ => ((), ())) (fun _ => ()) trivial
  have hacc : (parityV0 0 () && parityV0 0 ()) = true := by decide
  have himp : ¬ ((unrestrictedEnv (ZMod 2)).Grounded () (ext 0 ((), ()) ()) ∧
      parityScheme.commit (ext 0 ((), ()) ()) = 0 ∧
      parityPhi0 (ext 0 ((), ()) ()) ∧ parityPhi1 (ext 0 ((), ()) ())) := by
    rintro ⟨_, _, h00, h11⟩
    have hcontra : ([0, 0] : List (ZMod 2)) = [1, 1] := h00.symm.trans h11
    exact absurd hcontra (by decide)
  have hone : BindingGame.prob (fun _ : (unrestrictedEnv (ZMod 2)).Coins 0 =>
      (parityV0 0 () && parityV0 0 ()) = true ∧
        ¬ ((unrestrictedEnv (ZMod 2)).Grounded () (ext 0 ((), ()) ()) ∧
            parityScheme.commit (ext 0 ((), ()) ()) = 0 ∧
            parityPhi0 (ext 0 ((), ()) ()) ∧ parityPhi1 (ext 0 ((), ()) ()))) = 1 :=
    prob_eq_one_of_true (fun _ => ⟨hacc, himp⟩)
  dsimp at h0
  linarith

/-! ## §3. `L0` / `P6`: `BoundDfaStmt` vs Word-Free `UnboundDfaStmt` & Zero-Work Splice Tooth -/

/-- One transition step `(pre, sym, post)` of a deterministic automaton run. -/
structure DfaStep (State Sym : Type) where
  pre  : State
  sym  : Sym
  post : State
  deriving DecidableEq, Repr

/-- An automaton execution trace; its consumed input word is `trace.word`. -/
structure DfaTrace (State Sym : Type) where
  steps : List (DfaStep State Sym)
  deriving DecidableEq, Repr

def DfaTrace.word {State Sym : Type} (t : DfaTrace State Sym) : List Sym :=
  t.steps.map DfaStep.sym

/-- Step-by-step trace acceptance from state `q` under `δ : State → Sym → State` and `accept`. -/
def DfaRunAccepts {State Sym : Type}
    (δ : State → Sym → State) (accept : State → Bool) :
    State → List (DfaStep State Sym) → Prop
  | q, [] => accept q = true
  | q, s :: rest => s.pre = q ∧ s.post = δ s.pre s.sym ∧ DfaRunAccepts δ accept s.post rest

/-- `DfaAccepts δ q₀ accept trace` holds iff `trace` is a valid accepting run from `q₀`. -/
def DfaAccepts {State Sym : Type}
    (δ : State → Sym → State) (q₀ : State) (accept : State → Bool)
    (trace : DfaTrace State Sym) : Prop :=
  DfaRunAccepts δ accept q₀ trace.steps

/-- Executable Boolean trace checker equivalent to `DfaRunAccepts`. -/
def dfaRunAcceptsB {State Sym : Type} [DecidableEq State]
    (δ : State → Sym → State) (accept : State → Bool) :
    State → List (DfaStep State Sym) → Bool
  | q, [] => accept q
  | q, s :: rest =>
      decide (s.pre = q) && decide (s.post = δ s.pre s.sym) &&
        dfaRunAcceptsB δ accept s.post rest

theorem dfaRunAcceptsB_eq_true_iff {State Sym : Type} [DecidableEq State]
    (δ : State → Sym → State) (accept : State → Bool)
    (q : State) (steps : List (DfaStep State Sym)) :
    dfaRunAcceptsB δ accept q steps = true ↔ DfaRunAccepts δ accept q steps := by
  induction steps generalizing q with
  | nil => simp [dfaRunAcceptsB, DfaRunAccepts]
  | cons s rest ih =>
      simp only [dfaRunAcceptsB, DfaRunAccepts, Bool.and_eq_true, decide_eq_true_eq,
        ih s.post, and_assoc]

/-- Any accepting trace computes `accept (trace.word.foldl δ q₀) = true`. -/
theorem dfaRunAccepts_implies_foldl {State Sym : Type}
    {δ : State → Sym → State} {accept : State → Bool}
    {q : State} {steps : List (DfaStep State Sym)}
    (h : DfaRunAccepts δ accept q steps) :
    accept ((steps.map DfaStep.sym).foldl δ q) = true := by
  induction steps generalizing q with
  | nil => exact h
  | cons s rest ih =>
      rcases h with ⟨rfl, hpost, hrest⟩
      simp only [List.map_cons, List.foldl_cons, ← hpost]
      exact ih hrest

/-- Canonical trace builder for `w` under `δ` starting at `q`. -/
def buildDfaTrace {State Sym : Type} (δ : State → Sym → State) :
    State → List Sym → List (DfaStep State Sym)
  | _, [] => []
  | q, a :: ws => ⟨q, a, δ q a⟩ :: buildDfaTrace δ (δ q a) ws

theorem buildDfaTrace_word {State Sym : Type} (δ : State → Sym → State)
    (q : State) (w : List Sym) :
    (DfaTrace.mk (buildDfaTrace δ q w)).word = w := by
  induction w generalizing q with
  | nil => rfl
  | cons a ws ih =>
      simp only [DfaTrace.word, buildDfaTrace, List.map_cons]
      exact congrArg (a :: ·) (ih (δ q a))

theorem buildDfaTrace_accepts_iff {State Sym : Type}
    (δ : State → Sym → State) (accept : State → Bool) (q : State) (w : List Sym) :
    DfaAccepts δ q accept ⟨buildDfaTrace δ q w⟩ ↔ accept (w.foldl δ q) = true := by
  unfold DfaAccepts
  induction w generalizing q with
  | nil => simp [buildDfaTrace, DfaRunAccepts]
  | cons a ws ih => simp [buildDfaTrace, DfaRunAccepts, ih (δ q a)]

/-- Word-free `UnboundDfaStmt` (`CERTIFICATES.md` §0.1): carries `δ, q₀, accept` and **no** `c`. -/
structure UnboundDfaStmt (State Sym : Type) where
  δ      : State → Sym → State
  q₀     : State
  accept : State → Bool

/-- Word-free verifier kernel (`dfa_verify_sound` shape). -/
structure UnboundDfaKernel (State Sym Proof : Type) where
  verify  : UnboundDfaStmt State Sym → Proof → Bool
  extract : ∀ (stmt : UnboundDfaStmt State Sym) (π : Proof),
    verify stmt π = true → ∃ trace : DfaTrace State Sym, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace

theorem dfa_verify_sound {State Sym Proof : Type}
    (K : UnboundDfaKernel State Sym Proof) (stmt : UnboundDfaStmt State Sym) (π : Proof)
    (hacc : K.verify stmt π = true) :
    ∃ trace : DfaTrace State Sym, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace :=
  K.extract stmt π hacc

/-- **`L0` / `P6` Content-Bound DFA Statement (`CERTIFICATES.md` §5 `P6`)**:
extends `UnboundDfaStmt` with the committed record digest `c : Digest`. -/
structure BoundDfaStmt (State Sym Digest : Type) extends UnboundDfaStmt State Sym where
  c : Digest

/-- Content-bound DFA verifier kernel under `ContentScheme` `S`. -/
structure BoundDfaKernel {Sym Digest Op : Type} (S : ContentScheme Sym Digest Op)
    (State Proof : Type) where
  verify  : BoundDfaStmt State Sym Digest → Proof → Bool
  extract : ∀ (stmt : BoundDfaStmt State Sym Digest) (π : Proof),
    verify stmt π = true →
      ∃ w : List Sym, S.commit w = stmt.c ∧
        ∃ trace : DfaTrace State Sym,
          DfaAccepts stmt.δ stmt.q₀ stmt.accept trace ∧ trace.word = w

/-- **`P6` `dfa_bound_sound`**: an accepted content-bound DFA proof guarantees a word `w`
committed at `stmt.c` and an accepting trace with `trace.word = w`. -/
theorem dfa_bound_sound {Sym Digest Op State Proof : Type}
    {S : ContentScheme Sym Digest Op} (K : BoundDfaKernel S State Proof)
    (stmt : BoundDfaStmt State Sym Digest) (π : Proof)
    (hacc : K.verify stmt π = true) :
    ∃ w : List Sym, S.commit w = stmt.c ∧
      ∃ trace : DfaTrace State Sym,
        DfaAccepts stmt.δ stmt.q₀ stmt.accept trace ∧ trace.word = w :=
  K.extract stmt π hacc

/-- Every `BoundDfaKernel` for fixed automaton `A : UnboundDfaStmt State Sym` induces a zero-error
`CertSound` certificate for `∃ trace, DfaAccepts A.δ A.q₀ A.accept trace ∧ trace.word = w`. -/
theorem boundDfaKernel_certSound {Sym Digest Op State Proof : Type}
    {S : ContentScheme Sym Digest Op} (K : BoundDfaKernel S State Proof)
    (A : UnboundDfaStmt State Sym) (dflt : List Sym) :
    CertSound (unrestrictedEnv Sym) S
      (fun c π => K.verify ⟨A, c⟩ π)
      (fun w => ∃ trace : DfaTrace State Sym, DfaAccepts A.δ A.q₀ A.accept trace ∧ trace.word = w)
      (fun _ => 0) := by
  classical
  let ext : Digest → Proof → (unrestrictedEnv Sym).Log → List Sym := fun c π _ =>
    if h : K.verify ⟨A, c⟩ π = true then (K.extract ⟨A, c⟩ π h).choose else dflt
  refine ⟨ext, fun q c π log _ => ?_⟩
  have hfalse : ∀ ω : (unrestrictedEnv Sym).Coins q,
      ¬ (K.verify ⟨A, c ω⟩ (π ω) = true ∧
          ¬ ((unrestrictedEnv Sym).Grounded (log ω) (ext (c ω) (π ω) (log ω)) ∧
              S.commit (ext (c ω) (π ω) (log ω)) = c ω ∧
              ∃ trace : DfaTrace State Sym,
                DfaAccepts A.δ A.q₀ A.accept trace ∧ trace.word = ext (c ω) (π ω) (log ω))) := by
    intro ω ⟨hv, hbad⟩
    have hex : S.commit (ext (c ω) (π ω) (log ω)) = c ω ∧
        ∃ trace, DfaAccepts A.δ A.q₀ A.accept trace ∧ trace.word = ext (c ω) (π ω) (log ω) := by
      simp only [ext, hv, ↓reduceDIte]
      exact (K.extract ⟨A, c ω⟩ (π ω) hv).choose_spec
    exact hbad ⟨trivial, hex.1, hex.2⟩
  rw [prob_eq_zero_of_false hfalse]

/-- Honest executable `BoundDfaKernel` over `idealContentScheme` (satisfying witness). -/
def honestIdealDfaKernel (State Sym : Type) [DecidableEq State] [DecidableEq Sym] :
    BoundDfaKernel (idealContentScheme Sym) State (DfaTrace State Sym) where
  verify := fun stmt trace =>
    decide ((idealContentScheme Sym).commit trace.word = stmt.c) &&
      dfaRunAcceptsB stmt.δ stmt.accept stmt.q₀ trace.steps
  extract := fun stmt trace hv => by
    rw [Bool.and_eq_true, decide_eq_true_eq, dfaRunAcceptsB_eq_true_iff] at hv
    exact ⟨trace.word, hv.1, trace, hv.2, rfl⟩

/-- Absence DFA for secret symbol `true` (`false` = clean `q₀`, `true` = tainted trap). -/
def noSecretDfa : UnboundDfaStmt Bool Bool where
  δ := fun q a => q || a
  q₀ := false
  accept := fun q => !q

/-- **Zero-Work Splice Kernel**: ignores the proof and any record, checking ONLY `stmt.accept stmt.q₀`
(which holds for every absence automaton avoiding a non-empty pattern, via the empty trace `[]`). -/
def spliceUnboundKernel (State Sym : Type) : UnboundDfaKernel State Sym Unit where
  verify := fun stmt _ => stmt.accept stmt.q₀
  extract := fun _stmt _ hv => ⟨⟨[]⟩, hv⟩

/-- **`P6` Constructive Zero-Work Splice Separation (`unbound_dfa_splice_falsifier`)**:
On `noSecretDfa` and committed **forbidden** record `w_forbidden = [true]` (`c_bad = [true]`):
1. `spliceUnboundKernel` satisfies word-free `dfa_verify_sound` universally AND accepts `noSecretDfa`;
2. Honest `honestIdealDfaKernel` accepts benign `[false, false]` (`dfa_bound_sound` satisfiable);
3. `dfa_bound_sound`'s conclusion is **FALSE** on `⟨noSecretDfa, [true]⟩` (and `honestIdealDfaKernel`
   rejects every candidate trace against `[true]`). -/
theorem unbound_dfa_splice_falsifier :
    let S := idealContentScheme Bool
    let c_benign := S.commit [false, false]
    let c_forbidden := S.commit [true]
    -- (1) Word-ignoring splice verifier accepts and satisfies word-free dfa_verify_sound:
    ((spliceUnboundKernel Bool Bool).verify noSecretDfa () = true ∧
      ∃ trace, DfaAccepts noSecretDfa.δ noSecretDfa.q₀ noSecretDfa.accept trace) ∧
    -- (2) Honest content-bound verifier accepts benign [false, false]:
    (honestIdealDfaKernel Bool Bool).verify ⟨noSecretDfa, c_benign⟩
      ⟨buildDfaTrace noSecretDfa.δ noSecretDfa.q₀ [false, false]⟩ = true ∧
    -- (3) Content-bound soundness conclusion is FALSE on forbidden record [true]:
    ¬ (∃ w : List Bool, S.commit w = c_forbidden ∧
        ∃ trace : DfaTrace Bool Bool,
          DfaAccepts noSecretDfa.δ noSecretDfa.q₀ noSecretDfa.accept trace ∧ trace.word = w) := by
  refine ⟨⟨rfl, dfa_verify_sound (spliceUnboundKernel Bool Bool) noSecretDfa () rfl⟩,
    by decide, ?_⟩
  rintro ⟨w, hw, trace, hacc, hword⟩
  have hweq : w = [true] := hw
  subst hweq
  have hfold := dfaRunAccepts_implies_foldl hacc
  change noSecretDfa.accept (trace.word.foldl noSecretDfa.δ noSecretDfa.q₀) = true at hfold
  rw [hword] at hfold
  exact absurd hfold (by decide)

/-! ## §4. `L2` / `P7`: `AllRecords` Corpus Union Bound (`cert_allRecords`) & 1-Felt vs 8-Felt Tooth -/

/-- General finite union bound over `Fin N` in `BindingGame.prob` (requires no `0 ≤ ε` guard). -/
theorem prob_exists_fin_le {Ω : Type} [Fintype Ω] {N : ℕ}
    (bad : Fin N → Ω → Prop) {ε : ℝ}
    (h : ∀ k : Fin N, BindingGame.prob (bad k) ≤ ε) :
    BindingGame.prob (fun ω => ∃ k : Fin N, bad k ω) ≤ (N : ℝ) * ε := by
  classical
  have hsum : BindingGame.prob (fun ω => ∃ k : Fin N, bad k ω) ≤
      ∑ k : Fin N, BindingGame.prob (bad k) := by
    unfold BindingGame.prob
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun ω _ => ?_)
    split_ifs with hex
    · rcases hex with ⟨k₀, hk₀⟩
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin N)),
          0 ≤ (if bad k ω then (1 : ℝ) else 0) := fun k _ => by split_ifs <;> norm_num
      have hle := Finset.single_le_sum hnonneg (Finset.mem_univ k₀)
      simpa [hk₀] using hle
    · exact Finset.sum_nonneg (fun k _ => by split_ifs <;> norm_num)
  have hbound : (∑ k : Fin N, BindingGame.prob (bad k)) ≤ (N : ℝ) * ε := by
    calc ∑ k : Fin N, BindingGame.prob (bad k)
        ≤ ∑ _k : Fin N, ε := Finset.sum_le_sum (fun k _ => h k)
      _ = (N : ℝ) * ε := by simp
  rcases Nat.eq_zero_or_pos N with rfl | _
  · have hempty : ∀ ω : Ω, ¬ (∃ k : Fin 0, bad k ω) := fun _ ⟨k, _⟩ => Fin.elim0 k
    rw [prob_eq_zero_of_false hempty]
    simp
  · exact le_trans hsum hbound

/-- Corpus/MMR commitment scheme over leaf digests `Fin N → Digest` (`CERTIFICATES.md` §1 & L2). -/
structure MmrScheme (Digest Root MmrProof : Type) where
  mroot        : ∀ {N : ℕ}, (Fin N → Digest) → Root
  openLeaves   : ∀ {N : ℕ}, (Fin N → Digest) → MmrProof
  verifyLeaves : ∀ (N : ℕ), Root → (Fin N → Digest) → MmrProof → Bool
  complete     : ∀ {N : ℕ} (L : Fin N → Digest),
    verifyLeaves N (mroot L) L (openLeaves L) = true
  mmrBindAdv   : ℕ → ℝ
  mmrBindAdv_nonneg : ∀ q : ℕ, 0 ≤ mmrBindAdv q

/-- A leaf-digest vector `L : Fin N → Digest` is grounded in query log `l` when every leaf `L k`
has a `Grounded` preimage word in `l` (established automatically off the `N` `CertSound` legs!). -/
def GroundedLeaves {Sym Digest Op : Type} (E : QueryEnv Sym)
    (S : ContentScheme Sym Digest Op) (l : E.Log) {N : ℕ} (L : Fin N → Digest) : Prop :=
  ∀ k : Fin N, ∃ w : List Sym, E.Grounded l w ∧ S.commit w = L k

/-- Computational binding of an `MmrScheme` against log-grounded leaf-vector equivocation
(preventing the W4 pigeonhole collapse on compressing MMR roots). -/
def MmrBindSound {Sym Digest Op Root MmrProof : Type}
    (E : QueryEnv Sym) (S : ContentScheme Sym Digest Op)
    (Mmr : MmrScheme Digest Root MmrProof) : Prop :=
  ∀ (q N : ℕ) (L_true : Fin N → Digest) (L_claim : E.Coins q → Fin N → Digest)
    (π_mmr : E.Coins q → MmrProof) (log : E.Coins q → E.Log),
    E.ValidLog q log →
    (∀ ω, GroundedLeaves E S (log ω) L_true) →
    BindingGame.prob (fun ω =>
      GroundedLeaves E S (log ω) (L_claim ω) ∧
        Mmr.verifyLeaves N (Mmr.mroot L_true) (L_claim ω) (π_mmr ω) = true ∧
        L_claim ω ≠ L_true) ≤ Mmr.mmrBindAdv q

/-- **`AllRecords` relation (`CERTIFICATES.md` §1)**: `R` commits `N` leaf digests each satisfied
by some committed word under `φ`. -/
def AllRecords {Sym Digest Op Root MmrProof : Type}
    (Mmr : MmrScheme Digest Root MmrProof) (S : ContentScheme Sym Digest Op)
    (R : Root) (N : ℕ) (φ : List Sym → Prop) : Prop :=
  ∃ L : Fin N → Digest, Mmr.mroot L = R ∧ ∀ k : Fin N, ∃ w : List Sym, S.commit w = L k ∧ φ w

/-- **`L2` / `P7` Corpus Aggregation Union Bound (`cert_allRecords`, `CERTIFICATES.md` §2 L2)**:
Given `N` per-record certificates verified by `V` alongside an MMR leaf opening against
`R = Mmr.mroot (fun k => S.commit (ws k))`:
- both `AllRecords Mmr S R N φ` AND full attribution **`∀ k : Fin N, φ (ws k)`** hold outside
  probability **`(N : ℝ) * ε q + Mmr.mmrBindAdv q + S.bindAdv q`** (`S.bindAdv q` charged **once**,
  not `N` times, by extracting the first mismatching corpus index!). -/
theorem cert_allRecords {Sym Digest Op Proof Root MmrProof : Type}
    {E : QueryEnv Sym}
    (Mmr : MmrScheme Digest Root MmrProof)
    (S : ContentScheme Sym Digest Op)
    {V : Digest → Proof → Bool} {φ : List Sym → Prop} {ε : ℕ → ℝ}
    (hcert : CertSound E S V φ ε)
    (hmmr : MmrBindSound E S Mmr)
    (hbind : BindSound E S)
    {N : ℕ} (ws : Fin N → List Sym)
    (q : ℕ)
    (L_claim : E.Coins q → Fin N → Digest)
    (πs : E.Coins q → Fin N → Proof)
    (π_mmr : E.Coins q → MmrProof)
    (log : E.Coins q → E.Log)
    (hlog : E.ValidLog q log)
    (hws_gr : ∀ (k : Fin N) (ω : E.Coins q), E.Grounded (log ω) (ws k)) :
    let L_true : Fin N → Digest := fun k => S.commit (ws k)
    let R : Root := Mmr.mroot L_true
    let corpusVerify : E.Coins q → Bool := fun ω =>
      Mmr.verifyLeaves N R (L_claim ω) (π_mmr ω) &&
        (List.finRange N).all (fun k => V (L_claim ω k) (πs ω k))
    BindingGame.prob (fun ω =>
      corpusVerify ω = true ∧ ¬ (AllRecords Mmr S R N φ ∧ ∀ k : Fin N, φ (ws k)))
      ≤ (N : ℝ) * ε q + Mmr.mmrBindAdv q + S.bindAdv q := by
  classical
  rcases hcert with ⟨ext, hs⟩
  intro L_true R corpusVerify
  let w_ext : Fin N → E.Coins q → List Sym := fun k ω => ext (L_claim ω k) (πs ω k) (log ω)
  let badCert : Fin N → E.Coins q → Prop := fun k ω =>
    V (L_claim ω k) (πs ω k) = true ∧
      ¬ (E.Grounded (log ω) (w_ext k ω) ∧ S.commit (w_ext k ω) = L_claim ω k ∧ φ (w_ext k ω))
  let badMmr : E.Coins q → Prop := fun ω =>
    GroundedLeaves E S (log ω) (L_claim ω) ∧
      Mmr.verifyLeaves N R (L_claim ω) (π_mmr ω) = true ∧ L_claim ω ≠ L_true
  let badBind : E.Coins q → Prop := fun ω =>
    ∃ k : Fin N, E.Grounded (log ω) (w_ext k ω) ∧ E.Grounded (log ω) (ws k) ∧
      S.commit (w_ext k ω) = S.commit (ws k) ∧ w_ext k ω ≠ ws k
  have hcert_union : BindingGame.prob (fun ω => ∃ k : Fin N, badCert k ω) ≤ (N : ℝ) * ε q :=
    prob_exists_fin_le badCert (fun k => hs q (fun ω => L_claim ω k) (fun ω => πs ω k) log hlog)
  have htrue_gr : ∀ ω, GroundedLeaves E S (log ω) L_true :=
    fun ω k => ⟨ws k, hws_gr k ω, rfl⟩
  have hmmr_b : BindingGame.prob badMmr ≤ Mmr.mmrBindAdv q :=
    hmmr q N L_true L_claim π_mmr log hlog htrue_gr
  have hbind_b : BindingGame.prob badBind ≤ S.bindAdv q := by
    let u₁ : E.Coins q → List Sym := fun ω =>
      if h : badBind ω then w_ext h.choose ω else []
    let u₂ : E.Coins q → List Sym := fun ω =>
      if h : badBind ω then ws h.choose else []
    have hsub : BindingGame.prob badBind ≤
        BindingGame.prob (fun ω =>
          E.Grounded (log ω) (u₁ ω) ∧ E.Grounded (log ω) (u₂ ω) ∧
            S.commit (u₁ ω) = S.commit (u₂ ω) ∧ u₁ ω ≠ u₂ ω) := by
      apply BindingGame.prob_mono
      intro ω hb
      simp only [u₁, u₂, hb, ↓reduceDIte]
      exact hb.choose_spec
    exact le_trans hsub (hbind q log hlog u₁ u₂)
  have hcov : BindingGame.prob (fun ω =>
      corpusVerify ω = true ∧ ¬ (AllRecords Mmr S R N φ ∧ ∀ k : Fin N, φ (ws k))) ≤
      BindingGame.prob (fun ω =>
        (∃ k : Fin N, badCert k ω) ∨ (badMmr ω ∨ badBind ω)) := by
    apply BindingGame.prob_mono
    intro ω ⟨hver, hfail⟩
    dsimp only [corpusVerify] at hver
    rw [Bool.and_eq_true, List.all_eq_true] at hver
    rcases hver with ⟨hvMmr, hvAll⟩
    by_cases hbc : ∃ k : Fin N, badCert k ω
    · exact Or.inl hbc
    · by_cases hbm : badMmr ω
      · exact Or.inr (Or.inl hbm)
      · by_cases hbb : badBind ω
        · exact Or.inr (Or.inr hbb)
        · exfalso
          have hgood_all : ∀ k : Fin N,
              E.Grounded (log ω) (w_ext k ω) ∧
                S.commit (w_ext k ω) = L_claim ω k ∧ φ (w_ext k ω) := by
            intro k
            have hvk : V (L_claim ω k) (πs ω k) = true := hvAll k (List.mem_finRange k)
            by_contra hng
            exact hbc ⟨k, hvk, hng⟩
          have hclaim_gr : GroundedLeaves E S (log ω) (L_claim ω) :=
            fun k => ⟨w_ext k ω, (hgood_all k).1, (hgood_all k).2.1⟩
          have hLeq : L_claim ω = L_true := by
            by_contra hne
            exact hbm ⟨hclaim_gr, hvMmr, hne⟩
          have hphi_ws : ∀ k : Fin N, φ (ws k) := by
            intro k
            have hgood := hgood_all k
            have hcomm : S.commit (w_ext k ω) = S.commit (ws k) := by
              rw [hgood.2.1, hLeq]
            have hw_eq : w_ext k ω = ws k := by
              by_contra hne
              exact hbb ⟨k, hgood.1, hws_gr k ω, hcomm, hne⟩
            exact hw_eq ▸ hgood.2.2
          have hallRec : AllRecords Mmr S R N φ :=
            ⟨L_true, rfl, fun k => ⟨ws k, rfl, hphi_ws k⟩⟩
          exact hfail ⟨hallRec, hphi_ws⟩
  have hu₁ := BindingGame.prob_or (fun ω => ∃ k : Fin N, badCert k ω) (fun ω => badMmr ω ∨ badBind ω)
  have hu₂ := BindingGame.prob_or badMmr badBind
  linarith

/-- Ideal non-compressing MMR scheme (`mmrBindAdv = 0`). -/
def idealMmrScheme (Digest : Type) [DecidableEq Digest] :
    MmrScheme Digest (List Digest) Unit where
  mroot := fun L => List.ofFn L
  openLeaves := fun _ => ()
  verifyLeaves := fun _ R L _ => decide (List.ofFn L = R)
  complete := fun L => by simp
  mmrBindAdv := fun _ => 0
  mmrBindAdv_nonneg := fun _ => le_rfl

theorem idealMmrScheme_bindSound {Sym Digest Op : Type} [DecidableEq Digest]
    (E : QueryEnv Sym) (S : ContentScheme Sym Digest Op) :
    MmrBindSound E S (idealMmrScheme Digest) := by
  intro q N L_true L_claim π_mmr log _ _
  have hfalse : ∀ ω : E.Coins q,
      ¬ (GroundedLeaves E S (log ω) (L_claim ω) ∧
          (idealMmrScheme Digest).verifyLeaves N ((idealMmrScheme Digest).mroot L_true)
            (L_claim ω) (π_mmr ω) = true ∧ L_claim ω ≠ L_true) := by
    intro ω ⟨_, hv, hne⟩
    simp only [idealMmrScheme, decide_eq_true_eq] at hv
    apply hne
    funext k
    have hk := congrArg (fun l : List Digest => l[k.1]?) hv
    simpa using hk
  rw [prob_eq_zero_of_false hfalse]
  exact (idealMmrScheme Digest).mmrBindAdv_nonneg q

/-- **Compressing `MmrScheme` Non-Vacuity Witness (`0 < mmrBindAdv = 1/2 < 1`)**:
`unitMmrScheme` compresses any leaf vector `Fin N → ZMod 2` into `Unit` (`()`). Over `sampledMmrEnv`
(`log true = [[0, 0]]`, `log false = [[0, 0], [0, 1]]`), `GroundedLeaves` pins every leaf to `0` on
`true`, so `MmrBindSound` holds at nontrivial compressing budget `mmrBindAdv = 1 / 2`. -/
@[reducible] def sampledMmrEnv : QueryEnv (ZMod 2) where
  Coins := fun _ => Bool
  Log := List (List (ZMod 2))
  coinsFintype := fun _ => inferInstance
  coinsNonempty := fun _ => ⟨true⟩
  ValidLog := fun _ log => ∀ b : Bool, log b = if b then [[0, 0]] else [[0, 0], [0, 1]]
  Grounded := fun l w => w ∈ l

@[reducible] noncomputable def compressingUnitMmr : MmrScheme (ZMod 2) Unit Unit where
  mroot := fun _ => ()
  openLeaves := fun _ => ()
  verifyLeaves := fun _ _ _ _ => true
  complete := fun _ => rfl
  mmrBindAdv := fun _ => 1 / 2
  mmrBindAdv_nonneg := fun _ => by norm_num

theorem compressingUnitMmr_bindSound :
    MmrBindSound sampledMmrEnv parityHalfScheme compressingUnitMmr := by
  intro q N L_true L_claim _ log hlog htrue_gr
  have hno_true : ¬ (GroundedLeaves sampledMmrEnv parityHalfScheme (log true) (L_claim true) ∧
      compressingUnitMmr.verifyLeaves N (compressingUnitMmr.mroot L_true) (L_claim true) () = true ∧
      L_claim true ≠ L_true) := by
    rintro ⟨hcl, _, hne⟩
    apply hne
    funext k
    rcases hcl k with ⟨wc, hwc_mem, hwc_eq⟩
    rcases htrue_gr true k with ⟨wt, hwt_mem, hwt_eq⟩
    change wc ∈ log true at hwc_mem
    change wt ∈ log true at hwt_mem
    rw [hlog true] at hwc_mem hwt_mem
    simp only [↓reduceIte, List.mem_singleton] at hwc_mem hwt_mem
    rw [← hwc_eq, ← hwt_eq, hwc_mem, hwt_mem]
  classical
  unfold BindingGame.prob
  rw [Fintype.sum_bool, Fintype.card_bool]
  split_ifs with ht _
  · exact False.elim (hno_true ht)
  · exact False.elim (hno_true ht)
  · norm_num
  · norm_num

/-! ### `P7` 1-Felt vs 8-Felt (`Fin 8 → BabyBear`) Collision & `AllRecords` Falsifiers -/

/-- **8-lane Poseidon2/BabyBear digest (`CERTIFICATES.md` §§0.3, 3a, `P7`)**: `Fin 8 → BabyBear`
(`BabyBear = ZMod 2013265921` from `Selvage/BabyBearExt4.lean`, ~248 bits across 8 lanes). -/
abbrev Digest8 : Type := Fin 8 → BabyBear

/-- Buggy lane-0 projection (`DescriptorIR2.MapOp.holdsAt` reading `root 0` only, `CERTIFICATES.md` §0.3). -/
def lane0Proj (d : Digest8) : BabyBear := d 0

/-- **`P7` Lane-0 vs 8-Lane Splice Falsifier (`digest8_lane0_splice_falsifier`)**:
Two distinct 8-lane digests `d_good ≠ d_bad : Digest8` collide on lane 0 (`lane0Proj d_good =
lane0Proj d_bad`), demonstrating why reading lane 0 alone drops 7 of 8 BabyBear lanes (~217 bits). -/
def digest8Zero : Digest8 := fun _ => 0
def digest8Lane1Set : Digest8 := fun i => if i = 0 then 0 else 1

theorem digest8_lane0_splice_falsifier :
    lane0Proj digest8Zero = lane0Proj digest8Lane1Set ∧
    digest8Zero ≠ digest8Lane1Set := by
  refine ⟨rfl, fun heq => ?_⟩
  have h1 : digest8Zero 1 = digest8Lane1Set 1 := congrFun heq 1
  have hne : (0 : BabyBear) ≠ 1 := by decide
  exact hne h1

/-- 1-felt vs 8-lane (`Digest8`) `ContentScheme` instances over `List ℕ` scalar records. -/
def oneFeltScalarCommit (w : List ℕ) : BabyBear :=
  ((w.foldr (· + ·) 0 : ℕ) : BabyBear)

def eightFeltScalarCommit (w : List ℕ) : Digest8 :=
  let s := w.foldr (· + ·) 0
  fun lane => ((s / modulus ^ lane.1 : ℕ) : BabyBear)

def oneFeltContentScheme : ContentScheme ℕ BabyBear (List ℕ) where
  commit := oneFeltScalarCommit
  openAt := fun w _ => w
  openLen := fun w => w
  verifyOpen := fun c i v o => decide (oneFeltScalarCommit o = c ∧ o[i]? = some v)
  verifyLen := fun c n o => decide (oneFeltScalarCommit o = c ∧ o.length = n)
  complete := fun w i hi => by simp [List.getElem?_eq_getElem hi]
  completeLen := fun w => by simp
  bindAdv := fun _ => 1
  bindAdv_nonneg := fun _ => by norm_num

def eightFeltContentScheme : ContentScheme ℕ Digest8 (List ℕ) where
  commit := eightFeltScalarCommit
  openAt := fun w _ => w
  openLen := fun w => w
  verifyOpen := fun c i v o => decide (eightFeltScalarCommit o = c ∧ o[i]? = some v)
  verifyLen := fun c n o => decide (eightFeltScalarCommit o = c ∧ o.length = n)
  complete := fun w i hi => by simp [List.getElem?_eq_getElem hi]
  completeLen := fun w => by simp
  bindAdv := fun _ => 1
  bindAdv_nonneg := fun _ => by norm_num

/-- **`P7` 1-Felt Wraparound Falsifier Over `AllRecords` (`oneFelt_wraparound_breaks_allRecords`)**:
Consider forbidden 1-record corpus `ws := fun _ : Fin 1 => [modulus]` (`2013265921 ≠ 0`) and
policy `φ w := (w = [0])` (`¬ ∀ k, φ (ws k)`):
1. Under 1-felt `oneFeltContentScheme`, `AllRecords (idealMmrScheme BabyBear) oneFeltContentScheme R₁ 1 φ`
   **HOLDS** (witnessed by `[0]`, since `(modulus : BabyBear) = 0`), breaking corpus attribution!
2. Under 8-lane `eightFeltContentScheme` (`Digest8`), `AllRecords (idealMmrScheme Digest8) eightFeltContentScheme R₈ 1 φ`
   is **REFUSED** (`eightFeltScalarCommit [0] ≠ eightFeltScalarCommit [modulus]` at lane `1`)! -/
theorem oneFelt_wraparound_breaks_allRecords :
    let ws : Fin 1 → List ℕ := fun _ => [modulus]
    let φ : List ℕ → Prop := fun w => w = [0]
    let R₁ := (idealMmrScheme BabyBear).mroot (fun k => oneFeltContentScheme.commit (ws k))
    let R₈ := (idealMmrScheme Digest8).mroot (fun k => eightFeltContentScheme.commit (ws k))
    (¬ ∀ k : Fin 1, φ (ws k)) ∧
    AllRecords (idealMmrScheme BabyBear) oneFeltContentScheme R₁ 1 φ ∧
    ¬ AllRecords (idealMmrScheme Digest8) eightFeltContentScheme R₈ 1 φ := by
  refine ⟨?_, ?_, ?_⟩
  · intro hall
    have h0 := hall 0
    simp [modulus] at h0
  · refine ⟨fun _ => oneFeltContentScheme.commit [modulus], rfl, fun _ => ⟨[0], ?_, rfl⟩⟩
    simp [oneFeltContentScheme, oneFeltScalarCommit]
  · rintro ⟨L, hL, hall⟩
    rcases hall 0 with ⟨w, hw_comm, rfl⟩
    have hL0 : L 0 = eightFeltContentScheme.commit [modulus] := by
      have hk := congrArg (fun l : List Digest8 => l[0]?) hL
      simpa [idealMmrScheme] using hk
    have heq : eightFeltScalarCommit [0] = eightFeltScalarCommit [modulus] :=
      hw_comm.trans hL0
    have h1 := congrFun heq 1
    simp only [eightFeltScalarCommit, List.foldr_cons, List.foldr_nil, Nat.add_zero, Fin.val_one,
      pow_one, Nat.zero_div, Nat.cast_zero, Nat.div_self (by norm_num [modulus] : 0 < modulus),
      Nat.cast_one] at h1
    exact absurd h1 (by decide)

/-! ## §5. `L4` / `P8` (`cert_produced_weld` + `TK` Tooth), `L5` (`cert_mapScheme`), & `Pred` Bridge -/

/-- **`Produced` Inference Soundness (`CERTIFICATES.md` §1 & §3c, FlashProve `Sound` shape)**:
an inference verifier `V_inf` for `(m, c_in, c_out)` has a straightline query-log extractor
recovering log-grounded `out` with `IsModelOutput m c_in out ∧ S_inf.commit out = c_out` up to `ε_inf q`. -/
def ProducedSound {Model PromptDigest Sym DigestInf OpInf InfProof : Type}
    (E : QueryEnv Sym) (S_inf : ContentScheme Sym DigestInf OpInf)
    (IsModelOutput : Model → PromptDigest → List Sym → Prop)
    (V_inf : Model → PromptDigest → DigestInf → InfProof → Bool)
    (ε_inf : ℕ → ℝ) : Prop :=
  ∃ ext_inf : Model → PromptDigest → DigestInf → InfProof → E.Log → List Sym,
    ∀ (q : ℕ) (m : E.Coins q → Model) (cin : E.Coins q → PromptDigest)
      (cout : E.Coins q → DigestInf) (π : E.Coins q → InfProof) (log : E.Coins q → E.Log),
      E.ValidLog q log →
      BindingGame.prob (fun ω =>
        V_inf (m ω) (cin ω) (cout ω) (π ω) = true ∧
          ¬ (E.Grounded (log ω) (ext_inf (m ω) (cin ω) (cout ω) (π ω) (log ω)) ∧
              IsModelOutput (m ω) (cin ω) (ext_inf (m ω) (cin ω) (cout ω) (π ω) (log ω)) ∧
              S_inf.commit (ext_inf (m ω) (cin ω) (cout ω) (π ω) (log ω)) = cout ω))
        ≤ ε_inf q

/-- **Cross-scheme `Bridge` Soundness (`CERTIFICATES.md` §2 L4)**:
whenever grounded `out` commits to `c_out` under `S_inf` and grounded `w` commits to `c'_out`
under `S_cert`, `V_bridge c_out c'_out π_b = true` with `out ≠ w` occurs with probability `≤ ε_br q`. -/
def BridgeSound {Sym DigestInf OpInf DigestCert OpCert BridgeProof : Type}
    (E : QueryEnv Sym)
    (S_inf : ContentScheme Sym DigestInf OpInf)
    (S_cert : ContentScheme Sym DigestCert OpCert)
    (V_bridge : DigestInf → DigestCert → BridgeProof → Bool)
    (ε_br : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) (cout : E.Coins q → DigestInf) (cout' : E.Coins q → DigestCert)
    (πb : E.Coins q → BridgeProof) (log : E.Coins q → E.Log),
    E.ValidLog q log →
    ∀ (out w : E.Coins q → List Sym),
      BindingGame.prob (fun ω =>
        E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
          V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
          S_inf.commit (out ω) = cout ω ∧
          S_cert.commit (w ω) = cout' ω ∧
          out ω ≠ w ω)
        ≤ ε_br q

/-- **`L4` / `P8` Model-Identity Weld (`cert_produced_weld`, `CERTIFICATES.md` §2 L4)**:
`Produced(m, c_in, c_out; ε_inf) ∧ Cert(c'_out, φ; ε_c) ∧ Bridge(c_out, c'_out; ε_bridge)`
implies straightline extraction of grounded `out` satisfying `IsModelOutput m c_in out ∧ φ out`
with error **`ε_inf q + ε_c q + ε_bridge q`**. -/
theorem cert_produced_weld
    {Model PromptDigest Sym DigestInf OpInf DigestCert OpCert InfProof CertProof BridgeProof : Type}
    {E : QueryEnv Sym}
    {S_inf : ContentScheme Sym DigestInf OpInf}
    {S_cert : ContentScheme Sym DigestCert OpCert}
    {IsModelOutput : Model → PromptDigest → List Sym → Prop}
    {V_inf : Model → PromptDigest → DigestInf → InfProof → Bool}
    {V_cert : DigestCert → CertProof → Bool}
    {V_bridge : DigestInf → DigestCert → BridgeProof → Bool}
    {φ : List Sym → Prop} {ε_inf ε_c ε_bridge : ℕ → ℝ}
    (hinf : ProducedSound E S_inf IsModelOutput V_inf ε_inf)
    (hcert : CertSound E S_cert V_cert φ ε_c)
    (hbr : BridgeSound E S_inf S_cert V_bridge ε_bridge) :
    ∃ ext_out : Model → PromptDigest → DigestInf → InfProof → E.Log → List Sym,
      ∀ (q : ℕ) (m : E.Coins q → Model) (cin : E.Coins q → PromptDigest)
        (cout : E.Coins q → DigestInf) (cout' : E.Coins q → DigestCert)
        (πi : E.Coins q → InfProof) (πc : E.Coins q → CertProof)
        (πb : E.Coins q → BridgeProof) (log : E.Coins q → E.Log),
        E.ValidLog q log →
        BindingGame.prob (fun ω =>
          (V_inf (m ω) (cin ω) (cout ω) (πi ω) &&
           V_cert (cout' ω) (πc ω) &&
           V_bridge (cout ω) (cout' ω) (πb ω)) = true ∧
          ¬ (E.Grounded (log ω) (ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω)) ∧
              IsModelOutput (m ω) (cin ω) (ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω)) ∧
              φ (ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω))))
          ≤ ε_inf q + ε_c q + ε_bridge q := by
  rcases hinf with ⟨ext_inf, hs_i⟩
  rcases hcert with ⟨ext_c, hs_c⟩
  refine ⟨ext_inf, ?_⟩
  intro q m cin cout cout' πi πc πb log hlog
  let out : E.Coins q → List Sym := fun ω => ext_inf (m ω) (cin ω) (cout ω) (πi ω) (log ω)
  let w : E.Coins q → List Sym := fun ω => ext_c (cout' ω) (πc ω) (log ω)
  have hbi := hs_i q m cin cout πi log hlog
  have hbc := hs_c q cout' πc log hlog
  have hbbr := hbr q cout cout' πb log hlog out w
  have hcov : BindingGame.prob (fun ω =>
      (V_inf (m ω) (cin ω) (cout ω) (πi ω) &&
       V_cert (cout' ω) (πc ω) &&
       V_bridge (cout ω) (cout' ω) (πb ω)) = true ∧
        ¬ (E.Grounded (log ω) (out ω) ∧ IsModelOutput (m ω) (cin ω) (out ω) ∧ φ (out ω))) ≤
      BindingGame.prob (fun ω =>
        (V_inf (m ω) (cin ω) (cout ω) (πi ω) = true ∧
          ¬ (E.Grounded (log ω) (out ω) ∧ IsModelOutput (m ω) (cin ω) (out ω) ∧
              S_inf.commit (out ω) = cout ω)) ∨
        ((V_cert (cout' ω) (πc ω) = true ∧
            ¬ (E.Grounded (log ω) (w ω) ∧ S_cert.commit (w ω) = cout' ω ∧ φ (w ω))) ∨
          (E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
            V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
            S_inf.commit (out ω) = cout ω ∧ S_cert.commit (w ω) = cout' ω ∧ out ω ≠ w ω))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hacc, hfail⟩
    rw [Bool.and_eq_true, Bool.and_eq_true] at hacc
    rcases hacc with ⟨⟨hvi, hvc⟩, hvb⟩
    by_cases hgi : E.Grounded (log ω) (out ω) ∧ IsModelOutput (m ω) (cin ω) (out ω) ∧
        S_inf.commit (out ω) = cout ω
    · by_cases hgc : E.Grounded (log ω) (w ω) ∧ S_cert.commit (w ω) = cout' ω ∧ φ (w ω)
      · right; right
        refine ⟨hgi.1, hgc.1, hvb, hgi.2.2, hgc.2.1,
          fun heq => hfail ⟨hgi.1, hgi.2.1, heq.symm ▸ hgc.2.2⟩⟩
      · exact Or.inr (Or.inl ⟨hvc, hgc⟩)
    · exact Or.inl ⟨hvi, hgi⟩
  have hu₁ := BindingGame.prob_or
    (fun ω => V_inf (m ω) (cin ω) (cout ω) (πi ω) = true ∧
      ¬ (E.Grounded (log ω) (out ω) ∧ IsModelOutput (m ω) (cin ω) (out ω) ∧
          S_inf.commit (out ω) = cout ω))
    (fun ω => (V_cert (cout' ω) (πc ω) = true ∧
        ¬ (E.Grounded (log ω) (w ω) ∧ S_cert.commit (w ω) = cout' ω ∧ φ (w ω))) ∨
      (E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
        V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
        S_inf.commit (out ω) = cout ω ∧ S_cert.commit (w ω) = cout' ω ∧ out ω ≠ w ω))
  have hu₂ := BindingGame.prob_or
    (fun ω => V_cert (cout' ω) (πc ω) = true ∧
      ¬ (E.Grounded (log ω) (w ω) ∧ S_cert.commit (w ω) = cout' ω ∧ φ (w ω)))
    (fun ω => E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
      V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
      S_inf.commit (out ω) = cout ω ∧ S_cert.commit (w ω) = cout' ω ∧ out ω ≠ w ω)
  linarith

/-- Same-scheme `BridgeSound` instantiation (`c_out == c'_out` under `S`, e.g. `TK(window)`):
`BridgeSound` holds with `ε_br := S.bindAdv` whenever `BindSound E S` holds. -/
theorem bridgeSound_same_scheme {Sym Digest Op : Type} [DecidableEq Digest]
    {E : QueryEnv Sym} (S : ContentScheme Sym Digest Op) (hbind : BindSound E S) :
    BridgeSound E S S (fun c c' (_ : Unit) => decide (c = c')) S.bindAdv := by
  intro q cout cout' _ log hlog out w
  have hsub : BindingGame.prob (fun ω =>
      E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
        decide (cout ω = cout' ω) = true ∧
        S.commit (out ω) = cout ω ∧ S.commit (w ω) = cout' ω ∧ out ω ≠ w ω) ≤
      BindingGame.prob (fun ω =>
        E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
          S.commit (out ω) = S.commit (w ω) ∧ out ω ≠ w ω) := by
    apply BindingGame.prob_mono
    intro ω ⟨hgo, hgw, heq, ho, hw', hne⟩
    rw [decide_eq_true_eq] at heq
    exact ⟨hgo, hgw, ho.trans (heq.trans hw'.symm), hne⟩
  exact le_trans hsub (hbind q log hlog out w)

/-- Dual-commitment `BridgeSound` instantiation (`CERTIFICATES.md` §2 L4): an in-circuit re-hash
certificate proving `∃ w_b, Grounded w_b ∧ S_inf.commit w_b = c_out ∧ S_cert.commit w_b = c'_out`
(error `ε_pf`) realizes `BridgeSound` at `ε_bridge q = ε_pf q + S_inf.bindAdv q + S_cert.bindAdv q`. -/
theorem bridgeSound_of_dual_cert
    {Sym DigestInf OpInf DigestCert OpCert BridgeProof : Type}
    {E : QueryEnv Sym}
    (S_inf : ContentScheme Sym DigestInf OpInf)
    (S_cert : ContentScheme Sym DigestCert OpCert)
    (V_bridge : DigestInf → DigestCert → BridgeProof → Bool)
    (ε_pf : ℕ → ℝ)
    (hb_inf : BindSound E S_inf)
    (hb_cert : BindSound E S_cert)
    (hdual : ∃ ext_b : DigestInf → DigestCert → BridgeProof → E.Log → List Sym,
      ∀ (q : ℕ) (cout : E.Coins q → DigestInf) (cout' : E.Coins q → DigestCert)
        (πb : E.Coins q → BridgeProof) (log : E.Coins q → E.Log),
        E.ValidLog q log →
        BindingGame.prob (fun ω =>
          V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
            ¬ (E.Grounded (log ω) (ext_b (cout ω) (cout' ω) (πb ω) (log ω)) ∧
                S_inf.commit (ext_b (cout ω) (cout' ω) (πb ω) (log ω)) = cout ω ∧
                S_cert.commit (ext_b (cout ω) (cout' ω) (πb ω) (log ω)) = cout' ω))
          ≤ ε_pf q) :
    BridgeSound E S_inf S_cert V_bridge
      (fun q => ε_pf q + S_inf.bindAdv q + S_cert.bindAdv q) := by
  rcases hdual with ⟨ext_b, hs_b⟩
  intro q cout cout' πb log hlog out w
  let wb : E.Coins q → List Sym := fun ω => ext_b (cout ω) (cout' ω) (πb ω) (log ω)
  have h1 := hs_b q cout cout' πb log hlog
  have h2 := hb_inf q log hlog out wb
  have h3 := hb_cert q log hlog wb w
  have hcov : BindingGame.prob (fun ω =>
      E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (w ω) ∧
        V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
        S_inf.commit (out ω) = cout ω ∧ S_cert.commit (w ω) = cout' ω ∧ out ω ≠ w ω) ≤
      BindingGame.prob (fun ω =>
        (V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
          ¬ (E.Grounded (log ω) (wb ω) ∧
              S_inf.commit (wb ω) = cout ω ∧ S_cert.commit (wb ω) = cout' ω)) ∨
        ((E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (wb ω) ∧
            S_inf.commit (out ω) = S_inf.commit (wb ω) ∧ out ω ≠ wb ω) ∨
          (E.Grounded (log ω) (wb ω) ∧ E.Grounded (log ω) (w ω) ∧
            S_cert.commit (wb ω) = S_cert.commit (w ω) ∧ wb ω ≠ w ω))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hgo, hgw, hvb, ho, hw', hne⟩
    by_cases hgb : E.Grounded (log ω) (wb ω) ∧
        S_inf.commit (wb ω) = cout ω ∧ S_cert.commit (wb ω) = cout' ω
    · by_cases heq1 : out ω = wb ω
      · right; right
        exact ⟨hgb.1, hgw, hgb.2.2.trans hw'.symm, fun heq2 => hne (heq1.trans heq2)⟩
      · right; left
        exact ⟨hgo, hgb.1, ho.trans hgb.2.1.symm, heq1⟩
    · exact Or.inl ⟨hvb, hgb⟩
  have hu₁ := BindingGame.prob_or
    (fun ω => V_bridge (cout ω) (cout' ω) (πb ω) = true ∧
      ¬ (E.Grounded (log ω) (wb ω) ∧
          S_inf.commit (wb ω) = cout ω ∧ S_cert.commit (wb ω) = cout' ω))
    (fun ω => (E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (wb ω) ∧
        S_inf.commit (out ω) = S_inf.commit (wb ω) ∧ out ω ≠ wb ω) ∨
      (E.Grounded (log ω) (wb ω) ∧ E.Grounded (log ω) (w ω) ∧
        S_cert.commit (wb ω) = S_cert.commit (w ω) ∧ wb ω ≠ w ω))
  have hu₂ := BindingGame.prob_or
    (fun ω => E.Grounded (log ω) (out ω) ∧ E.Grounded (log ω) (wb ω) ∧
      S_inf.commit (out ω) = S_inf.commit (wb ω) ∧ out ω ≠ wb ω)
    (fun ω => E.Grounded (log ω) (wb ω) ∧ E.Grounded (log ω) (w ω) ∧
      S_cert.commit (wb ω) = S_cert.commit (w ω) ∧ wb ω ≠ w ω)
  linarith

/-- Concrete witness inhabiting `cert_produced_weld` (`0 + 0 + 0 = 0`): deterministic model
`f (m, cin) := m :: cin` welded to a Tier-1 `SubstringAt` certificate at offset `0`. -/
theorem cert_produced_weld_ideal_witness :
    let S := idealContentScheme UInt8
    let V_inf : UInt8 → List UInt8 → List UInt8 → Unit → Bool :=
      fun m cin cout _ => decide (m :: cin = cout)
    ProducedSound (unrestrictedEnv UInt8) S (fun m cin out => out = m :: cin) V_inf (fun _ => 0) ∧
    ∃ ext_out : UInt8 → List UInt8 → List UInt8 → Unit → Unit → List UInt8,
      ∀ (q : ℕ) (m : Unit → UInt8) (cin cout cout' : Unit → List UInt8)
        (πi : Unit → Unit) (πc : Unit → Tier1Proof [42]) (_πb log : Unit → Unit),
        (unrestrictedEnv UInt8).ValidLog q log →
        BindingGame.prob (fun ω =>
          (V_inf (m ω) (cin ω) (cout ω) (πi ω) &&
           verifySubstringOpenings S (cout' ω) 0 [42] (πc ω).1 (πc ω).2.1 (πc ω).2.2 &&
           decide (cout ω = cout' ω)) = true ∧
          ¬ ((unrestrictedEnv UInt8).Grounded (log ω) (ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω)) ∧
              ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω) = m ω :: cin ω ∧
              SubstringAtPlain (ext_out (m ω) (cin ω) (cout ω) (πi ω) (log ω)) 0 [42]))
          ≤ (0 : ℝ) + 0 + S.bindAdv q := by
  have hprod : ProducedSound (unrestrictedEnv UInt8) (idealContentScheme UInt8)
      (fun m cin out => out = m :: cin)
      (fun m cin cout (_ : Unit) => decide (m :: cin = cout))
      (fun _ => 0) := by
    refine ⟨fun m cin _ _ _ => m :: cin, fun q m cin cout _ log _ => ?_⟩
    have hfalse : ∀ ω : (unrestrictedEnv UInt8).Coins q,
        ¬ (decide (m ω :: cin ω = cout ω) = true ∧
            ¬ ((unrestrictedEnv UInt8).Grounded (log ω) (m ω :: cin ω) ∧
                m ω :: cin ω = m ω :: cin ω ∧
                (idealContentScheme UInt8).commit (m ω :: cin ω) = cout ω)) := by
      intro ω ⟨hv, hbad⟩
      rw [decide_eq_true_eq] at hv
      exact hbad ⟨trivial, rfl, hv⟩
    rw [prob_eq_zero_of_false hfalse]
  exact ⟨hprod, cert_produced_weld hprod (tier1_substringAt_certSound 0 [42])
    (bridgeSound_same_scheme (idealContentScheme UInt8)
      (idealContentScheme_bindSound (unrestrictedEnv UInt8)))⟩

/-- **`P8` `TK` Collision Tooth (`tk_weld_collision_tooth`, `CERTIFICATES.md` §§3c, 5 `P8`)**:
When `c_out := TK window`, any certificate witness `w' ≠ window` committed to `c_out`
constructively exhibits a `TK` collision (`w' ≠ window ∧ TK w' = TK window`). Conversely, if `TK`
is injective on the pair (`TK w' = TK window → w' = window`), `w' ≠ window` is refused (`TK w' ≠ c_out`). -/
theorem tk_weld_collision_tooth {Sym TkDigest : Type}
    (TK : List Sym → TkDigest) {window w' : List Sym} {c_out : TkDigest}
    (hinf : TK window = c_out) (hcert : TK w' = c_out) (hne : w' ≠ window) :
    w' ≠ window ∧ TK w' = TK window :=
  ⟨hne, hcert.trans hinf.symm⟩

/-- **`P8` Non-Injective `TK` Falsifier (`tk_noninjective_weld_falsifier`)**:
If `TK` has a collision (modeled by prefix-truncating `TK w := w.take 1`), then an honest model
output `window = [0, 1]` (violating `φ w := (w = [0, 2])`) and an honest certificate for `w' = [0, 2]`
BOTH bind to `c_out = TK window = [0]`, yet `¬ φ window` — proving why the `L4` weld requires
`TK` collision resistance (`tkScheme.bindAdv`), an assumption FlashProve's standalone theorem omits. -/
def prefixTk (w : List UInt8) : List UInt8 := w.take 1

theorem tk_noninjective_weld_falsifier :
    let window : List UInt8 := [0, 1]
    let w' : List UInt8 := [0, 2]
    let φ : List UInt8 → Prop := fun w => w = [0, 2]
    let c_out := prefixTk window
    w' ≠ window ∧
    prefixTk window = c_out ∧
    prefixTk w' = c_out ∧
    φ w' ∧
    ¬ φ window := by
  refine ⟨by decide, rfl, by decide, rfl, by decide⟩

/-! ### `L5`: Transport Along a Content-Scheme Morphism (`cert_mapScheme`) -/

/-- Deterministic digest-level morphism `S → S'` (`∀ w, S'.commit w = mapDigest (S.commit w)`). -/
structure DetSchemeMorphism {Sym D Op D' Op' : Type}
    (S : ContentScheme Sym D Op) (S' : ContentScheme Sym D' Op') where
  mapDigest : D → D'
  commutes  : ∀ w : List Sym, S'.commit w = mapDigest (S.commit w)

/-- Deterministic morphism transport preserves `CertSound` with zero extra binding loss. -/
theorem cert_mapScheme_det {Sym D Op D' Op' Proof : Type} [DecidableEq D']
    {E : QueryEnv Sym}
    {S : ContentScheme Sym D Op} {S' : ContentScheme Sym D' Op'}
    (M : DetSchemeMorphism S S')
    {V : D → Proof → Bool} {φ : List Sym → Prop} {ε : ℕ → ℝ}
    (hs : CertSound E S V φ ε) :
    CertSound E S'
      (fun c' (π : D × Proof) => decide (M.mapDigest π.1 = c') && V π.1 π.2)
      φ ε := by
  rcases hs with ⟨ext, hprob⟩
  refine ⟨fun _ π l => ext π.1 π.2 l, ?_⟩
  intro q c' π log hlog
  have hsub : BindingGame.prob (fun ω =>
      (decide (M.mapDigest (π ω).1 = c' ω) && V (π ω).1 (π ω).2) = true ∧
        ¬ (E.Grounded (log ω) (ext (π ω).1 (π ω).2 (log ω)) ∧
            S'.commit (ext (π ω).1 (π ω).2 (log ω)) = c' ω ∧
            φ (ext (π ω).1 (π ω).2 (log ω)))) ≤
      BindingGame.prob (fun ω =>
        V (π ω).1 (π ω).2 = true ∧
          ¬ (E.Grounded (log ω) (ext (π ω).1 (π ω).2 (log ω)) ∧
              S.commit (ext (π ω).1 (π ω).2 (log ω)) = (π ω).1 ∧
              φ (ext (π ω).1 (π ω).2 (log ω)))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hacc, hfail⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at hacc
    refine ⟨hacc.2, fun ⟨hgr, hc, hp⟩ => hfail ⟨hgr, ?_, hp⟩⟩
    rw [M.commutes, hc, hacc.1]
  exact le_trans hsub (hprob q (fun ω => (π ω).1) (fun ω => (π ω).2) log hlog)

/-- **Computational Content-Scheme Morphism (`CERTIFICATES.md` §2 L5 & §3b)**:
a prover-computable link witness `verifyLink c c' π_mor` extracting a log-grounded word `w_m` that
opens both `S.commit w_m = c` and `S'.commit w_m = c'` with soundness error `ε_mor q`. -/
structure SchemeMorphism {Sym D Op D' Op' : Type}
    (E : QueryEnv Sym)
    (S : ContentScheme Sym D Op) (S' : ContentScheme Sym D' Op')
    (LinkProof : Type) (ε_mor : ℕ → ℝ) where
  verifyLink : D → D' → LinkProof → Bool
  extLink    : D → D' → LinkProof → E.Log → List Sym
  sound      : ∀ (q : ℕ) (c : E.Coins q → D) (c' : E.Coins q → D')
    (π : E.Coins q → LinkProof) (log : E.Coins q → E.Log),
    E.ValidLog q log →
    BindingGame.prob (fun ω =>
      verifyLink (c ω) (c' ω) (π ω) = true ∧
        ¬ (E.Grounded (log ω) (extLink (c ω) (c' ω) (π ω) (log ω)) ∧
            S.commit (extLink (c ω) (c' ω) (π ω) (log ω)) = c ω ∧
            S'.commit (extLink (c ω) (c' ω) (π ω) (log ω)) = c' ω))
      ≤ ε_mor q

/-- **`L5` Transport Along a Scheme Morphism (`cert_mapScheme`, `CERTIFICATES.md` §2 L5)**:
carries `CertSound E S V φ ε` into `CertSound E S'` at error `ε q + ε_mor q + S.bindAdv q`
(and bounded by `ε q + ε_mor q + S.bindAdv q + S'.bindAdv q`). -/
theorem cert_mapScheme {Sym D Op D' Op' Proof LinkProof : Type}
    {E : QueryEnv Sym}
    {S : ContentScheme Sym D Op} {S' : ContentScheme Sym D' Op'}
    {ε_mor : ℕ → ℝ} (M : SchemeMorphism E S S' LinkProof ε_mor)
    {V : D → Proof → Bool} {φ : List Sym → Prop} {ε : ℕ → ℝ}
    (hcert : CertSound E S V φ ε)
    (hbindS : BindSound E S) :
    CertSound E S'
      (fun c' (π : D × Proof × LinkProof) =>
        V π.1 π.2.1 && M.verifyLink π.1 c' π.2.2)
      φ (fun q => ε q + ε_mor q + S.bindAdv q + S'.bindAdv q) := by
  rcases hcert with ⟨ext, hs⟩
  refine ⟨fun _ π l => ext π.1 π.2.1 l, ?_⟩
  intro q c' π log hlog
  let w₁ : E.Coins q → List Sym := fun ω => ext (π ω).1 (π ω).2.1 (log ω)
  let wm : E.Coins q → List Sym := fun ω => M.extLink (π ω).1 (c' ω) (π ω).2.2 (log ω)
  have hb₁ := hs q (fun ω => (π ω).1) (fun ω => (π ω).2.1) log hlog
  have hbm := M.sound q (fun ω => (π ω).1) c' (fun ω => (π ω).2.2) log hlog
  have hbs := hbindS q log hlog w₁ wm
  have hbs' : 0 ≤ S'.bindAdv q := S'.bindAdv_nonneg q
  have hcov : BindingGame.prob (fun ω =>
      (V (π ω).1 (π ω).2.1 && M.verifyLink (π ω).1 (c' ω) (π ω).2.2) = true ∧
        ¬ (E.Grounded (log ω) (w₁ ω) ∧ S'.commit (w₁ ω) = c' ω ∧ φ (w₁ ω))) ≤
      BindingGame.prob (fun ω =>
        (V (π ω).1 (π ω).2.1 = true ∧
          ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω))) ∨
        ((M.verifyLink (π ω).1 (c' ω) (π ω).2.2 = true ∧
            ¬ (E.Grounded (log ω) (wm ω) ∧
                S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = c' ω)) ∨
          (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
            S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hacc, hfail⟩
    rw [Bool.and_eq_true] at hacc
    by_cases hg₁ : E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω)
    · by_cases hgm : E.Grounded (log ω) (wm ω) ∧ S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = c' ω
      · right; right
        refine ⟨hg₁.1, hgm.1, hg₁.2.1.trans hgm.2.1.symm,
          fun heq => hfail ⟨hg₁.1, heq ▸ hgm.2.2, hg₁.2.2⟩⟩
      · exact Or.inr (Or.inl ⟨hacc.2, hgm⟩)
    · exact Or.inl ⟨hacc.1, hg₁⟩
  have hu₁ := BindingGame.prob_or
    (fun ω => V (π ω).1 (π ω).2.1 = true ∧
      ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω)))
    (fun ω => (M.verifyLink (π ω).1 (c' ω) (π ω).2.2 = true ∧
        ¬ (E.Grounded (log ω) (wm ω) ∧ S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = c' ω)) ∨
      (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
        S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω))
  have hu₂ := BindingGame.prob_or
    (fun ω => M.verifyLink (π ω).1 (c' ω) (π ω).2.2 = true ∧
      ¬ (E.Grounded (log ω) (wm ω) ∧ S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = c' ω))
    (fun ω => E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
      S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω)
  linarith

/-- **`L5` Full Target-Word Attribution (`cert_mapScheme_attributed`)**:
when attributing transported `φ` to a concrete word `w_target` committed at `c' = S'.commit w_target`,
**both** `S.bindAdv q` and `S'.bindAdv q` enter: error `ε q + ε_mor q + S.bindAdv q + S'.bindAdv q`. -/
theorem cert_mapScheme_attributed {Sym D Op D' Op' Proof LinkProof : Type}
    {E : QueryEnv Sym}
    {S : ContentScheme Sym D Op} {S' : ContentScheme Sym D' Op'}
    {ε_mor : ℕ → ℝ} (M : SchemeMorphism E S S' LinkProof ε_mor)
    {V : D → Proof → Bool} {φ : List Sym → Prop} {ε : ℕ → ℝ}
    (hcert : CertSound E S V φ ε)
    (hbindS : BindSound E S)
    (hbindS' : BindSound E S')
    (q : ℕ) (w_target : E.Coins q → List Sym)
    (π : E.Coins q → D × Proof × LinkProof)
    (log : E.Coins q → E.Log)
    (hlog : E.ValidLog q log)
    (htgt : ∀ ω, E.Grounded (log ω) (w_target ω)) :
    BindingGame.prob (fun ω =>
      (V (π ω).1 (π ω).2.1 && M.verifyLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2) = true ∧
        ¬ φ (w_target ω))
      ≤ ε q + ε_mor q + S.bindAdv q + S'.bindAdv q := by
  rcases hcert with ⟨ext, hs⟩
  let w₁ : E.Coins q → List Sym := fun ω => ext (π ω).1 (π ω).2.1 (log ω)
  let wm : E.Coins q → List Sym := fun ω =>
    M.extLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2 (log ω)
  have hb₁ := hs q (fun ω => (π ω).1) (fun ω => (π ω).2.1) log hlog
  have hbm := M.sound q (fun ω => (π ω).1) (fun ω => S'.commit (w_target ω))
    (fun ω => (π ω).2.2) log hlog
  have hbs := hbindS q log hlog w₁ wm
  have hbs' := hbindS' q log hlog wm w_target
  have hcov : BindingGame.prob (fun ω =>
      (V (π ω).1 (π ω).2.1 && M.verifyLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2) = true ∧
        ¬ φ (w_target ω)) ≤
      BindingGame.prob (fun ω =>
        (V (π ω).1 (π ω).2.1 = true ∧
          ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω))) ∨
        ((M.verifyLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2 = true ∧
            ¬ (E.Grounded (log ω) (wm ω) ∧
                S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = S'.commit (w_target ω))) ∨
          ((E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
              S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω) ∨
            (E.Grounded (log ω) (wm ω) ∧ E.Grounded (log ω) (w_target ω) ∧
              S'.commit (wm ω) = S'.commit (w_target ω) ∧ wm ω ≠ w_target ω)))) := by
    apply BindingGame.prob_mono
    intro ω ⟨hacc, hfail⟩
    rw [Bool.and_eq_true] at hacc
    by_cases hg₁ : E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω)
    · by_cases hgm : E.Grounded (log ω) (wm ω) ∧
          S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = S'.commit (w_target ω)
      · by_cases heq1 : w₁ ω = wm ω
        · by_cases heq2 : wm ω = w_target ω
          · exact False.elim (hfail (heq2 ▸ heq1 ▸ hg₁.2.2))
          · right; right; right
            exact ⟨hgm.1, htgt ω, hgm.2.2, heq2⟩
        · right; right; left
          exact ⟨hg₁.1, hgm.1, hg₁.2.1.trans hgm.2.1.symm, heq1⟩
      · exact Or.inr (Or.inl ⟨hacc.2, hgm⟩)
    · exact Or.inl ⟨hacc.1, hg₁⟩
  have hu₁ := BindingGame.prob_or
    (fun ω => V (π ω).1 (π ω).2.1 = true ∧
      ¬ (E.Grounded (log ω) (w₁ ω) ∧ S.commit (w₁ ω) = (π ω).1 ∧ φ (w₁ ω)))
    (fun ω => (M.verifyLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2 = true ∧
        ¬ (E.Grounded (log ω) (wm ω) ∧
            S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = S'.commit (w_target ω))) ∨
      ((E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
          S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω) ∨
        (E.Grounded (log ω) (wm ω) ∧ E.Grounded (log ω) (w_target ω) ∧
          S'.commit (wm ω) = S'.commit (w_target ω) ∧ wm ω ≠ w_target ω)))
  have hu₂ := BindingGame.prob_or
    (fun ω => M.verifyLink (π ω).1 (S'.commit (w_target ω)) (π ω).2.2 = true ∧
      ¬ (E.Grounded (log ω) (wm ω) ∧
          S.commit (wm ω) = (π ω).1 ∧ S'.commit (wm ω) = S'.commit (w_target ω)))
    (fun ω => (E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
        S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω) ∨
      (E.Grounded (log ω) (wm ω) ∧ E.Grounded (log ω) (w_target ω) ∧
        S'.commit (wm ω) = S'.commit (w_target ω) ∧ wm ω ≠ w_target ω))
  have hu₃ := BindingGame.prob_or
    (fun ω => E.Grounded (log ω) (w₁ ω) ∧ E.Grounded (log ω) (wm ω) ∧
      S.commit (w₁ ω) = S.commit (wm ω) ∧ w₁ ω ≠ wm ω)
    (fun ω => E.Grounded (log ω) (wm ω) ∧ E.Grounded (log ω) (w_target ω) ∧
      S'.commit (wm ω) = S'.commit (w_target ω) ∧ wm ω ≠ w_target ω)
  linarith

/-- **`L5` Both-Sides `bindAdv` Necessity Tooth (`cert_mapScheme_both_bindAdv_necessary`)**:
1. Source-side break (`S = parityScheme`, `S' = idealContentScheme`): `[1, 1]` bridges exactly to
   `c = 0`, where `parityV0` certifies `φ₀ ([0, 0])` at `ε = 0, ε_mor = 0, S'.bindAdv = 0`, yet
   `¬ φ₀ [1, 1]` — `S.bindAdv` cannot be dropped;
2. Target-side break (`S = idealContentScheme`, `S' = parityScheme`): `[0, 0]` is certified under
   `S` (`ε = 0, S.bindAdv = 0`) and bridges exactly (`ε_mor = 0`) to `S'.commit [1, 1] = 0`, yet
   `¬ φ₀ [1, 1]` — `S'.bindAdv` cannot be dropped! -/
theorem cert_mapScheme_both_bindAdv_necessary :
    let w_good : List (ZMod 2) := [0, 0]
    let w_target : List (ZMod 2) := [1, 1]
    -- (1) Source-side collision (S = parityScheme, S' = ideal):
    (parityV0 (parityScheme.commit w_target) () = true ∧
      (idealContentScheme (ZMod 2)).commit w_target = w_target ∧
      ¬ parityPhi0 w_target) ∧
    -- (2) Target-side collision (S = ideal, S' = parityScheme):
    ((idealContentScheme (ZMod 2)).commit w_good = w_good ∧
      parityPhi0 w_good ∧
      parityScheme.commit w_good = parityScheme.commit w_target ∧
      ¬ parityPhi0 w_target) :=
  ⟨⟨by decide, rfl, by decide⟩, ⟨rfl, rfl, by decide, by decide⟩⟩

/-! ### Bridge to `Pred/Core.lean`: Third-Party `.witnessed vk` Policy Discharge -/

/-- Connects `Pred.evalWith` (`Pred/Core.lean:339`) on `.witnessed vk` to `CertSound`:
when an external discharge oracle `O : Pred.Oracle` verifies a certificate `V` against the state's
projected digest `projDigest new` and side-channel proof `projProof new`, `Pred.evalWith` inherits
`CertSound` while keeping `Pred` 100% first-order syntactic. -/
theorem pred_witnessed_certificate_sound {Sym Digest Op Proof : Type}
    {E : QueryEnv Sym} {S : ContentScheme Sym Digest Op}
    {V : Digest → Proof → Bool} {φ : List Sym → Prop} {ε : ℕ → ℝ}
    (hs : CertSound E S V φ ε)
    (vk : Pred.Vk)
    (projDigest : Pred.State → Digest)
    (projProof : Pred.State → Proof) :
    ∃ ext : Pred.State → E.Log → List Sym,
      ∀ (q : ℕ) (old new : E.Coins q → Pred.State) (log : E.Coins q → E.Log),
        E.ValidLog q log →
        let O : Pred.Oracle := fun vk' _ st =>
          decide (vk' = vk) && V (projDigest st) (projProof st)
        BindingGame.prob (fun ω =>
          Pred.evalWith O (.witnessed vk) (old ω) (new ω) = true ∧
            ¬ (E.Grounded (log ω) (ext (new ω) (log ω)) ∧
                S.commit (ext (new ω) (log ω)) = projDigest (new ω) ∧
                φ (ext (new ω) (log ω))))
          ≤ ε q := by
  rcases hs with ⟨ext, hprob⟩
  refine ⟨fun st l => ext (projDigest st) (projProof st) l, ?_⟩
  intro q old new log hlog O
  have hsub : BindingGame.prob (fun ω =>
      Pred.evalWith O (.witnessed vk) (old ω) (new ω) = true ∧
        ¬ (E.Grounded (log ω) (ext (projDigest (new ω)) (projProof (new ω)) (log ω)) ∧
            S.commit (ext (projDigest (new ω)) (projProof (new ω)) (log ω)) = projDigest (new ω) ∧
            φ (ext (projDigest (new ω)) (projProof (new ω)) (log ω)))) ≤
      BindingGame.prob (fun ω =>
        V (projDigest (new ω)) (projProof (new ω)) = true ∧
          ¬ (E.Grounded (log ω) (ext (projDigest (new ω)) (projProof (new ω)) (log ω)) ∧
              S.commit (ext (projDigest (new ω)) (projProof (new ω)) (log ω)) = projDigest (new ω) ∧
              φ (ext (projDigest (new ω)) (projProof (new ω)) (log ω)))) := by
    apply BindingGame.prob_mono
    intro ω ⟨heval, hbad⟩
    simp only [Pred.evalWith, O, decide_true, Bool.true_and] at heval
    exact ⟨heval, hbad⟩
  exact le_trans hsub (hprob q (fun ω => projDigest (new ω)) (fun ω => projProof (new ω)) log hlog)

/-! ## §6. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.CertificateComposition.idealContentScheme_bindSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms idealContentScheme_bindSound
/-- info: 'Minidregg.Assurance.CertificateComposition.parityHalfScheme_bindSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parityHalfScheme_bindSound
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_and
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_and_ideal_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_and_ideal_witness
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_and_fractional_compressing_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_and_fractional_compressing_witness
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_and_dropping_bindAdv_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_and_dropping_bindAdv_false
/-- info: 'Minidregg.Assurance.CertificateComposition.dfa_verify_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms dfa_verify_sound
/-- info: 'Minidregg.Assurance.CertificateComposition.dfa_bound_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfa_bound_sound
/-- info: 'Minidregg.Assurance.CertificateComposition.boundDfaKernel_certSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundDfaKernel_certSound
/-- info: 'Minidregg.Assurance.CertificateComposition.unbound_dfa_splice_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unbound_dfa_splice_falsifier
/-- info: 'Minidregg.Assurance.CertificateComposition.prob_exists_fin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prob_exists_fin_le
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_allRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_allRecords
/-- info: 'Minidregg.Assurance.CertificateComposition.compressingUnitMmr_bindSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressingUnitMmr_bindSound
/-- info: 'Minidregg.Assurance.CertificateComposition.digest8_lane0_splice_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms digest8_lane0_splice_falsifier
/-- info: 'Minidregg.Assurance.CertificateComposition.oneFelt_wraparound_breaks_allRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms oneFelt_wraparound_breaks_allRecords
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_produced_weld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_produced_weld
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_produced_weld_ideal_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_produced_weld_ideal_witness
/-- info: 'Minidregg.Assurance.CertificateComposition.bridgeSound_same_scheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bridgeSound_same_scheme
/-- info: 'Minidregg.Assurance.CertificateComposition.bridgeSound_of_dual_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bridgeSound_of_dual_cert
/-- info: 'Minidregg.Assurance.CertificateComposition.tk_weld_collision_tooth' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tk_weld_collision_tooth
/-- info: 'Minidregg.Assurance.CertificateComposition.tk_noninjective_weld_falsifier' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tk_noninjective_weld_falsifier
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_mapScheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_mapScheme
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_mapScheme_attributed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_mapScheme_attributed
/-- info: 'Minidregg.Assurance.CertificateComposition.cert_mapScheme_both_bindAdv_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_mapScheme_both_bindAdv_necessary
/-- info: 'Minidregg.Assurance.CertificateComposition.pred_witnessed_certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pred_witnessed_certificate_sound

end Minidregg.Assurance.CertificateComposition
