/-
# Assurance.UnlearningExact — exact deletion for a sufficient-statistics learner (C18/C19), with absence.

The dark-learning program's C18 learner keeps the statistics of its LIVE records, `state = Σ contrib r`, over a
committed log whose positions never move: a slot holds a live record or a tombstone. A deletion request names a
record `r`; the ledger accepts a certificate when four LOG legs hold over the opened logs `L` (before) and `L'`
(after) and the positions `P` the certificate names,

* `opened` — every position in `P` opens to `r` in `L`;
* `tomb`   — every position in `P` is a tombstone in `L'`;
* `frame`  — every other position is unchanged;
* `absent` — `r` occurs nowhere in `L'` (the absence protocol's whole-log `Count = 0`),

and one STATE leg, `S' = S - |P| • contrib r`, computed by the verifier itself from `r`'s bytes.

* `delete_exact` — the log legs force `L' = eraseAll r L` (every copy tombstoned, nothing else touched), and the
  state leg holds IFF `S'` is the fold over `L'`: the certificate verifies exactly when the new state is the
  learner's state on the remaining records.
* `delete_absence` — composed with `Count = 0`: the live multiset after is `(live L).filter (· ≠ r)`, `r` is not in
  it, and the accepted state is the fold over it. `influence_gone`: the accepted state is unchanged by ANY
  re-definition of `r`'s contribution (a statement about the state, not about what the log discloses).
* `history_independent` / `deleted_equals_never_trained` — the state is a function of the live multiset, so a log
  that was trained on `r` and then deleted it and a log that never held `r` (any length, any order) have EQUAL
  states. The state must not distinguish them; the log does (its tombstones).
* `release_unique` — the release check `(λ I + A) N = δ B` with `A = Σ φ φᵀ`, `λ > 0` and `δ ≠ 0` determines the
  model `N / δ` uniquely (`release_cross` is the cross-multiplied form, trivial at `δ = 0`), so an accepted release after deletion IS the release the learner computes from scratch on
  the remaining records (`deleted_release_is_retrained`).

Binding legs are NOT re-proved here: the opened logs are the committed ones by the MMR's binding
(`mroot_binds_or_collides`, breadstuffs `MMR.lean`) and records are identified by a collision-resistant content
key. The release is stated over `ℚ`; the harness checks it over `ℤ`, which embeds.

**Teeth** (`UnlearningTeeth`): drop `absent` (a duplicate deleted once), `frame` (a second record removed too),
or `opened` (more positions claimed than copies) and the conclusion is FALSE on a two- or three-slot log; drop
`λ > 0` and two different models pass the release check. `legs_inhabited` gives an honest instance.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

namespace Minidregg.Assurance.Unlearning

open Finset

set_option linter.unusedSectionVars false

variable {R S : Type} [DecidableEq R] [AddCommGroup S]

/-- A committed log of `n` positions: a live record or a tombstone (`none`). Positions never move. -/
abbrev Log (R : Type) (n : ℕ) := Fin n → Option R

/-- One slot's contribution: a tombstone contributes nothing. -/
def slotVal (contrib : R → S) : Option R → S
  | none => 0
  | some r => contrib r

/-- The learner state: the fold of the live records' contributions. -/
def state (contrib : R → S) {n : ℕ} (L : Log R n) : S := ∑ j, slotVal contrib (L j)

/-- The live multiset of a log. -/
def live {n : ℕ} (L : Log R n) : Multiset R := ((Finset.univ : Finset (Fin n)).val.map L).filterMap id

/-- How many live slots hold `r` (the absence protocol's Count over the content key of `r`). -/
def count {n : ℕ} (L : Log R n) (r : R) : ℕ := (univ.filter (fun j => L j = some r)).card

/-- The log with every copy of `r` tombstoned and nothing else changed. -/
def eraseAll {n : ℕ} (r : R) (L : Log R n) : Log R n := fun j => if L j = some r then none else L j

/-- The four log legs of an accepted delete certificate, over the opened logs. -/
structure DeleteLegs {n : ℕ} (L L' : Log R n) (r : R) (P : Finset (Fin n)) : Prop where
  opened : ∀ j ∈ P, L j = some r
  tomb : ∀ j ∈ P, L' j = none
  frame : ∀ j, j ∉ P → L' j = L j
  absent : count L' r = 0

lemma not_some_of_count_zero {n : ℕ} {L : Log R n} {r : R} (h : count L r = 0) (j : Fin n) :
    L j ≠ some r := by
  intro hj
  have : j ∈ univ.filter (fun j => L j = some r) := by simp [hj]
  have hpos := Finset.card_pos.mpr ⟨j, this⟩
  unfold count at h
  omega

/-- The log legs pin the new log and the positions. -/
theorem legs_pin {n : ℕ} {L L' : Log R n} {r : R} {P : Finset (Fin n)} (h : DeleteLegs L L' r P) :
    L' = eraseAll r L ∧ P = univ.filter (fun j => L j = some r) := by
  have hnot := not_some_of_count_zero h.absent
  constructor
  · funext j
    unfold eraseAll
    by_cases hj : j ∈ P
    · simp [h.tomb j hj, h.opened j hj]
    · have hf := h.frame j hj
      have : L j ≠ some r := fun hL => hnot j (hf.trans hL)
      simp [hf, this]
  · ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact h.opened j
    · intro hL
      by_contra hj
      exact hnot j ((h.frame j hj).trans hL)

lemma state_eq_eraseAll_add (contrib : R → S) {n : ℕ} (L : Log R n) (r : R) :
    state contrib L = state contrib (eraseAll r L) + (count L r) • contrib r := by
  have hsplit : ∀ j, slotVal contrib (L j)
      = slotVal contrib (eraseAll r L j) + (if L j = some r then contrib r else 0) := by
    intro j
    unfold eraseAll
    by_cases h : L j = some r
    · simp [h, slotVal]
    · simp [h]
  unfold state count
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.sum_const]

/-- **`delete_exact`.** Given the invariant (the ledger's state is the fold of the old log) and the four log legs,
the new log is the old one with every copy of `r` tombstoned, and the state leg holds IFF the claimed new state is
the fold of the new log. -/
theorem delete_exact (contrib : R → S) {n : ℕ} {L L' : Log R n} {r : R} {P : Finset (Fin n)} {S₀ S' : S}
    (hinv : S₀ = state contrib L) (hlegs : DeleteLegs L L' r P) :
    L' = eraseAll r L ∧ (S' = S₀ - P.card • contrib r ↔ S' = state contrib L') := by
  obtain ⟨hL', hP⟩ := legs_pin hlegs
  refine ⟨hL', ?_⟩
  have hc : P.card = count L r := by rw [hP]; rfl
  have key : S₀ - P.card • contrib r = state contrib L' := by
    rw [hinv, hc, state_eq_eraseAll_add contrib L r, hL', add_sub_cancel_right]
  rw [key]

lemma filterMap_sum (contrib : R → S) (m : Multiset (Option R)) :
    ((m.filterMap id).map contrib).sum = (m.map (slotVal contrib)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    cases a with
    | none => simp [Multiset.filterMap_cons_none, slotVal, ih]
    | some x => simp [Multiset.filterMap_cons_some, slotVal, ih]

/-- The state is the fold of the live multiset. -/
theorem state_eq_live (contrib : R → S) {n : ℕ} (L : Log R n) :
    state contrib L = ((live L).map contrib).sum := by
  unfold state live
  rw [filterMap_sum, Multiset.map_map]
  rfl

/-- **History independence.** Two logs (of any lengths) with the same live multiset have the same state. -/
theorem history_independent (contrib : R → S) {n m : ℕ} (L₁ : Log R n) (L₂ : Log R m)
    (h : live L₁ = live L₂) : state contrib L₁ = state contrib L₂ := by
  rw [state_eq_live, state_eq_live, h]

lemma filterMap_erase (r : R) (m : Multiset (Option R)) :
    (m.map (fun o => if o = some r then none else o)).filterMap id = (m.filterMap id).filter (· ≠ r) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    cases a with
    | none => simp [Multiset.filterMap_cons_none, ih]
    | some x =>
      by_cases hx : x = r
      · subst hx; simp [Multiset.filterMap_cons_some, ih]
      · have : (some x = some r) = False := by simp [hx]
        simp [Multiset.filterMap_cons_some, ih, hx, Multiset.filter_cons_of_pos]

theorem live_eraseAll {n : ℕ} (r : R) (L : Log R n) : live (eraseAll r L) = (live L).filter (· ≠ r) := by
  unfold live
  rw [← filterMap_erase, Multiset.map_map]
  rfl

/-- **`delete_absence`.** An accepted deletion (log legs + state leg) leaves a live multiset that is the old one
without `r`, contains no `r` (the absence protocol's `Count = 0`, as a multiset fact), and the accepted state is
the fold over it. -/
theorem delete_absence (contrib : R → S) {n : ℕ} {L L' : Log R n} {r : R} {P : Finset (Fin n)} {S₀ S' : S}
    (hinv : S₀ = state contrib L) (hlegs : DeleteLegs L L' r P) (hstate : S' = S₀ - P.card • contrib r) :
    live L' = (live L).filter (· ≠ r) ∧ r ∉ live L' ∧
      S' = (((live L).filter (· ≠ r)).map contrib).sum := by
  obtain ⟨hL', hiff⟩ := delete_exact contrib hinv hlegs (S' := S')
  have hlive : live L' = (live L).filter (· ≠ r) := by rw [hL', live_eraseAll]
  refine ⟨hlive, ?_, ?_⟩
  · rw [hlive]; simp
  · rw [hiff.mp hstate, state_eq_live, hlive]

/-- **Contribution-map invariance.** The accepted state is the same under any contribution map that agrees with
`contrib` away from `r`: the state is not a function of `r`'s contribution. (This is a statement about the
STATE; what an observer can infer from the log, the certificates or earlier releases is outside it.) -/
theorem influence_gone (contrib contrib' : R → S) {n : ℕ} {L L' : Log R n} {r : R} {P : Finset (Fin n)}
    {S₀ S' : S} (hinv : S₀ = state contrib L) (hlegs : DeleteLegs L L' r P)
    (hstate : S' = S₀ - P.card • contrib r) (hagree : ∀ x, x ≠ r → contrib' x = contrib x) :
    S' = state contrib' L' := by
  obtain ⟨hL', hiff⟩ := delete_exact contrib hinv hlegs (S' := S')
  rw [hiff.mp hstate]
  unfold state
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hnot := not_some_of_count_zero hlegs.absent j
  cases hj : L' j with
  | none => rfl
  | some x =>
    have hx : x ≠ r := fun h => hnot (by rw [hj, h])
    simp [slotVal, hagree x hx]

/-- **Trained-then-deleted equals never-trained.** Any log `L₀` (any length, any order) whose live records are the
old ones without `r` has exactly the accepted post-deletion state. -/
theorem deleted_equals_never_trained (contrib : R → S) {n m : ℕ} {L L' : Log R n} {r : R}
    {P : Finset (Fin n)} {S₀ S' : S} (hinv : S₀ = state contrib L) (hlegs : DeleteLegs L L' r P)
    (hstate : S' = S₀ - P.card • contrib r) (L₀ : Log R m) (hnever : live L₀ = (live L).filter (· ≠ r)) :
    S' = state contrib L₀ := by
  rw [(delete_absence contrib hinv hlegs hstate).2.2, state_eq_live, hnever]

/-! ## The release: `λ > 0` makes it unique -/

section Release

open Matrix

variable {ι : Type} [Fintype ι] {d c : ℕ}

lemma quad_form (a x : Fin d → ℚ) : x ⬝ᵥ (vecMulVec a a *ᵥ x) = (a ⬝ᵥ x) * (a ⬝ᵥ x) := by
  have h : vecMulVec a a *ᵥ x = (a ⬝ᵥ x) • a := by
    funext i
    simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [h, dotProduct_smul, smul_eq_mul, dotProduct_comm x a]

/-- `λ I + Σ v vᵀ` with `λ > 0` is injective on vectors (positive definite). -/
theorem gram_injective (v : ι → Fin d → ℚ) {lam : ℚ} (hlam : 0 < lam) (x : Fin d → ℚ)
    (hx : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) *ᵥ x = 0) : x = 0 := by
  have hq : x ⬝ᵥ ((lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) *ᵥ x)
      = lam * (x ⬝ᵥ x) + ∑ k, (v k ⬝ᵥ x) * (v k ⬝ᵥ x) := by
    rw [add_mulVec, smul_mulVec, one_mulVec, sum_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_sum, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => quad_form (v k) x)
  rw [hx, dotProduct_zero] at hq
  have hsq : 0 ≤ ∑ k, (v k ⬝ᵥ x) * (v k ⬝ᵥ x) :=
    Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have : x ⬝ᵥ x = 0 := by nlinarith
  exact dotProduct_self_eq_zero.mp this

/-- Cross-multiplied form: two releases passing the check satisfy `δ₂ N₁ = δ₁ N₂`. (With `δ = 0` this is
trivial; the quotient statement below needs nonzero denominators.) -/
theorem release_cross (v : ι → Fin d → ℚ) {lam : ℚ} (hlam : 0 < lam) (B N₁ N₂ : Matrix (Fin d) (Fin c) ℚ)
    (δ₁ δ₂ : ℚ)
    (h₁ : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) * N₁ = δ₁ • B)
    (h₂ : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) * N₂ = δ₂ • B) :
    δ₂ • N₁ = δ₁ • N₂ := by
  have hzero : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) * (δ₂ • N₁ - δ₁ • N₂)
      = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h₁, h₂, smul_smul, smul_smul, mul_comm, sub_self]
  rw [← sub_eq_zero]
  ext i j
  have hcol := gram_injective v hlam (fun i => (δ₂ • N₁ - δ₁ • N₂) i j) (by
    funext a
    have h1 := congrFun (congrFun hzero a) j
    rw [Matrix.mul_apply] at h1
    simpa only [mulVec, dotProduct, Pi.zero_apply, Matrix.zero_apply] using h1)
  simpa using congrFun hcol i

/-- **`release_unique`.** Two releases with NONZERO denominators that both pass the check
`(λ I + A) N = δ B`, `A = Σ v vᵀ`, `λ > 0`, are the same model: `N₁ / δ₁ = N₂ / δ₂`. (The harness requires
`δ > 0`; `(N, δ) = (0, 0)` passes the bare check and is refused there, and excluded here by `hδ`.) -/
theorem release_unique (v : ι → Fin d → ℚ) {lam : ℚ} (hlam : 0 < lam) (B N₁ N₂ : Matrix (Fin d) (Fin c) ℚ)
    {δ₁ δ₂ : ℚ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0)
    (h₁ : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) * N₁ = δ₁ • B)
    (h₂ : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + ∑ k, vecMulVec (v k) (v k)) * N₂ = δ₂ • B) :
    δ₁⁻¹ • N₁ = δ₂⁻¹ • N₂ := by
  have hx := release_cross v hlam B N₁ N₂ δ₁ δ₂ h₁ h₂
  have := congrArg (fun M => (δ₁⁻¹ * δ₂⁻¹) • M) hx
  simp only [smul_smul] at this
  rwa [show δ₁⁻¹ * δ₂⁻¹ * δ₂ = δ₁⁻¹ by field_simp, show δ₁⁻¹ * δ₂⁻¹ * δ₁ = δ₂⁻¹ by field_simp] at this

/-- The C18 contribution of a record: `(φ φᵀ, φ yᵀ)`. -/
def contribM (φ : R → Fin d → ℚ) (yv : R → Fin c → ℚ) (r : R) :
    Matrix (Fin d) (Fin d) ℚ × Matrix (Fin d) (Fin c) ℚ :=
  (vecMulVec (φ r) (φ r), vecMulVec (φ r) (yv r))

/-- A slot's feature vector (zero for a tombstone). -/
def slotVec (φ : R → Fin d → ℚ) {n : ℕ} (L : Log R n) (j : Fin n) : Fin d → ℚ := (L j).elim 0 φ

lemma gram_state (φ : R → Fin d → ℚ) (yv : R → Fin c → ℚ) {n : ℕ} (L : Log R n) :
    (state (contribM φ yv) L).1 = ∑ j, vecMulVec (slotVec φ L j) (slotVec φ L j) := by
  unfold state
  rw [Prod.fst_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold slotVec
  cases L j with
  | none => ext a b; simp [slotVal, vecMulVec]
  | some x => rfl

/-- **The accepted release after a deletion is the retrained release.** If the deletion was accepted and a release
`(N, δ)` passes the check against the post-deletion state, and `(N₀, δ₀)` is the learner's own release on ANY log
`L₀` that never held `r` (same remaining records), both with nonzero denominators, then `N / δ = N₀ / δ₀`. -/
theorem deleted_release_is_retrained (φ : R → Fin d → ℚ) (yv : R → Fin c → ℚ) {lam : ℚ} (hlam : 0 < lam)
    {n m : ℕ} {L L' : Log R n} {r : R} {P : Finset (Fin n)}
    {S₀ S' : Matrix (Fin d) (Fin d) ℚ × Matrix (Fin d) (Fin c) ℚ}
    (hinv : S₀ = state (contribM φ yv) L) (hlegs : DeleteLegs L L' r P)
    (hstate : S' = S₀ - P.card • contribM φ yv r)
    (N : Matrix (Fin d) (Fin c) ℚ) (δ : ℚ) (hrel : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + S'.1) * N = δ • S'.2)
    (L₀ : Log R m) (hnever : live L₀ = (live L).filter (· ≠ r)) (N₀ : Matrix (Fin d) (Fin c) ℚ) (δ₀ : ℚ)
    (hrel₀ : (lam • (1 : Matrix (Fin d) (Fin d) ℚ) + (state (contribM φ yv) L₀).1) * N₀
      = δ₀ • (state (contribM φ yv) L₀).2) (hδ : δ ≠ 0) (hδ₀ : δ₀ ≠ 0) :
    δ⁻¹ • N = δ₀⁻¹ • N₀ := by
  have hS : S' = state (contribM φ yv) L₀ :=
    deleted_equals_never_trained (contribM φ yv) hinv hlegs hstate L₀ hnever
  rw [hS, gram_state] at hrel
  rw [gram_state] at hrel₀
  exact release_unique (slotVec φ L₀) hlam _ N N₀ hδ hδ₀ hrel hrel₀

end Release

/-! ## Teeth -/

namespace UnlearningTeeth

/-- Contributions into `ℤ`: record `0` weighs 1, every other record 10. -/
def w : ℕ → ℤ := fun x => if x = 0 then 1 else 10

/-- **Without `absent` the conclusion is false**: a duplicate deleted once. Two copies of `0`; one position
tombstoned; `opened`, `tomb`, `frame` hold and the state leg is honest, yet the claimed state (1) is not the
never-trained state (0). -/
theorem false_without_absent :
    ¬ ∀ (L L' : Log ℕ 2) (r : ℕ) (P : Finset (Fin 2)) (S₀ S' : ℤ),
      S₀ = state w L → (∀ j ∈ P, L j = some r) → (∀ j ∈ P, L' j = none) → (∀ j, j ∉ P → L' j = L j) →
      S' = S₀ - P.card • w r → S' = state w (eraseAll r L) := by
  intro h
  have := h ![some 0, some 0] ![none, some 0] 0 {0} 2 1 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  revert this
  decide

/-- **Without `frame` the conclusion is false**: a second record removed too. `L' = [∅, ∅]` from `[0, 1]`;
`opened`, `tomb`, `absent` hold, the state leg is honest (`S' = 11 − 1 = 10`), yet the new log is not `eraseAll`
and the state does not fold it (its fold is 0). -/
theorem false_without_frame :
    ¬ ∀ (L L' : Log ℕ 2) (r : ℕ) (P : Finset (Fin 2)) (S₀ S' : ℤ),
      S₀ = state w L → (∀ j ∈ P, L j = some r) → (∀ j ∈ P, L' j = none) → count L' r = 0 →
      S' = S₀ - P.card • w r → S' = state w L' := by
  intro h
  have := h ![some 0, some 1] ![none, none] 0 {0} 11 10 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  revert this
  decide

/-- **Without `opened` the conclusion is false**: more positions claimed than copies. One copy of `0`, two
positions claimed; the state leg subtracts twice (`S' = 11 − 2 = 9`), the never-trained state is 10. -/
theorem false_without_opened :
    ¬ ∀ (L L' : Log ℕ 2) (r : ℕ) (P : Finset (Fin 2)) (S₀ S' : ℤ),
      S₀ = state w L → (∀ j ∈ P, L' j = none) → (∀ j, j ∉ P → L' j = L j) → count L' r = 0 →
      S' = S₀ - P.card • w r → S' = state w (eraseAll r L) := by
  intro h
  have := h ![some 0, some 1] ![none, none] 0 {0, 1} 11 9 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  revert this
  decide

/-- **The premise is inhabited**: an honest deletion of both copies of `0` from `[0, 1, 0]`. -/
theorem legs_inhabited :
    DeleteLegs (![some 0, some 1, some 0] : Log ℕ 3) ![none, some 1, none] 0 {0, 2} where
  opened := by decide
  tomb := by decide
  frame := by decide
  absent := by decide

/-- …and it fires: the accepted state is the never-trained state `w 1 = 10`. -/
theorem legs_fire : (12 : ℤ) - (({0, 2} : Finset (Fin 3)).card • w 0) = state w (![none, some 1] : Log ℕ 2) := by
  decide

/-- **Without `λ > 0` uniqueness is false**, even with nonzero denominators: with no data and `λ = 0` the check is
`0 = δ B` with `B = 0`, and `N = 0`, `N = 1` both pass with `δ = 1`. -/
theorem release_false_without_lam :
    ¬ ∀ (B N₁ N₂ : Matrix (Fin 1) (Fin 1) ℚ) (δ₁ δ₂ : ℚ), δ₁ ≠ 0 → δ₂ ≠ 0 →
      ((0 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) + ∑ k : Fin 0, Matrix.vecMulVec (Fin.elim0 k) (Fin.elim0 k)) * N₁
          = δ₁ • B →
      ((0 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) + ∑ k : Fin 0, Matrix.vecMulVec (Fin.elim0 k) (Fin.elim0 k)) * N₂
          = δ₂ • B →
      δ₁⁻¹ • N₁ = δ₂⁻¹ • N₂ := by
  intro h
  have := h 0 0 1 1 1 one_ne_zero one_ne_zero (by simp) (by simp)
  have h00 := congrFun (congrFun this 0) 0
  simp at h00

end UnlearningTeeth

/-- info: 'Minidregg.Assurance.Unlearning.delete_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_exact
/-- info: 'Minidregg.Assurance.Unlearning.delete_absence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_absence
/-- info: 'Minidregg.Assurance.Unlearning.influence_gone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms influence_gone
/-- info: 'Minidregg.Assurance.Unlearning.deleted_equals_never_trained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deleted_equals_never_trained
/-- info: 'Minidregg.Assurance.Unlearning.release_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms release_unique
/-- info: 'Minidregg.Assurance.Unlearning.release_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms release_cross
/-- info: 'Minidregg.Assurance.Unlearning.deleted_release_is_retrained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deleted_release_is_retrained
/-- info: 'Minidregg.Assurance.Unlearning.UnlearningTeeth.false_without_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningTeeth.false_without_absent

/-- info: 'Minidregg.Assurance.Unlearning.UnlearningTeeth.false_without_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningTeeth.false_without_frame

/-- info: 'Minidregg.Assurance.Unlearning.UnlearningTeeth.false_without_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningTeeth.false_without_opened

/-- info: 'Minidregg.Assurance.Unlearning.UnlearningTeeth.release_false_without_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningTeeth.release_false_without_lam

/-- info: 'Minidregg.Assurance.Unlearning.UnlearningTeeth.legs_fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UnlearningTeeth.legs_fire

end Minidregg.Assurance.Unlearning
