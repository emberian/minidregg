/-
# `Theory.Char2Degree4SumcheckHvzk` — characteristic-2 degree-≤4 sumcheck and degree-2
# BaseFold round-polynomial HVZK (gate `G8 / #125`)

Scope: **round polynomials only**, honest verifier with fixed challenges, coefficient level.
The terminal opening of the mask columns at `r` (handled by the half-cube blinding of
`Compiler/Tower256AlgebraicCert.lean`) is out of scope here.

## Statements (all over `[Field F] [CharP F 2]` unless marked)

1. **Teeth.**
   * `charTwo_affine_cubeSum_eq_zero`: every *affine* (total-degree-1) mask
     `a₀ + ∑ₖ aₖ xₖ` sums to `0` on `{0,1}^m` for `m ≥ 2`, so the round-0 claim leaks
     (`charTwo_affine_mask_round0_leaks`). The `m ≥ 2` guard is load-bearing
     (`ell1_affine_cubeSum_eq_one`) and the statement is false for *multilinear* masks
     (`multilinear_x0x1_cubeSum_eq_one`: `∑ x₀x₁ = 1`).
   * `bitVal_sq_add_self`, `bitVal_cube_add_sq`: `x² + x` and `x³ + x²` vanish on `{0,1}`.
   * `z2_constant_term_degree_le_two`: a lone `Z₂ · u` term with `u` constant in `X` has
     `c₃ = c₄ = 0`; `threeColumn_c4_eq_zero` / `threeColumn_transcripts_separate`: without the
     `Z₃` column, `c₄` of every masked round polynomial equals the honest `c₄` (support-disjoint
     transcripts, `zmod2_threeColumn_distinguisher` is a kernel-checked instance).
2. **Per-round algebra.** `peval_zero_add_one_five`: `p(0)+p(1) = c₁+c₂+c₃+c₄` (so `c₀` is free;
   `zmod3_c0_not_free` shows `CharP F 2` is load-bearing). `roundPartialSum_eq` derives the
   round-`j` coefficient vector `roundMaskCoeffs` of the 4-column mask
   `m_lin + P₁u₁ + Z₂u₂ + Z₃u₃` from the hypercube partial sum. `roundMaskEquiv`: for `ζ^{j+1} ≠ 0`
   the pivots `(a₀, a₁, b₁, s₁, t₁)` (const and slope of `m_lin`, slopes of `u₁, u₂, u₃`) biject
   onto all five coefficients; `card_roundMask_hyperplane`: exactly `|F|^4` pivots land on each
   claim hyperplane `c₁+c₂+c₃+c₄ = κ`.
3. **Multi-round.** `sumcheck_mask_hvzk`, `sumcheck_mask_fiber_one/zero`,
   `card_consistent`: for any two honest degree-≤4 transcripts with the same claim, every event
   has the same number of masks (`TVD = 0`); each consistent transcript has exactly one mask, and
   there are `|F|^{4D}` of each. `fourColumn_sumcheck_hvzk` transports this to per-round fresh
   4-column pivots; `basefold_hvzk` is the degree-2 `eq(r,x)·bfMask(x)` analogue.

Model caveat (`[OPEN]` in the note): the multi-round results assume the round-`j` pivots range
over all chain-consistent values ("fresh pivots per round"). In a single multilinear column the
slopes of round `j` are fixed by round `j-1`; full rank of that chained map is not proved here.

Import boundary: `Theory/` tier (Mathlib only).
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Minidregg.Theory.Char2Degree4SumcheckHvzk

open scoped BigOperators

set_option autoImplicit false

/-! ## §0. Booleans and the zero-on-hypercube factors -/

/-- A Boolean as `0`/`1`. -/
def bitVal {R : Type*} [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

@[simp] theorem bitVal_false {R : Type*} [Zero R] [One R] : bitVal false = (0 : R) := rfl
@[simp] theorem bitVal_true {R : Type*} [Zero R] [One R] : bitVal true = (1 : R) := rfl

/-- `x² + x = 0` on `{0,1}` in characteristic `2`. -/
theorem bitVal_sq_add_self {R : Type*} [Ring R] [CharP R 2] (b : Bool) :
    (bitVal b : R) ^ 2 + bitVal b = 0 := by
  cases b <;> simp [CharTwo.add_self_eq_zero]

/-- `x³ + x² = 0` on `{0,1}` in characteristic `2`. -/
theorem bitVal_cube_add_sq {R : Type*} [Ring R] [CharP R 2] (b : Bool) :
    (bitVal b : R) ^ 3 + bitVal b ^ 2 = 0 := by
  cases b <;> simp [CharTwo.add_self_eq_zero]

/-! ## §1. Teeth: the affine round-0 leak -/

/-- Summing a function of one coordinate over `{0,1}^m`. -/
theorem sum_cube_coord {R : Type*} [AddCommMonoid R] {m : ℕ} (k : Fin m) (g : Bool → R) :
    ∑ x : Fin m → Bool, g (x k) =
      Fintype.card ({j : Fin m // j ≠ k} → Bool) • (g false + g true) := by
  rw [Fintype.sum_equiv (Equiv.funSplitAt k Bool) (fun x => g (x k)) (fun p => g p.1)
    (fun x => rfl),
    Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, add_comm]

/-- **Affine char-2 trap.** Every total-degree-1 mask sums to `0` on `{0,1}^m`, `m ≥ 2`. -/
theorem charTwo_affine_cubeSum_eq_zero {R : Type*} [CommRing R] [CharP R 2] {m : ℕ}
    (hm : 2 ≤ m) (a₀ : R) (a : Fin m → R) :
    ∑ x : Fin m → Bool, (a₀ + ∑ k, a k * bitVal (x k)) = 0 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  have hconst : ∑ _x : Fin m → Bool, a₀ = 0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [h2, zero_pow (by omega), zero_mul]
  have hk : ∀ k : Fin m, ∑ x : Fin m → Bool, a k * bitVal (x k) = 0 := by
    intro k
    rw [sum_cube_coord k (fun b => a k * bitVal b)]
    obtain ⟨i, hi⟩ : ∃ i : Fin m, i ≠ k := by
      by_cases hk0 : (k : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by show 1 ≠ (k : ℕ); omega)⟩
      · exact ⟨⟨0, by omega⟩, Fin.ne_of_val_ne (by show 0 ≠ (k : ℕ); omega)⟩
    have hpos : 0 < Fintype.card {j : Fin m // j ≠ k} := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    rw [Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    rw [h2, zero_pow hpos.ne', zero_mul]
  rw [Finset.sum_add_distrib, hconst, zero_add, Finset.sum_comm]
  exact Finset.sum_eq_zero (fun k _ => hk k)

/-- Consequence: adding `ρ ·` an affine mask leaves the hypercube sum (the round-0 claim)
equal to the unmasked one, for every target `Φ`. -/
theorem charTwo_affine_mask_round0_leaks {R : Type*} [CommRing R] [CharP R 2] {m : ℕ}
    (hm : 2 ≤ m) (Φ : (Fin m → Bool) → R) (ρ a₀ : R) (a : Fin m → R) :
    ∑ x : Fin m → Bool, (Φ x + ρ * (a₀ + ∑ k, a k * bitVal (x k))) = ∑ x, Φ x := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, charTwo_affine_cubeSum_eq_zero hm, mul_zero,
    add_zero]

/-- Falsifier for the reading "every *multilinear* mask sums to `0`": `x₀x₁` sums to `1`. -/
theorem multilinear_x0x1_cubeSum_eq_one {R : Type*} [CommRing R] :
    ∑ x : Fin 2 → Bool, (bitVal (x 0) * bitVal (x 1) : R) = 1 := by
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Bool) (fun x => (bitVal (x 0) * bitVal (x 1) : R))
    (fun p => (bitVal p.1 * bitVal p.2 : R)) (fun x => rfl)]
  simp [Fintype.sum_prod_type]

/-- The `m ≥ 2` guard is load-bearing: at `m = 1`, `∑ x₀ = 1`. -/
theorem ell1_affine_cubeSum_eq_one {R : Type*} [CommRing R] :
    ∑ x : Fin 1 → Bool, (bitVal (x 0) : R) = 1 := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) (fun x => (bitVal (x 0) : R))
    (fun b => (bitVal b : R))
    (fun x => rfl)]
  simp

/-! ## §2. Univariate round polynomials and the characteristic-2 claim hyperplane -/

/-- Evaluation of the coefficient vector `c₀, …, cₙ` at `x`. -/
def peval {F : Type*} [Semiring F] {n : ℕ} (c : Fin (n + 1) → F) (x : F) : F :=
  ∑ i, c i * x ^ (i : ℕ)

theorem peval_five {F : Type*} [CommRing F] (c : Fin 5 → F) (x : F) :
    peval c x = c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3 + c 4 * x ^ 4 := by
  simp [peval, Fin.sum_univ_five]

theorem peval_three {F : Type*} [CommRing F] (c : Fin 3 → F) (x : F) :
    peval c x = c 0 + c 1 * x + c 2 * x ^ 2 := by
  simp [peval, Fin.sum_univ_three]

/-- **The char-2 sumcheck check.** `p(0) + p(1) = c₁ + c₂ + c₃ + c₄`: `c₀` is free and the claim
cuts a hyperplane in `(c₁, …, c₄)`. -/
theorem peval_zero_add_one_five {F : Type*} [CommRing F] [CharP F 2] (c : Fin 5 → F) :
    peval c 0 + peval c 1 = c 1 + c 2 + c 3 + c 4 := by
  rw [peval_five, peval_five]
  linear_combination c 0 * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem peval_zero_add_one_three {F : Type*} [CommRing F] [CharP F 2] (c : Fin 3 → F) :
    peval c 0 + peval c 1 = c 1 + c 2 := by
  rw [peval_three, peval_three]
  linear_combination c 0 * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- Falsifier: outside characteristic `2` the identity fails (`ZMod 3`, `p = 1`). -/
theorem zmod3_c0_not_free :
    peval (![1, 0, 0, 0, 0] : Fin 5 → ZMod 3) 0 + peval ![1, 0, 0, 0, 0] 1 ≠
      (![1, 0, 0, 0, 0] : Fin 5 → ZMod 3) 1 + ![1, 0, 0, 0, 0] 2 + ![1, 0, 0, 0, 0] 3 +
        ![1, 0, 0, 0, 0] 4 := by
  rw [peval_five, peval_five]
  decide

theorem peval_add {F : Type*} [CommRing F] {n : ℕ} (c c' : Fin (n + 1) → F) (x : F) :
    peval (c + c') x = peval c x + peval c' x := by
  simp [peval, add_mul, Finset.sum_add_distrib]

theorem peval_smul {F : Type*} [CommRing F] {n : ℕ} (a : F) (c : Fin (n + 1) → F) (x : F) :
    peval (a • c) x = a * peval c x := by
  simp [peval, Finset.mul_sum, mul_assoc]

/-! ## §3. Multi-round consistency and the translation lemma -/

/-- Claim entering round `j`: the public claim at `j = 0`, else `p_{j-1}(r_{j-1})`. -/
def claimAt {F : Type*} [Semiring F] {n D : ℕ} (claim : F) (τ : Fin D → Fin (n + 1) → F)
    (r : Fin D → F) : ℕ → F
  | 0 => claim
  | j + 1 => if h : j < D then peval (τ ⟨j, h⟩) (r ⟨j, h⟩) else 0

/-- A `D`-round transcript of degree-`≤ n` round polynomials passes every sumcheck check. -/
def Consistent {F : Type*} [Semiring F] {n D : ℕ} (r : Fin D → F) (claim : F)
    (τ : Fin D → Fin (n + 1) → F) : Prop :=
  ∀ j : Fin D, peval (τ j) 0 + peval (τ j) 1 = claimAt claim τ r j

section Linear

variable {F : Type*} [CommRing F] {n D : ℕ}

theorem claimAt_lin (r : Fin D → F) (a b c₁ c₂ : F) (τ₁ τ₂ : Fin D → Fin (n + 1) → F)
    (j : ℕ) :
    claimAt (a * c₁ + b * c₂) (a • τ₁ + b • τ₂) r j =
      a * claimAt c₁ τ₁ r j + b * claimAt c₂ τ₂ r j := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [claimAt]
    split_ifs
    · simp [peval_add, peval_smul]
    · simp

/-- Consistency is affine-linear in (claim, transcript). -/
theorem Consistent.lin {r : Fin D → F} {c₁ c₂ : F} {τ₁ τ₂ : Fin D → Fin (n + 1) → F}
    (h₁ : Consistent r c₁ τ₁) (h₂ : Consistent r c₂ τ₂) (a b : F) :
    Consistent r (a * c₁ + b * c₂) (a • τ₁ + b • τ₂) := by
  intro j
  rw [claimAt_lin, ← h₁ j, ← h₂ j]
  simp only [Pi.add_apply, Pi.smul_apply, peval_add, peval_smul]
  ring

end Linear

/-- **Translation lemma.** If the mask set `Q` is invariant under the shift by
`ρ⁻¹ • (h - h')`, then every event `E` on the masked transcript has the same mask count
under the honest messages `h` and `h'`. -/
theorem shift_event_card_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (Q : V → Prop) (ρ : F) (hρ : ρ ≠ 0) (h h' : V)
    (hQ : ∀ M, Q M ↔ Q (M + ρ⁻¹ • (h - h'))) (E : V → Prop) :
    Nat.card {M // Q M ∧ E (h + ρ • M)} = Nat.card {M // Q M ∧ E (h' + ρ • M)} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight (ρ⁻¹ • (h - h'))) ?_)
  intro M
  have key : h' + ρ • (M + ρ⁻¹ • (h - h')) = h + ρ • M := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul]
    abel
  simp only [Equiv.coe_addRight, key]
  exact and_congr (hQ M) Iff.rfl

/-! ## §4. Degree-≤4 sumcheck: zero-claim masks give `TVD = 0` and exact counts -/

section Deg4

variable {F : Type*} [Field F] {D : ℕ}

/-- **Joint `D`-round HVZK.** Masks uniform over the zero-claim consistent transcripts:
any two honest transcripts with the same claim induce the same count for every event. -/
theorem sumcheck_mask_hvzk (r : Fin D → F) (claim ρ : F) (hρ : ρ ≠ 0)
    (h h' : Fin D → Fin 5 → F) (hh : Consistent r claim h) (hh' : Consistent r claim h')
    (E : (Fin D → Fin 5 → F) → Prop) :
    Nat.card {M : Fin D → Fin 5 → F // Consistent r 0 M ∧ E (h + ρ • M)} =
      Nat.card {M : Fin D → Fin 5 → F // Consistent r 0 M ∧ E (h' + ρ • M)} := by
  refine shift_event_card_eq _ ρ hρ h h' ?_ E
  have hd : Consistent r 0 (ρ⁻¹ • (h - h')) := by
    have := Consistent.lin hh hh' ρ⁻¹ (-ρ⁻¹)
    rwa [neg_mul, add_neg_cancel, neg_smul, ← sub_eq_add_neg, ← smul_sub] at this
  intro M
  constructor
  · intro hM
    simpa using Consistent.lin hM hd 1 1
  · intro hM
    simpa using Consistent.lin hM hd 1 (-1)

/-- Each consistent transcript has exactly one mask preimage. -/
theorem sumcheck_mask_fiber_one (r : Fin D → F) (claim ρ : F) (hρ : ρ ≠ 0)
    (h : Fin D → Fin 5 → F) (hh : Consistent r claim h) (t : Fin D → Fin 5 → F)
    (ht : Consistent r claim t) :
    Nat.card {M : Fin D → Fin 5 → F // Consistent r 0 M ∧ h + ρ • M = t} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨M₁, _, e₁⟩ ⟨M₂, _, e₂⟩ => Subtype.ext ?_⟩, ⟨⟨ρ⁻¹ • (t - h), ?_, ?_⟩⟩⟩
  · rw [← e₂] at e₁
    have e := add_left_cancel e₁
    calc M₁ = ρ⁻¹ • (ρ • M₁) := by rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]
      _ = ρ⁻¹ • (ρ • M₂) := by rw [e]
      _ = M₂ := by rw [smul_smul, inv_mul_cancel₀ hρ, one_smul]
  · have := Consistent.lin ht hh ρ⁻¹ (-ρ⁻¹)
    rwa [neg_mul, add_neg_cancel, neg_smul, ← sub_eq_add_neg, ← smul_sub] at this
  · rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
    abel

/-- Inconsistent transcripts have no mask preimage. -/
theorem sumcheck_mask_fiber_zero (r : Fin D → F) (claim ρ : F)
    (h : Fin D → Fin 5 → F) (hh : Consistent r claim h) (t : Fin D → Fin 5 → F)
    (ht : ¬ Consistent r claim t) :
    Nat.card {M : Fin D → Fin 5 → F // Consistent r 0 M ∧ h + ρ • M = t} = 0 := by
  have : IsEmpty {M : Fin D → Fin 5 → F // Consistent r 0 M ∧ h + ρ • M = t} :=
    ⟨fun ⟨M, hM, e⟩ => ht (by simpa [e] using Consistent.lin hh hM 1 ρ)⟩
  exact Nat.card_of_isEmpty

variable [CharP F 2]

/-- Row with free `c₀, c₂, c₃, c₄` and `c₁` solved from the claim `k`. -/
def rowOf (k : F) (g : Fin 4 → F) : Fin 5 → F := ![g 0, k + g 1 + g 2 + g 3, g 1, g 2, g 3]

/-- Forget `c₁`. -/
def dropC1 (c : Fin 5 → F) : Fin 4 → F := ![c 0, c 2, c 3, c 4]

theorem rowOf_sum (k : F) (g : Fin 4 → F) :
    rowOf k g 1 + rowOf k g 2 + rowOf k g 3 + rowOf k g 4 = k := by
  simp only [rowOf, Matrix.cons_val]
  linear_combination (g 1 + g 2 + g 3) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem rowOf_dropC1 (c : Fin 5 → F) : rowOf (c 1 + c 2 + c 3 + c 4) (dropC1 c) = c := by
  funext i
  fin_cases i <;> simp [rowOf, dropC1]
  linear_combination (c 2 + c 3 + c 4) * (CharTwo.two_eq_zero : (2 : F) = 0)

omit [CharP F 2] in
theorem dropC1_rowOf (k : F) (g : Fin 4 → F) : dropC1 (rowOf k g) = g := by
  funext i
  fin_cases i <;> simp [rowOf, dropC1]

/-- The claim hyperplane `c₁+c₂+c₃+c₄ = κ` ≃ `(c₀, c₂, c₃, c₄)`: dimension 4, `c₀` free. -/
noncomputable def hyperplaneEquiv (κ : F) :
    {c : Fin 5 → F // peval c 0 + peval c 1 = κ} ≃ (Fin 4 → F) where
  toFun c := dropC1 c.1
  invFun g := ⟨rowOf κ g, by rw [peval_zero_add_one_five, rowOf_sum]⟩
  left_inv c := by
    apply Subtype.ext
    have hc := c.2
    rw [peval_zero_add_one_five] at hc
    have h := rowOf_dropC1 c.1
    rw [hc] at h
    exact h
  right_inv g := dropC1_rowOf κ g

/-- Extend a `Fin D`-indexed family by `0`. -/
def ext0 {α : Type*} [Zero α] (f : Fin D → α) (j : ℕ) : α := if h : j < D then f ⟨j, h⟩ else 0

/-- Running claim of the transcript built from free coordinates `f`. -/
def kap (c : F) (f : Fin D → Fin 4 → F) (r : Fin D → F) : ℕ → F
  | 0 => c
  | j + 1 => peval (rowOf (kap c f r j) (ext0 f j)) (ext0 r j)

/-- The consistent transcript with free coordinates `f`. -/
def build (c : F) (f : Fin D → Fin 4 → F) (r : Fin D → F) : Fin D → Fin 5 → F :=
  fun j => rowOf (kap c f r j) (f j)

theorem build_consistent (c : F) (f : Fin D → Fin 4 → F) (r : Fin D → F) :
    Consistent r c (build c f r) := by
  intro j
  rw [peval_zero_add_one_five]
  show rowOf _ (f j) 1 + rowOf _ (f j) 2 + rowOf _ (f j) 3 + rowOf _ (f j) 4 = _
  rw [rowOf_sum]
  rcases j with ⟨_ | j, hj⟩
  · rfl
  · have hn : j < D := Nat.lt_of_succ_lt hj
    simp [kap, claimAt, ext0, hn, build]

theorem kap_dropC1 {c : F} {r : Fin D → F} {τ : Fin D → Fin 5 → F} (hτ : Consistent r c τ) :
    ∀ j, kap c (fun i => dropC1 (τ i)) r j = claimAt c τ r j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [kap, claimAt, ext0]
    split_ifs with hn
    · rw [ih, ← hτ ⟨j, hn⟩, peval_zero_add_one_five, rowOf_dropC1]
    · simp [rowOf, peval_five]

/-- Consistent transcripts with claim `c` ≃ free coordinates `(c₀, c₂, c₃, c₄)` per round. -/
noncomputable def consistentEquiv (r : Fin D → F) (c : F) :
    {τ : Fin D → Fin 5 → F // Consistent r c τ} ≃ (Fin D → Fin 4 → F) where
  toFun τ := fun j => dropC1 (τ.1 j)
  invFun f := ⟨build c f r, build_consistent c f r⟩
  left_inv τ := by
    apply Subtype.ext
    funext j
    show rowOf (kap c (fun i => dropC1 (τ.1 i)) r j) (dropC1 (τ.1 j)) = τ.1 j
    rw [kap_dropC1 τ.2, ← τ.2 j, peval_zero_add_one_five, rowOf_dropC1]
  right_inv f := by
    funext j
    exact dropC1_rowOf _ _

/-- **Count.** There are exactly `|F|^{4D}` consistent degree-≤4 transcripts for every claim. -/
theorem card_consistent (r : Fin D → F) (c : F) :
    Nat.card {τ : Fin D → Fin 5 → F // Consistent r c τ} = Nat.card F ^ (4 * D) := by
  rw [Nat.card_congr (consistentEquiv r c), Nat.card_fun, Nat.card_fun, pow_mul]
  simp

end Deg4

/-! ## §5. The 4-column characteristic-2 mask, round by round -/

/-- Public data of round `j`: `zj = ζ^{j+1}`, `E = ∑_{k<j} ζ^{k+1} r_k`,
`C2 = ∑_{k<j} ζ^{k+1}(r_k²+r_k)`, `C3 = ∑_{k<j} ζ^{k+1}(r_k³+r_k²)`. -/
structure RoundPublic (F : Type*) where
  zj : F
  E : F
  C2 : F
  C3 : F

/-- The standard publics from `ζ` and the challenges (matching `P₁, Z₂, Z₃` of
`Tower256AlgebraicCert.evalCombinedPhiC`). -/
def stdPublic {F : Type*} [CommRing F] {D : ℕ} (ζ : F) (r : Fin D → F) (j : Fin D) :
    RoundPublic F where
  zj := ζ ^ ((j : ℕ) + 1)
  E := ∑ k ∈ Finset.univ.filter (fun k : Fin D => k < j), ζ ^ ((k : ℕ) + 1) * r k
  C2 := ∑ k ∈ Finset.univ.filter (fun k : Fin D => k < j), ζ ^ ((k : ℕ) + 1) * (r k ^ 2 + r k)
  C3 := ∑ k ∈ Finset.univ.filter (fun k : Fin D => k < j),
    ζ ^ ((k : ℕ) + 1) * (r k ^ 3 + r k ^ 2)

theorem stdPublic_zj_ne_zero {F : Type*} [Field F] {D : ℕ} {ζ : F} (hζ : ζ ≠ 0)
    (r : Fin D → F) (j : Fin D) : (stdPublic ζ r j).zj ≠ 0 :=
  pow_ne_zero _ hζ

/-- Non-pivot partial-sum data of round `j`: `b0 = U₁(0)`, `w0 + w1 X` the `P₁`-suffix part,
`s0 = U₂(0)`, `t0 = U₃(0)`. -/
structure RoundAux (F : Type*) where
  b0 : F
  w0 : F
  w1 : F
  s0 : F
  t0 : F

section Round

variable {F : Type*}

/-- Coefficients `c₀..c₄` of the round-`j` mask polynomial from the pivots
`θ = (a₀, a₁, b₁, s₁, t₁)`. -/
def roundMaskCoeffs [Mul F] [Add F] (P : RoundPublic F) (A : RoundAux F) (θ : Fin 5 → F) :
    Fin 5 → F :=
  ![P.C3 * A.t0 + P.C2 * A.s0 + P.E * A.b0 + A.w0 + θ 0,
    P.C3 * θ 4 + P.C2 * θ 3 + P.zj * A.s0 + P.E * θ 2 + P.zj * A.b0 + A.w1 + θ 1,
    P.zj * A.t0 + P.zj * (A.s0 + θ 3) + P.zj * θ 2,
    P.zj * (A.t0 + θ 4) + P.zj * θ 3,
    P.zj * θ 4]

/-- The coefficient vector evaluates to the factored round mask. -/
theorem roundMaskCoeffs_eval [CommRing F] (P : RoundPublic F) (A : RoundAux F)
    (θ : Fin 5 → F) (X : F) :
    peval (roundMaskCoeffs P A θ) X =
      (θ 0 + θ 1 * X) + ((P.E + P.zj * X) * (A.b0 + θ 2 * X) + (A.w0 + A.w1 * X)) +
        (P.C2 + P.zj * (X ^ 2 + X)) * (A.s0 + θ 3 * X) +
        (P.C3 + P.zj * (X ^ 3 + X ^ 2)) * (A.t0 + θ 4 * X) := by
  rw [peval_five]
  simp [roundMaskCoeffs]
  ring

/-- Suffix part of `P₁` on a Boolean suffix: `∑_{k>j} ζ^{k+1} x_k`. -/
def suffixLin [CommRing F] {n : ℕ} (zs : Fin n → F) (y : Fin n → Bool) : F :=
  ∑ k, zs k * bitVal (y k)

/-- **Hypercube grounding.** The round-`j` partial sum over the Boolean suffix `y ∈ {0,1}^n`
of `m_lin + P₁u₁ + Z₂u₂ + Z₃u₃` (columns multilinear in the round variable `X`) is the
polynomial with coefficients `roundMaskCoeffs`, with pivots and aux given by suffix sums. -/
theorem roundPartialSum_eq [CommRing F] [CharP F 2] {n : ℕ} (P : RoundPublic F)
    (zs : Fin n → F) (m0 m1 u10 u11 u20 u21 u30 u31 : (Fin n → Bool) → F) (X : F) :
    ∑ y : Fin n → Bool,
      ((m0 y + X * m1 y) +
        (P.E + P.zj * X + suffixLin zs y) * (u10 y + X * u11 y) +
        (P.C2 + P.zj * (X ^ 2 + X) + ∑ k, zs k * (bitVal (y k) ^ 2 + bitVal (y k))) *
          (u20 y + X * u21 y) +
        (P.C3 + P.zj * (X ^ 3 + X ^ 2) + ∑ k, zs k * (bitVal (y k) ^ 3 + bitVal (y k) ^ 2)) *
          (u30 y + X * u31 y)) =
    peval (roundMaskCoeffs P
        ⟨∑ y, u10 y, ∑ y, suffixLin zs y * u10 y, ∑ y, suffixLin zs y * u11 y,
          ∑ y, u20 y, ∑ y, u30 y⟩
        ![∑ y, m0 y, ∑ y, m1 y, ∑ y, u11 y, ∑ y, u21 y, ∑ y, u31 y]) X := by
  simp only [bitVal_sq_add_self, bitVal_cube_add_sq, mul_zero, Finset.sum_const_zero, add_zero]
  have hpt : ∀ y : Fin n → Bool,
      (m0 y + X * m1 y) + (P.E + P.zj * X + suffixLin zs y) * (u10 y + X * u11 y) +
          (P.C2 + P.zj * (X ^ 2 + X)) * (u20 y + X * u21 y) +
          (P.C3 + P.zj * (X ^ 3 + X ^ 2)) * (u30 y + X * u31 y) =
        (m0 y + X * m1 y) + ((P.E + P.zj * X) * (u10 y + X * u11 y) +
          (suffixLin zs y * u10 y + X * (suffixLin zs y * u11 y))) +
          (P.C2 + P.zj * (X ^ 2 + X)) * (u20 y + X * u21 y) +
          (P.C3 + P.zj * (X ^ 3 + X ^ 2)) * (u30 y + X * u31 y) := fun y => by ring
  rw [Finset.sum_congr rfl (fun y _ => hpt y), roundMaskCoeffs_eval]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.cons_val]
  ring

/-- Explicit inverse of the pivot map (`zj ≠ 0`). -/
noncomputable def roundMaskInv [Field F] (P : RoundPublic F) (A : RoundAux F) (c : Fin 5 → F) :
    Fin 5 → F :=
  let t1 := c 4 / P.zj
  let s1 := c 3 / P.zj - A.t0 - t1
  let b1 := c 2 / P.zj - A.t0 - A.s0 - s1
  ![c 0 - (P.C3 * A.t0 + P.C2 * A.s0 + P.E * A.b0 + A.w0),
    c 1 - (P.C3 * t1 + P.C2 * s1 + P.zj * A.s0 + P.E * b1 + P.zj * A.b0 + A.w1),
    b1, s1, t1]

/-- **Per-round full-rank bijection.** For `ζ^{j+1} ≠ 0` the pivots
`(a₀, a₁, b₁, s₁, t₁)` ↔ `(c₀, c₁, c₂, c₃, c₄)`: `t₁ ↦ c₄` (`u₃` via `Z₃`), `s₁ ↦ c₃`
(`u₂` via `Z₂`), `b₁ ↦ c₂` (`u₁` via `P₁`), `a₁ ↦ c₁`, `a₀ ↦ c₀` (`m_lin`), triangularly. -/
noncomputable def roundMaskEquiv [Field F] (P : RoundPublic F) (A : RoundAux F)
    (hz : P.zj ≠ 0) : (Fin 5 → F) ≃ (Fin 5 → F) where
  toFun := roundMaskCoeffs P A
  invFun := roundMaskInv P A
  left_inv θ := by
    funext i
    fin_cases i <;> simp [roundMaskCoeffs, roundMaskInv] <;> field_simp <;> ring
  right_inv c := by
    funext i
    fin_cases i <;> simp [roundMaskCoeffs, roundMaskInv] <;> field_simp <;> ring

/-- Mask claim of round `j` in characteristic `2`: `a₀` never enters it. -/
theorem roundMask_claim [CommRing F] [CharP F 2] (P : RoundPublic F) (A : RoundAux F)
    (θ : Fin 5 → F) :
    peval (roundMaskCoeffs P A θ) 0 + peval (roundMaskCoeffs P A θ) 1 =
      θ 1 + P.E * θ 2 + P.zj * (A.b0 + θ 2) + A.w1 + P.C2 * θ 3 + P.C3 * θ 4 := by
  rw [peval_zero_add_one_five]
  simp only [roundMaskCoeffs, Matrix.cons_val]
  linear_combination (P.zj * (A.s0 + A.t0 + θ 3 + θ 4)) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **Rank 4 on each claim hyperplane.** Exactly `|F|^4` pivot vectors give a round
polynomial with `p(0) + p(1) = κ`; it is the 4-dimensional slice `c₁+c₂+c₃+c₄ = κ`. -/
theorem card_roundMask_hyperplane [Field F] [CharP F 2] (P : RoundPublic F) (A : RoundAux F)
    (hz : P.zj ≠ 0) (κ : F) :
    Nat.card {θ : Fin 5 → F //
        peval (roundMaskCoeffs P A θ) 0 + peval (roundMaskCoeffs P A θ) 1 = κ} =
      Nat.card F ^ 4 := by
  have e := (Equiv.subtypeEquiv (q := fun c : Fin 5 → F => peval c 0 + peval c 1 = κ)
    (roundMaskEquiv P A hz) (fun _ => Iff.rfl)).trans (hyperplaneEquiv κ)
  exact (Nat.card_congr e).trans (by rw [Nat.card_fun]; simp)

/-- **Tooth (#125).** A lone `Z₂ · u` term with `u` constant in `X` has `deg ≤ 2`. -/
theorem z2_constant_term_degree_le_two [CommRing F] (P : RoundPublic F) (s : F) (X : F) :
    roundMaskCoeffs P ⟨0, 0, 0, s, 0⟩ 0 3 = 0 ∧ roundMaskCoeffs P ⟨0, 0, 0, s, 0⟩ 0 4 = 0 ∧
      peval (roundMaskCoeffs P ⟨0, 0, 0, s, 0⟩ 0) X = (P.C2 + P.zj * (X ^ 2 + X)) * s := by
  refine ⟨by simp [roundMaskCoeffs], by simp [roundMaskCoeffs], ?_⟩
  rw [roundMaskCoeffs_eval]
  simp

/-- **Tooth (#125).** Without the `Z₃` column (`t₀ = t₁ = 0`) the `X⁴` coefficient of the mask
is identically zero, for any `m_lin, u₁, u₂`. -/
theorem threeColumn_c4_eq_zero [CommRing F] (P : RoundPublic F) (A : RoundAux F)
    (θ : Fin 5 → F) (hθ : θ 4 = 0) : roundMaskCoeffs P A θ 4 = 0 := by
  simp [roundMaskCoeffs, hθ]

/-- Hence honest round polynomials with different `c₄` give support-disjoint masked
transcripts under the 3-column mask: the `[X⁴]` coefficient is unblinded (`TVD = 1`). -/
theorem threeColumn_transcripts_separate [CommRing F] (P P' : RoundPublic F)
    (A A' : RoundAux F) (θ θ' : Fin 5 → F) (hθ : θ 4 = 0) (hθ' : θ' 4 = 0) (ρ : F)
    (h h' : Fin 5 → F) (hne : h 4 ≠ h' 4) :
    h + ρ • roundMaskCoeffs P A θ ≠ h' + ρ • roundMaskCoeffs P' A' θ' := by
  intro e
  have := congrFun e 4
  simp [threeColumn_c4_eq_zero P A θ hθ, threeColumn_c4_eq_zero P' A' θ' hθ'] at this
  exact hne this

end Round

/-! ## §6. 4-column multi-round HVZK (fresh pivots per round) -/

section FourColumn

variable {F : Type*} [Field F] {D : ℕ}

/-- Round-by-round 4-column mask transcript. -/
def colMask (P : Fin D → RoundPublic F) (A : Fin D → RoundAux F) (θ : Fin D → Fin 5 → F) :
    Fin D → Fin 5 → F :=
  fun j => roundMaskCoeffs (P j) (A j) (θ j)

noncomputable def colMaskEquiv (P : Fin D → RoundPublic F) (A : Fin D → RoundAux F)
    (hP : ∀ j, (P j).zj ≠ 0) : (Fin D → Fin 5 → F) ≃ (Fin D → Fin 5 → F) :=
  Equiv.piCongrRight fun j => roundMaskEquiv (P j) (A j) (hP j)

theorem colMask_card_congr (P : Fin D → RoundPublic F) (A : Fin D → RoundAux F)
    (hP : ∀ j, (P j).zj ≠ 0) (S : (Fin D → Fin 5 → F) → Prop) :
    Nat.card {θ // S (colMask P A θ)} = Nat.card {M // S M} :=
  Nat.card_congr (Equiv.subtypeEquiv (colMaskEquiv P A hP) (fun _ => Iff.rfl))

/-- **4-column HVZK, `TVD = 0`.** With pivots ranging over the chain-consistent (zero-claim)
values, every event on the masked transcript has the same count under any two honest
degree-≤4 transcripts with the same claim. -/
theorem fourColumn_sumcheck_hvzk (P : Fin D → RoundPublic F) (A : Fin D → RoundAux F)
    (hP : ∀ j, (P j).zj ≠ 0) (r : Fin D → F) (claim ρ : F) (hρ : ρ ≠ 0)
    (h h' : Fin D → Fin 5 → F) (hh : Consistent r claim h) (hh' : Consistent r claim h')
    (E : (Fin D → Fin 5 → F) → Prop) :
    Nat.card {θ // Consistent r 0 (colMask P A θ) ∧ E (h + ρ • colMask P A θ)} =
      Nat.card {θ // Consistent r 0 (colMask P A θ) ∧ E (h' + ρ • colMask P A θ)} := by
  rw [colMask_card_congr P A hP (fun M => Consistent r 0 M ∧ E (h + ρ • M)),
    colMask_card_congr P A hP (fun M => Consistent r 0 M ∧ E (h' + ρ • M))]
  exact sumcheck_mask_hvzk r claim ρ hρ h h' hh hh' E

/-- **Capstone (G8).** For `ζ ≠ 0`, `ρ ≠ 0`, honest degree-≤4 transcript `h` with claim
`claim`: the pivot space has `|F|^{4D}` elements, as does the simulator's support (uniform
consistent transcripts); every consistent transcript has exactly one pivot preimage and
every inconsistent one none, so the real view is exactly the simulator's uniform view. -/
theorem char2_deg4_sumcheck_hvzk [CharP F 2] [Fintype F] (ζ : F) (hζ : ζ ≠ 0)
    (r : Fin D → F) (A : Fin D → RoundAux F) (claim ρ : F) (hρ : ρ ≠ 0)
    (h : Fin D → Fin 5 → F) (hh : Consistent r claim h) :
    Nat.card {θ // Consistent r 0 (colMask (stdPublic ζ r) A θ)} = Fintype.card F ^ (4 * D) ∧
    Nat.card {τ : Fin D → Fin 5 → F // Consistent r claim τ} = Fintype.card F ^ (4 * D) ∧
    (∀ t, Consistent r claim t →
      Nat.card {θ // Consistent r 0 (colMask (stdPublic ζ r) A θ) ∧
        h + ρ • colMask (stdPublic ζ r) A θ = t} = 1) ∧
    (∀ t, ¬ Consistent r claim t →
      Nat.card {θ // Consistent r 0 (colMask (stdPublic ζ r) A θ) ∧
        h + ρ • colMask (stdPublic ζ r) A θ = t} = 0) := by
  have hP := stdPublic_zj_ne_zero hζ r
  refine ⟨?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [colMask_card_congr _ A hP (Consistent r 0), card_consistent, Nat.card_eq_fintype_card]
  · rw [card_consistent, Nat.card_eq_fintype_card]
  · rw [colMask_card_congr _ A hP (fun M => Consistent r 0 M ∧ h + ρ • M = t)]
    exact sumcheck_mask_fiber_one r claim ρ hρ h hh t ht
  · rw [colMask_card_congr _ A hP (fun M => Consistent r 0 M ∧ h + ρ • M = t)]
    exact sumcheck_mask_fiber_zero r claim ρ h hh t ht

end FourColumn

/-! ## §7. Degree-2 BaseFold mask `eq(r, x) · bfMask(x)` -/

section BaseFold

variable {F : Type*}

/-- Coefficients of `κ · (e + X) · (β₀ + β₁ X)`: the round polynomial of `eq(r,x)·g(x)` with
eq-prefix `κ`, round eq-factor `e + X` (`e = 1 + r_j`) and `g`'s round partial sum `β`. -/
def bfRound [Mul F] [Add F] (κ e : F) (β : Fin 2 → F) : Fin 3 → F :=
  ![κ * e * β 0, κ * (β 0 + e * β 1), κ * β 1]

/-- In characteristic `2`, `eq(r, X) = r X + (1-r)(1-X) = (1 + r) + X`. -/
theorem eqFactor_charTwo [CommRing F] [CharP F 2] (r X : F) :
    r * X + (1 - r) * (1 - X) = (1 + r) + X := by
  linear_combination (r * X - r - X) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem bfRound_eval [CommRing F] (κ e : F) (β : Fin 2 → F) (X : F) :
    peval (bfRound κ e β) X = κ * (e + X) * (β 0 + β 1 * X) := by
  rw [peval_three]
  simp [bfRound]
  ring

/-- The BaseFold round polynomial vanishes at `X = e` (char 2), so it lives in a
2-dimensional space and the claim leaves one free coordinate per round. -/
theorem bfRound_root [CommRing F] [CharP F 2] (κ e : F) (β : Fin 2 → F) :
    peval (bfRound κ e β) e = 0 := by
  rw [bfRound_eval, CharTwo.add_self_eq_zero, mul_zero, zero_mul]

theorem bfRound_injective [Field F] {κ : F} (hκ : κ ≠ 0) (e : F) :
    Function.Injective (bfRound κ e) := by
  intro β β' hb
  have h2 := congrFun hb 2
  have h1 := congrFun hb 1
  simp [bfRound, hκ] at h1 h2
  funext i
  fin_cases i
  · simpa [h2] using h1
  · simpa using h2

/-- Every degree-≤2 polynomial with root `e` is a masked BaseFold round polynomial. -/
theorem bfRound_surj_root [Field F] [CharP F 2] {κ : F} (hκ : κ ≠ 0) (e : F)
    (q : Fin 3 → F) (hq : peval q e = 0) : ∃ β, bfRound κ e β = q := by
  refine ⟨![(q 1 - e * q 2) / κ, q 2 / κ], ?_⟩
  rw [peval_three] at hq
  funext i
  fin_cases i <;> simp [bfRound] <;> field_simp
  · linear_combination (-1 : F) * hq + (e * q 1) * (CharTwo.two_eq_zero : (2 : F) = 0)
  · ring

/-- Round-by-round BaseFold transcript from the linear factors `β`. -/
def bfT [Mul F] [Add F] {D : ℕ} (κ e : Fin D → F) (β : Fin D → Fin 2 → F) :
    Fin D → Fin 3 → F :=
  fun j => bfRound (κ j) (e j) (β j)

theorem bfT_add [CommRing F] {D : ℕ} (κ e : Fin D → F) (β β' : Fin D → Fin 2 → F) :
    bfT κ e (β + β') = bfT κ e β + bfT κ e β' := by
  funext j i
  fin_cases i <;> simp [bfT, bfRound] <;> ring

theorem bfT_smul [CommRing F] {D : ℕ} (κ e : Fin D → F) (a : F) (β : Fin D → Fin 2 → F) :
    bfT κ e (a • β) = a • bfT κ e β := by
  funext j i
  fin_cases i <;> simp [bfT, bfRound] <;> ring

/-- **BaseFold HVZK, `TVD = 0`.** Honest round polynomials of `eq(r,x)·f(x)` are `bfT γ`; the
mask contributes `ρ · bfT β` with `β` uniform over zero-claim chains. Any two honest `γ, γ'`
with the same claim give the same count for every transcript event, in all `D` rounds. -/
theorem basefold_hvzk [Field F] {D : ℕ} (κ e r : Fin D → F) (claim ρ : F) (hρ : ρ ≠ 0)
    (γ γ' : Fin D → Fin 2 → F) (hγ : Consistent r claim (bfT κ e γ))
    (hγ' : Consistent r claim (bfT κ e γ')) (E : (Fin D → Fin 3 → F) → Prop) :
    Nat.card {β // Consistent r 0 (bfT κ e β) ∧ E (bfT κ e γ + ρ • bfT κ e β)} =
      Nat.card {β // Consistent r 0 (bfT κ e β) ∧ E (bfT κ e γ' + ρ • bfT κ e β)} := by
  have hview : ∀ g β : Fin D → Fin 2 → F,
      bfT κ e g + ρ • bfT κ e β = bfT κ e (g + ρ • β) := fun g β => by
    rw [bfT_add, bfT_smul]
  simp only [hview]
  refine shift_event_card_eq (fun β => Consistent r 0 (bfT κ e β)) ρ hρ γ γ' ?_
    (fun v => E (bfT κ e v))
  have hd : Consistent r 0 (bfT κ e (ρ⁻¹ • (γ - γ'))) := by
    have := Consistent.lin hγ hγ' ρ⁻¹ (-ρ⁻¹)
    rw [neg_mul, add_neg_cancel] at this
    have hs : ρ⁻¹ • (γ - γ') = ρ⁻¹ • γ + (-ρ⁻¹) • γ' := by
      rw [neg_smul, ← sub_eq_add_neg, smul_sub]
    rwa [hs, bfT_add, bfT_smul, bfT_smul]
  intro β
  constructor
  · intro hβ
    simpa [bfT_add] using Consistent.lin hβ hd 1 1
  · intro hβ
    simpa [bfT_add] using Consistent.lin hβ hd 1 (-1)

end BaseFold

/-! ## §8. Premise inhabitation and kernel-checked instances over `ZMod 2` -/

/-- The capstone's premises are inhabited (`ZMod 2`, one round, `ζ = ρ = 1`, `h = 0`). -/
theorem zmod2_capstone_premises_inhabited :
    (1 : ZMod 2) ≠ 0 ∧ Consistent (D := 1) (fun _ => (0 : ZMod 2)) 0
      (0 : Fin 1 → Fin 5 → ZMod 2) := by
  refine ⟨by decide, fun j => ?_⟩
  fin_cases j
  simp [peval, claimAt]

/-- Concrete 3-column distinguisher over `ZMod 2`: `h = 0` and `h' = X + X⁴` share the claim
`0` (`p(0)+p(1) = c₁+…+c₄`) but differ in `c₄`, so no pair of 3-column masks confuses them. -/
theorem zmod2_threeColumn_distinguisher (P : RoundPublic (ZMod 2)) (A : RoundAux (ZMod 2))
    (θ θ' : Fin 5 → ZMod 2) (hθ : θ 4 = 0) (hθ' : θ' 4 = 0) :
    peval (![0, 1, 0, 0, 1] : Fin 5 → ZMod 2) 0 + peval (![0, 1, 0, 0, 1] : Fin 5 → ZMod 2) 1 =
        peval (0 : Fin 5 → ZMod 2) 0 + peval (0 : Fin 5 → ZMod 2) 1 ∧
      (0 : Fin 5 → ZMod 2) + roundMaskCoeffs P A θ ≠
        ![0, 1, 0, 0, 1] + roundMaskCoeffs P A θ' := by
  refine ⟨by rw [peval_five, peval_five, peval_five, peval_five]; decide, ?_⟩
  have := threeColumn_transcripts_separate P P A A θ θ' hθ hθ' 1 0 ![0, 1, 0, 0, 1]
    (by decide)
  simpa using this

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.char2_deg4_sumcheck_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms char2_deg4_sumcheck_hvzk

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.fourColumn_sumcheck_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fourColumn_sumcheck_hvzk

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.sumcheck_mask_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck_mask_hvzk

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.card_roundMask_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_roundMask_hyperplane

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.roundPartialSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundPartialSum_eq

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.basefold_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefold_hvzk

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.bfRound_surj_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfRound_surj_root

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.charTwo_affine_cubeSum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_affine_cubeSum_eq_zero

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.multilinear_x0x1_cubeSum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms multilinear_x0x1_cubeSum_eq_one

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.z2_constant_term_degree_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms z2_constant_term_degree_le_two

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.threeColumn_transcripts_separate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms threeColumn_transcripts_separate

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.zmod2_threeColumn_distinguisher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod2_threeColumn_distinguisher

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.zmod2_capstone_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod2_capstone_premises_inhabited

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.zmod3_c0_not_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod3_c0_not_free

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.card_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_consistent

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.sumcheck_mask_fiber_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck_mask_fiber_one

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.sumcheck_mask_fiber_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck_mask_fiber_zero

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.peval_zero_add_one_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms peval_zero_add_one_five

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.ell1_affine_cubeSum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ell1_affine_cubeSum_eq_one

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.charTwo_affine_mask_round0_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_affine_mask_round0_leaks

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.eqFactor_charTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqFactor_charTwo

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.bfRound_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfRound_root

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.bfRound_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bfRound_injective

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.threeColumn_c4_eq_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms threeColumn_c4_eq_zero

/-- info: 'Minidregg.Theory.Char2Degree4SumcheckHvzk.roundMask_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundMask_claim

end Minidregg.Theory.Char2Degree4SumcheckHvzk
