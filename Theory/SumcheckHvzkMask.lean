/-
# `Theory.SumcheckHvzkMask` — Algebraic Metatheory of Separable Univariate Sumcheck Masking

Formalizes the Libra / Aurora / Virgo / `GMask` separable univariate sumcheck masking
transformation
$$g(X_0, \dots, X_{\ell - 1}) = \sum_{j=0}^{\ell - 1} g_j(X_j), \qquad \tilde{P} = P + g, \qquad g_j \in R_{\le d}[X],$$
over general rings and finite fields, together with its exact characteristic-two obstruction,
odd-characteristic linear fiber structure, and under-degree leakage counterexamples.

## Main Results

1. **Boolean-Cube Sum Identity (`cubeSum_separableFun_eq`, `cubeSum_separableMask_eq`):**
   Over any `[Ring R]` (and `[CommRing R]` for `Polynomial R`) and $\ell \ge 1$,
   $$\sum_{x \in \{0,1\}^\ell} \sum_{j=0}^{\ell-1} g_j(x_j)
     = 2^{\ell - 1} \cdot \sum_{j=0}^{\ell-1} (g_j(0) + g_j(1)).$$

2. **Characteristic-2 Trap Theorem (`charTwo_cubeSum_separableMask_eq_zero` & Falsifiers):**
   Over any `[Ring R] [CharP R 2]` (instantiated at `ZMod 2` and `Tower256 = binaryTower 8 = GF(2^256)`),
   for every $\ell \ge 2$, the hypercube sum of *every* separable univariate mask $g(x) = \sum_j g_j(x_j)$
   is **identically $0$** (`2^{\ell-1} = 0`), so $M = \sum_{x \in \{0,1\}^\ell} (P(x) + g(x)) = \sum_{x \in \{0,1\}^\ell} P(x)$
   leaks the unmasked hypercube sum of $P$ with probability $1$ (`charTwo_separableMask_not_gapAtMost`,
   kernel-checked on `ZMod 2` at $\ell = 2$ in `zmod2_ell2_separableMask_leaks`), and every round
   polynomial at $i + 2 < \ell$ vanishes identically (`charTwo_maskRoundPoly_eq_zero_of_lt`).

3. **Odd-Characteristic Perfect HVZK Fiber Regularity & Zero Statistical Gap
   (`maskTranscriptLinearEquiv`, `hvzkSumcheck_fiber_card_eq`, `hvzkSumcheck_terminal_fiber_card_eq`,
   `hvzkSumcheck_view_prob_eq`, `hvzkSumcheck_gapAtMost_zero`):**
   Over any `[Field F] [Fintype F]` with `(2 : F) ≠ 0`, $\ell \ge 1$, $d \ge 1$, and any challenge
   vector $r : \text{Fin }\ell \to F$:
   - Constructs an explicit `LinearEquiv` decomposing `MaskSpace ℓ d F` into
     `ConsistentTranscript hℓ r × (Fin (ℓ - 1) → F)`, proving that the mask-to-view linear map is
     **surjective onto sum-consistent transcripts** (`Fintype.card = |F|^{\ell d + 1}`) with exact
     constant fiber cardinality $|F|^{\ell - 1}$ (and identical $|F|^{\ell - 1}$ fiber cardinality
     both when the terminal evaluation $g(r) = s_{\ell-1}(r_{\ell-1}) - P(r)$ is pinned and when
     `cubeSum g = 0` masks a public claimed sum!).
   - Proves that *every* two target polynomials $P_0, P_1$ of per-variable degree $\le d$ induce the
     **exact same uniform distribution** over sum-consistent transcripts, achieving
     `FiniteTapeGap.GapAtMost tapes 0 den` against every distinguisher.

4. **Under-Degree Leakage Tooth (`underDegreeMask_distinguishes` & `ZMod 7` Kernel Keystones):**
   When the mask degree is $d_{\text{mask}} = d - 1 < d$ (e.g. an affine mask on a quadratic Gruen
   sumcheck), the degree-$d$ coefficient of $s_0(X)$ equals that of $P_0(X)$ unmasked, separating
   witnesses of identical hypercube sum ($P_0(X_0, X_1) = X_0^2$ vs $P_1(X_0, X_1) = X_0$ over `ZMod 7`)
   with advantage $1$, while upgrading to a degree-$2$ separable mask on the exact same pair restores
   zero statistical gap (`zmod7_quadratic_deg2Mask_fiber_and_gap_zero`).

Import boundary: `Theory/` tier (`Mathlib.*` + `Theory.*` only).
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theory.FiniteTapeGap
import Theory.BinaryTower
import Theory.AssertAxioms

namespace Minidregg.Theory.SumcheckHvzkMask

open scoped BigOperators
open Polynomial
open Minidregg.Theory.FiniteTapeGap
open Minidregg.Theory.AssertAxioms

set_option autoImplicit false

/-! ## §1. Boolean Hypercube & Separable Univariate Mask Identity -/

/-- Embed a boolean bit as `0` or `1` in any type with `0` and `1`. -/
def bitVal {R : Type*} [Zero R] [One R] (b : Bool) : R :=
  if b then 1 else 0

@[simp] theorem bitVal_false {R : Type*} [Zero R] [One R] : bitVal (false : Bool) = (0 : R) := rfl
@[simp] theorem bitVal_true {R : Type*} [Zero R] [One R] : bitVal (true : Bool) = (1 : R) := rfl

/-- Embed a boolean hypercube vertex `x : Fin ℓ → Bool` into `Fin ℓ → R`. -/
def cubePoint {R : Type*} [Zero R] [One R] {ℓ : ℕ} (x : Fin ℓ → Bool) : Fin ℓ → R :=
  fun j => bitVal (x j)

@[simp] theorem cubePoint_apply {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (x : Fin ℓ → Bool) (j : Fin ℓ) :
    cubePoint (R := R) x j = bitVal (x j) := rfl

/-- Sum of an `ℓ`-variate function over the boolean hypercube `{0, 1}^ℓ`. -/
def cubeSum {R : Type*} [AddCommMonoid R] [Zero R] [One R] {ℓ : ℕ}
    (f : (Fin ℓ → R) → R) : R :=
  ∑ x : (Fin ℓ → Bool), f (cubePoint x)

/-- Separable sum `g(x₀, …, x_{ℓ-1}) = ∑_{j=0}^{ℓ-1} g_j(x_j)` of univariate functions. -/
def separableFun {R : Type*} [AddCommMonoid R] {ℓ : ℕ}
    (g : Fin ℓ → R → R) (x : Fin ℓ → R) : R :=
  ∑ j : Fin ℓ, g j (x j)

/-- Separable polynomial evaluation `g(x₀, …, x_{ℓ-1}) = ∑_{j=0}^{ℓ-1} (g_j).eval (x_j)`. -/
def separablePolyEval {R : Type*} [Semiring R] {ℓ : ℕ}
    (g : Fin ℓ → Polynomial R) (x : Fin ℓ → R) : R :=
  ∑ j : Fin ℓ, (g j).eval (x j)

theorem separablePolyEval_eq_separableFun {R : Type*} [Semiring R] {ℓ : ℕ}
    (g : Fin ℓ → Polynomial R) :
    separablePolyEval g = separableFun (fun j y => (g j).eval y) := rfl

/-- Split coordinate `i` out of a finite function space `(ι → α) ≃ α × ({k : ι // k ≠ i} → α)`. -/
def splitCoordAt {ι α : Type*} [DecidableEq ι] (i : ι) :
    (ι → α) ≃ α × ({k : ι // k ≠ i} → α) where
  toFun x := (x i, fun k => x k.1)
  invFun p k := if h : k = i then p.1 else p.2 ⟨k, h⟩
  left_inv x := by
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨b, rest⟩
    ext
    · simp
    · rename_i k
      simp [k.2]

theorem card_compl_coord_bool {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Fintype.card ({k : ι // k ≠ i} → Bool) = 2 ^ (Fintype.card ι - 1) := by
  have hsub : Fintype.card {k : ι // k ≠ i} = Fintype.card ι - 1 := by
    have hc := Fintype.card_subtype_compl (fun k : ι => k = i)
    rw [Fintype.card_subtype_eq i] at hc
    exact hc
  rw [Fintype.card_fun, Fintype.card_bool, hsub]

/-- Summing a function of a single coordinate `x i` over all boolean assignments `ι → Bool`
multiplies `f 0 + f 1` by `2 ^ (|ι| - 1)` over any `[Ring R]`. -/
theorem sum_boolCube_singleCoord {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (i : ι) (f : R → R) :
    (∑ x : (ι → Bool), f (bitVal (x i))) =
      (2 : R) ^ (Fintype.card ι - 1) * (f 0 + f 1) := by
  calc
    (∑ x : (ι → Bool), f (bitVal (x i)))
        = ∑ p : Bool × ({k : ι // k ≠ i} → Bool), f (bitVal p.1) :=
          Fintype.sum_equiv (splitCoordAt i) _ _ (fun _ => rfl)
    _ = ∑ b : Bool, ∑ _rest : ({k : ι // k ≠ i} → Bool), f (bitVal b) :=
          Fintype.sum_prod_type _
    _ = (∑ _rest : ({k : ι // k ≠ i} → Bool), f (bitVal true)) +
        (∑ _rest : ({k : ι // k ≠ i} → Bool), f (bitVal false)) :=
          Fintype.sum_bool _
    _ = (Fintype.card ({k : ι // k ≠ i} → Bool)) • f 1 +
        (Fintype.card ({k : ι // k ≠ i} → Bool)) • f 0 := by
          simp [Finset.sum_const, Finset.card_univ]
    _ = (2 ^ (Fintype.card ι - 1)) • (f 0 + f 1) := by
          rw [card_compl_coord_bool i, add_comm, smul_add]
    _ = (2 : R) ^ (Fintype.card ι - 1) * (f 0 + f 1) := by
          rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- **Boolean-Cube Sum Identity (general `[Ring R]` function form):**
for every `ℓ : ℕ`, summing a separable univariate function
`g(x) = ∑_{j=0}^{ℓ-1} g_j(x_j)` over `{0, 1}^ℓ` scales `∑_j (g_j(0) + g_j(1))` by `2^{ℓ - 1}`
(for `ℓ ≥ 1`, each coordinate fiber has `2^{ℓ - 1}` boolean assignments; at `ℓ = 0`, both sides
vanish). -/
theorem cubeSum_separableFun_eq {R : Type*} [Ring R] {ℓ : ℕ}
    (g : Fin ℓ → R → R) :
    cubeSum (separableFun g) =
      (2 : R) ^ (ℓ - 1) * ∑ j : Fin ℓ, (g j 0 + g j 1) := by
  unfold cubeSum separableFun
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa [Fintype.card_fin] using sum_boolCube_singleCoord j (g j)

/-- **Boolean-Cube Sum Identity (`cubeSum_separableMask_eq`):**
over any `[CommRing R]` and `ℓ ≥ 1` (in fact all `ℓ : ℕ`), the boolean-cube sum of a separable
polynomial mask `g(X₀, …, X_{ℓ-1}) = ∑_{j=0}^{ℓ-1} g_j(X_j)` equals
`2^{ℓ - 1} · ∑_{j=0}^{ℓ-1} (g_j(0) + g_j(1))`. -/
theorem cubeSum_separableMask_eq {R : Type*} [CommRing R] {ℓ : ℕ}
    (g : Fin ℓ → Polynomial R) :
    cubeSum (separablePolyEval g) =
      (2 : R) ^ (ℓ - 1) * ∑ j : Fin ℓ, ((g j).eval 0 + (g j).eval 1) :=
  cubeSum_separableFun_eq (fun j y => (g j).eval y)

/-- Additivity of `cubeSum` under separable masking `P̃ = P + g`. -/
theorem cubeSum_add_separableMask {R : Type*} [CommRing R] {ℓ : ℕ}
    (P : (Fin ℓ → R) → R) (g : Fin ℓ → Polynomial R) :
    cubeSum (fun x => P x + separablePolyEval g x) =
      cubeSum P + (2 : R) ^ (ℓ - 1) * ∑ j : Fin ℓ, ((g j).eval 0 + (g j).eval 1) := by
  unfold cubeSum
  rw [Finset.sum_add_distrib]
  exact congrArg (cubeSum P + ·) (cubeSum_separableMask_eq g)

/-! ## §2. The Characteristic-2 Trap Theorem & Falsifiers (`ZMod 2` and `Tower256`) -/

/-- **The Characteristic-2 Trap Theorem (`charTwo_cubeSum_separableMask_eq_zero`):**
over *any* `[Ring R] [CharP R 2]` and *every* `ℓ ≥ 2`, the boolean-cube sum of **every** separable
univariate mask `g(x) = ∑_j g_j(x_j)` is identically `0` because `2^{ℓ - 1} = 0` in characteristic `2`. -/
theorem charTwo_cubeSum_separableMask_eq_zero {R : Type*} [Ring R] [CharP R 2]
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (g : Fin ℓ → R → R) :
    cubeSum (separableFun g) = 0 := by
  rw [cubeSum_separableFun_eq g]
  have hpos : ℓ - 1 ≠ 0 := by omega
  rw [CharTwo.two_eq_zero, zero_pow hpos, zero_mul]

/-- **Sharpness of `2 ≤ ℓ` at Characteristic 2 (`tower256_ell1_separableMask_nonzero_sum`):**
analogous to `Selvage.CharTwoWall.foldingTower_charTwo_inhabited_at_height_zero`, the `2 ≤ ℓ`
guard in `charTwo_cubeSum_separableMask_eq_zero` is **load-bearing**: at `ℓ = 1`, `2^{1-1} = 1`
even in characteristic `2`, so `g₀(X) = X` over `Tower256` (`GF(2^256)`) and `ZMod 2` achieves
`cubeSum = 1 ≠ 0`! -/
theorem charTwo_ell1_separableMask_eq_one {R : Type*} [CommRing R] [Nontrivial R] :
    cubeSum (separablePolyEval (fun _ : Fin 1 => (Polynomial.X : Polynomial R))) = 1 ∧
    cubeSum (separablePolyEval (fun _ : Fin 1 => (Polynomial.X : Polynomial R))) ≠ 0 := by
  have h1 : cubeSum (separablePolyEval (fun _ : Fin 1 => (Polynomial.X : Polynomial R))) = 1 := by
    rw [cubeSum_separableMask_eq]
    simp
  exact ⟨h1, h1 ▸ one_ne_zero⟩

theorem tower256_ell1_separableMask_nonzero_sum :
    cubeSum (separablePolyEval
      (fun _ : Fin 1 => (Polynomial.X : Polynomial (Minidregg.Theory.binaryTower 8)))) = 1 ∧
    cubeSum (separablePolyEval
      (fun _ : Fin 1 => (Polynomial.X : Polynomial (Minidregg.Theory.binaryTower 8)))) ≠ 0 :=
  charTwo_ell1_separableMask_eq_one

/-- Polynomial specialization of `charTwo_cubeSum_separableMask_eq_zero`. -/
theorem charTwo_cubeSum_separablePoly_eq_zero {R : Type*} [CommRing R] [CharP R 2]
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (g : Fin ℓ → Polynomial R) :
    cubeSum (separablePolyEval g) = 0 :=
  charTwo_cubeSum_separableMask_eq_zero hℓ (fun j y => (g j).eval y)

/-- **Unmasked Hypercube-Sum Leakage in Characteristic 2:**
over `[Ring R] [CharP R 2]` with `ℓ ≥ 2`, adding *any* separable mask `g` leaves the hypercube sum
`∑_{x ∈ {0,1}^ℓ} (P(x) + g(x)) = ∑_{x ∈ {0,1}^ℓ} P(x)` completely unblinded unless an auxiliary
scalar `G₀` (or Hilbert-90 / trace mask) blinds the claimed sum. -/
theorem charTwo_masked_cubeSum_eq {R : Type*} [Ring R] [CharP R 2]
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (P : (Fin ℓ → R) → R) (g : Fin ℓ → R → R) :
    cubeSum (fun x => P x + separableFun g x) = cubeSum P := by
  unfold cubeSum
  rw [Finset.sum_add_distrib]
  change cubeSum P + cubeSum (separableFun g) = cubeSum P
  rw [charTwo_cubeSum_separableMask_eq_zero hℓ g, add_zero]

/-- **Concrete instantiation on `Tower256 = binaryTower 8 = GF(2^256)`:**
every separable univariate polynomial mask in `ℓ ≥ 2` variables sums to `0` over `{0,1}^ℓ`. -/
theorem tower256_cubeSum_separableMask_eq_zero {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (g : Fin ℓ → Polynomial (Minidregg.Theory.binaryTower 8)) :
    cubeSum (separablePolyEval g) = 0 :=
  charTwo_cubeSum_separablePoly_eq_zero hℓ g

/-- **Characteristic-2 Statistical Separation (`charTwo_separableMask_not_gapAtMost`):**
whenever two witnesses `P₀, P₁` have distinct hypercube sums `cubeSum P₀ ≠ cubeSum P₁` in
characteristic `2` (`ℓ ≥ 2`), observing the masked hypercube sum `M = cubeSum (P + g)` without
an extra blinding scalar `G₀` separates `P₀` from `P₁` with probability `1` (refuting every
`GapAtMost tapes num den` with `num < den`). -/
theorem charTwo_separableMask_not_gapAtMost {R : Type*} [Ring R] [CharP R 2] [DecidableEq R]
    {ℓ tapes num den : ℕ} (hℓ : 2 ≤ ℓ) (hsmall : num < den)
    (P₀ P₁ : (Fin ℓ → R) → R) (hne : cubeSum P₀ ≠ cubeSum P₁)
    (maskAt : Fin tapes → Fin ℓ → R → R) :
    ¬ GapAtMost tapes num den
        (fun t => decide (cubeSum (fun x => P₀ x + separableFun (maskAt t) x) = cubeSum P₀))
        (fun t => decide (cubeSum (fun x => P₁ x + separableFun (maskAt t) x) = cubeSum P₀)) := by
  apply not_gapAtMost_of_separating hsmall
  · intro t
    rw [charTwo_masked_cubeSum_eq hℓ P₀ (maskAt t)]
    exact decide_eq_true rfl
  · intro t
    rw [charTwo_masked_cubeSum_eq hℓ P₁ (maskAt t)]
    exact decide_eq_false hne.symm

/-! ## §3. Interactive Sumcheck Transcripts, Linear Fiber Equiv & Odd-Characteristic HVZK -/

/-- Univariate polynomial of degree `≤ d`, represented by its `d + 1` coefficients `c₀, …, c_d`. -/
abbrev RoundPoly (d : ℕ) (R : Type*) := Fin (d + 1) → R

/-- Evaluate `p : RoundPoly d R` at `x : R` via `∑_{k=0}^d p_k x^k`. -/
def evalRoundPoly {R : Type*} [Semiring R] {d : ℕ} (p : RoundPoly d R) (x : R) : R :=
  ∑ k : Fin (d + 1), p k * x ^ (k : ℕ)

/-- Linear evaluation map `p ↦ p(x)` on `RoundPoly d R`. -/
def evalRoundPolyLM {R : Type*} [CommSemiring R] {d : ℕ} (x : R) : RoundPoly d R →ₗ[R] R where
  toFun p := evalRoundPoly p x
  map_add' p q := by
    simp only [evalRoundPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [evalRoundPoly, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

@[simp] theorem evalRoundPoly_zero {R : Type*} [Semiring R] {d : ℕ} :
    ∀ x : R, evalRoundPoly (0 : RoundPoly d R) x = 0 := by
  intro x; simp [evalRoundPoly]

theorem evalRoundPoly_add {R : Type*} [Semiring R] {d : ℕ}
    (p q : RoundPoly d R) (x : R) :
    evalRoundPoly (p + q) x = evalRoundPoly p x + evalRoundPoly q x := by
  simp only [evalRoundPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem evalRoundPoly_sub {R : Type*} [Ring R] {d : ℕ}
    (p q : RoundPoly d R) (x : R) :
    evalRoundPoly (p - q) x = evalRoundPoly p x - evalRoundPoly q x := by
  simp only [evalRoundPoly, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem evalRoundPoly_smul {R : Type*} [CommSemiring R] {d : ℕ}
    (c : R) (p : RoundPoly d R) (x : R) :
    evalRoundPoly (c • p) x = c * evalRoundPoly p x :=
  (evalRoundPolyLM x).map_smul c p

/-- Evaluate `p : RoundPoly d R` at `0` extracts the constant coefficient `p 0`. -/
@[simp] theorem evalRoundPoly_at_zero {R : Type*} [Semiring R] {d : ℕ} (p : RoundPoly d R) :
    evalRoundPoly p 0 = p 0 := by
  unfold evalRoundPoly
  rw [Fin.sum_univ_succ]
  simp

/-- Evaluate `p : RoundPoly d R` at `1` sums all coefficients `p 0 + ∑_{k < d} p (k.succ)`. -/
theorem evalRoundPoly_at_one {R : Type*} [Semiring R] {d : ℕ} (p : RoundPoly d R) :
    evalRoundPoly p 1 = p 0 + ∑ k : Fin d, p k.succ := by
  unfold evalRoundPoly
  rw [Fin.sum_univ_succ]
  simp

/-- Boolean endpoint sum `p(0) + p(1) = 2 * p(0) + ∑_{k < d} p(k.succ)`. -/
theorem evalRoundPoly_zero_add_one {R : Type*} [Ring R] {d : ℕ} (p : RoundPoly d R) :
    evalRoundPoly p 0 + evalRoundPoly p 1 = 2 * p 0 + ∑ k : Fin d, p k.succ := by
  rw [evalRoundPoly_at_zero, evalRoundPoly_at_one, two_mul, add_assoc]

/-- Embed `RoundPoly d R` into Mathlib's `Polynomial R`. -/
noncomputable def roundPolyToPolynomial {R : Type*} [Semiring R] {d : ℕ}
    (p : RoundPoly d R) : Polynomial R :=
  ∑ k : Fin (d + 1), Polynomial.C (p k) * Polynomial.X ^ (k : ℕ)

@[simp] theorem eval_roundPolyToPolynomial {R : Type*} [Semiring R] {d : ℕ}
    (p : RoundPoly d R) (x : R) :
    (roundPolyToPolynomial p).eval x = evalRoundPoly p x := by
  simp [roundPolyToPolynomial, evalRoundPoly, Polynomial.eval_finsetSum]

theorem degree_roundPolyToPolynomial_lt {R : Type*} [Semiring R] {d : ℕ}
    (p : RoundPoly d R) :
    (roundPolyToPolynomial p).degree < ((d + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe (d + 1))).mpr fun k _ =>
      lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le (k : ℕ) (p k))
        (WithBot.coe_lt_coe.mpr k.isLt))

/-- Evaluation-node isomorphism (`GMask` representation): over any field `F` with `d + 1` distinct
evaluation nodes `nodes : Fin (d + 1) ↪ F` (e.g. `0, 1, …, d` in large-characteristic fields),
coefficient polynomials `RoundPoly d F` are linearly equivalent to `(d + 1)`-point value tables. -/
noncomputable def evalAtNodesLinearEquiv {F : Type*} [Field F] [DecidableEq F] {d : ℕ}
    (nodes : Fin (d + 1) ↪ F) :
    RoundPoly d F ≃ₗ[F] (Fin (d + 1) → F) := by
  refine LinearEquiv.ofLinearMap
    (LinearMap.pi fun t => evalRoundPolyLM (nodes t))
    { toFun := fun vals k => (Lagrange.interpolate Finset.univ nodes vals).coeff (k : ℕ)
      map_add' := fun u v => by
        funext k
        rw [(Lagrange.interpolate Finset.univ nodes).map_add u v, Polynomial.coeff_add, Pi.add_apply]
      map_smul' := fun c u => by
        funext k
        rw [(Lagrange.interpolate Finset.univ nodes).map_smul c u, Polynomial.coeff_smul,
          Pi.smul_apply, RingHom.id_apply] }
    ?_ ?_
  · apply LinearMap.ext
    intro vals
    funext t
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.pi_apply,
      evalRoundPolyLM, LinearMap.id_coe, id_eq]
    have hdeg : (Lagrange.interpolate Finset.univ nodes vals).degree <
        ((d + 1 : ℕ) : WithBot ℕ) := by
      have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := nodes) vals
        nodes.injective.injOn
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have heq : roundPolyToPolynomial
        (fun k : Fin (d + 1) => (Lagrange.interpolate Finset.univ nodes vals).coeff (k : ℕ)) =
        Lagrange.interpolate Finset.univ nodes vals := by
      ext n
      simp only [roundPolyToPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
      by_cases hn : n < d + 1
      · rw [Finset.sum_eq_single ⟨n, hn⟩]
        · simp
        · intro b _ hb
          have hne : n ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
          simp [hne]
        · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
      · rw [Finset.sum_eq_zero]
        · symm
          exact Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.mp hn))
        · intro b _
          have hne : n ≠ (b : ℕ) := by omega
          simp [hne]
    change evalRoundPoly _ (nodes t) = vals t
    rw [← eval_roundPolyToPolynomial, heq]
    exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := nodes) vals
      nodes.injective.injOn (Finset.mem_univ t)
  · apply LinearMap.ext
    intro p
    funext k
    simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      evalRoundPolyLM, LinearMap.id_coe, id_eq]
    set vals : Fin (d + 1) → F := fun t => evalRoundPoly p (nodes t)
    have hinterp : Lagrange.interpolate Finset.univ nodes vals = roundPolyToPolynomial p := by
      symm
      apply Lagrange.eq_interpolate_of_eval_eq (s := Finset.univ) (v := nodes) vals
        nodes.injective.injOn
      · simpa [Finset.card_univ, Fintype.card_fin] using degree_roundPolyToPolynomial_lt p
      · intro t _
        exact eval_roundPolyToPolynomial p (nodes t)
    change (Lagrange.interpolate Finset.univ nodes vals).coeff (k : ℕ) = p k
    rw [hinterp]
    simp only [roundPolyToPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      have hne : (k : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne]
    · intro hmem; exact False.elim (hmem (Finset.mem_univ _))

/-! ### Multivariate Target Polynomials of Individual Degree `≤ d` & Sumcheck Slices -/

/-- Multivariate polynomial in `ℓ` variables of per-variable degree `≤ d`, represented by its
coefficient tensor `(Fin ℓ → Fin (d + 1)) → R`. -/
abbrev TargetPoly (ℓ d : ℕ) (R : Type*) := (Fin ℓ → Fin (d + 1)) → R

/-- Evaluate `P : TargetPoly ℓ d R` at `x : Fin ℓ → R`. -/
def evalTargetPoly {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (P : TargetPoly ℓ d R) (x : Fin ℓ → R) : R :=
  ∑ e : (Fin ℓ → Fin (d + 1)), P e * ∏ j : Fin ℓ, (x j) ^ (e j : ℕ)

/-- Canonical `R`-linear embedding of `TargetPoly ℓ d R` into Mathlib's `MvPolynomial (Fin ℓ) R`. -/
noncomputable def targetPolyToMvPolynomial {R : Type*} [CommSemiring R] {ℓ d : ℕ} :
    TargetPoly ℓ d R →ₗ[R] MvPolynomial (Fin ℓ) R where
  toFun P :=
    ∑ e : (Fin ℓ → Fin (d + 1)),
      MvPolynomial.C (P e) * ∏ j : Fin ℓ, MvPolynomial.X j ^ (e j : ℕ)
  map_add' P Q := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c P := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    change MvPolynomial.C (c * P e) * _ = _
    rw [map_mul, mul_assoc, MvPolynomial.C_mul']

@[simp] theorem eval_targetPolyToMvPolynomial {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (P : TargetPoly ℓ d R) (x : Fin ℓ → R) :
    MvPolynomial.eval x (targetPolyToMvPolynomial P) = evalTargetPoly P x := by
  simp [targetPolyToMvPolynomial, evalTargetPoly, map_sum, map_mul, map_prod, map_pow]

/-- Round-`i` sumcheck evaluation point `(r₀, …, r_{i-1}, x, tail_{i+1}, …, tail_{ℓ-1})`. -/
def slicePoint {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (i : Fin ℓ) (x : R) (tail : {j : Fin ℓ // i < j} → Bool) (j : Fin ℓ) : R :=
  if hlt : j < i then r j
  else if heq : j = i then x
  else bitVal (tail ⟨j, lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)⟩)

@[simp] theorem slicePoint_lt {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (i : Fin ℓ) (x : R) (tail : {j : Fin ℓ // i < j} → Bool)
    {j : Fin ℓ} (hj : j < i) :
    slicePoint r i x tail j = r j := by
  simp [slicePoint, hj]

@[simp] theorem slicePoint_eq {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (i : Fin ℓ) (x : R) (tail : {j : Fin ℓ // i < j} → Bool) :
    slicePoint r i x tail i = x := by
  simp [slicePoint]

@[simp] theorem slicePoint_gt {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (i : Fin ℓ) (x : R) (tail : {j : Fin ℓ // i < j} → Bool)
    {j : Fin ℓ} (hj : i < j) :
    slicePoint r i x tail j = bitVal (tail ⟨j, hj⟩) := by
  have hnotlt : ¬ j < i := not_lt.mpr (le_of_lt hj)
  have hne : j ≠ i := ne_of_gt hj
  simp [slicePoint, hnotlt, hne]

theorem slicePoint_ne {R : Type*} [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (i : Fin ℓ) (x y : R) (tail : {j : Fin ℓ // i < j} → Bool)
    {j : Fin ℓ} (hne : j ≠ i) :
    slicePoint r i x tail j = slicePoint r i y tail j := by
  by_cases hlt : j < i
  · simp [slicePoint, hlt]
  · simp [slicePoint, hlt, hne]

/-- Sum of an `ℓ`-variate function over the remaining boolean coordinates `j > i` at round `i`. -/
def roundSliceSum {R : Type*} [AddCommMonoid R] [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (f : (Fin ℓ → R) → R) (i : Fin ℓ) (x : R) : R :=
  ∑ tail : ({j : Fin ℓ // i < j} → Bool), f (slicePoint r i x tail)

/-- Split boolean hypercube `Fin ℓ → Bool` into coordinate `0` and tail `{j : Fin ℓ // ⟨0, hℓ⟩ < j} → Bool`. -/
def splitCubeZero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Fin ℓ → Bool) ≃ Bool × ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool) where
  toFun b := (b ⟨0, hℓ⟩, fun j => b j.1)
  invFun p j :=
    if h : j = ⟨0, hℓ⟩ then p.1
    else p.2 ⟨j, Nat.pos_of_ne_zero (fun (hz : (j : ℕ) = 0) => h (Fin.ext hz))⟩
  left_inv b := by
    funext j
    by_cases h : j = ⟨0, hℓ⟩
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨b0, tail⟩
    refine Prod.ext (by simp) (funext fun j => ?_)
    have hne : j.1 ≠ ⟨0, hℓ⟩ := ne_of_gt j.2
    simp [hne]

/-- Round-0 boolean endpoint sum equals the total hypercube sum `cubeSum f`. -/
theorem roundSliceSum_zero {R : Type*} [AddCommMonoid R] [Zero R] [One R] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (f : (Fin ℓ → R) → R) :
    roundSliceSum r f ⟨0, hℓ⟩ 0 + roundSliceSum r f ⟨0, hℓ⟩ 1 = cubeSum f := by
  have hpt : ∀ (b : Bool) (tail : {j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool),
      cubePoint (R := R) ((splitCubeZero hℓ).symm (b, tail)) =
        slicePoint r ⟨0, hℓ⟩ (bitVal b) tail := by
    intro b tail
    funext j
    by_cases hj0 : j = ⟨0, hℓ⟩
    · subst hj0
      simp [splitCubeZero, cubePoint]
    · have hpos : (⟨0, hℓ⟩ : Fin ℓ) < j :=
        Nat.pos_of_ne_zero (fun (hz : (j : ℕ) = 0) => hj0 (Fin.ext hz))
      rw [slicePoint_gt r ⟨0, hℓ⟩ _ tail hpos]
      simp [splitCubeZero, cubePoint, hj0]
  have hprod := Fintype.sum_prod_type
    (fun p : Bool × ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool) =>
      f (cubePoint ((splitCubeZero hℓ).symm p)))
  have hequiv := Fintype.sum_equiv (splitCubeZero hℓ).symm
    (fun p : Bool × ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool) =>
      f (cubePoint ((splitCubeZero hℓ).symm p)))
    (fun b : Fin ℓ → Bool => f (cubePoint b))
    (fun _ => rfl)
  calc
    roundSliceSum r f ⟨0, hℓ⟩ 0 + roundSliceSum r f ⟨0, hℓ⟩ 1
        = (∑ tail : ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool),
            f (cubePoint ((splitCubeZero hℓ).symm (false, tail)))) +
          (∑ tail : ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool),
            f (cubePoint ((splitCubeZero hℓ).symm (true, tail)))) := by
            simp only [roundSliceSum, hpt, bitVal_false, bitVal_true]
    _ = ∑ b : Bool, ∑ tail : ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool),
          f (cubePoint ((splitCubeZero hℓ).symm (b, tail))) := by
          rw [Fintype.sum_bool, add_comm]
    _ = ∑ p : Bool × ({j : Fin ℓ // (⟨0, hℓ⟩ : Fin ℓ) < j} → Bool),
          f (cubePoint ((splitCubeZero hℓ).symm p)) := hprod.symm
    _ = cubeSum f := hequiv

private theorem gt_succ_of_gt_ne {ℓ i : ℕ} (hi : i + 1 < ℓ) {j : Fin ℓ}
    (h1 : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin ℓ) < j)
    (hne : j ≠ ⟨i + 1, hi⟩) :
    (⟨i + 1, hi⟩ : Fin ℓ) < j := by
  have hle : i + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt h1
  have hnej : (j : ℕ) ≠ i + 1 := fun heq => hne (Fin.ext heq)
  exact Nat.lt_of_le_of_ne hle (Ne.symm hnej)

/-- Split round-`i` boolean tail into coordinate `i + 1` and round-`i + 1` boolean tail. -/
def splitTailStep {ℓ i : ℕ} (hi : i + 1 < ℓ) :
    ({j : Fin ℓ // (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin ℓ) < j} → Bool) ≃
      Bool × ({j : Fin ℓ // (⟨i + 1, hi⟩ : Fin ℓ) < j} → Bool) where
  toFun tail :=
    (tail ⟨⟨i + 1, hi⟩, Nat.lt_succ_self i⟩,
     fun j => tail ⟨j.1, lt_trans (Nat.lt_succ_self i) j.2⟩)
  invFun p j :=
    if h : j.1 = ⟨i + 1, hi⟩ then p.1
    else p.2 ⟨j.1, gt_succ_of_gt_ne hi j.2 h⟩
  left_inv tail := by
    funext j
    by_cases h : j.1 = ⟨i + 1, hi⟩
    · simp only [h, ↓reduceDIte]
      exact congrArg tail (Subtype.ext h.symm)
    · simp only [h, ↓reduceDIte]
  right_inv p := by
    rcases p with ⟨b, tail⟩
    refine Prod.ext (by simp) (funext fun j => ?_)
    have hne : j.1 ≠ ⟨i + 1, hi⟩ := ne_of_gt j.2
    simp only [hne, ↓reduceDIte]

/-- Round-`i+1` boolean endpoint sum equals round-`i` evaluated at `r_i`. -/
theorem roundSliceSum_step {R : Type*} [AddCommMonoid R] [Zero R] [One R] {ℓ : ℕ}
    (r : Fin ℓ → R) (f : (Fin ℓ → R) → R) {i : ℕ} (hi : i + 1 < ℓ) :
    roundSliceSum r f ⟨i + 1, hi⟩ 0 + roundSliceSum r f ⟨i + 1, hi⟩ 1 =
      roundSliceSum r f ⟨i, Nat.lt_of_succ_lt hi⟩ (r ⟨i, Nat.lt_of_succ_lt hi⟩) := by
  let cur : Fin ℓ := ⟨i, Nat.lt_of_succ_lt hi⟩
  let nxt : Fin ℓ := ⟨i + 1, hi⟩
  have hcur_lt_nxt : cur < nxt := Nat.lt_succ_self i
  have hpt : ∀ (b : Bool) (tail : {j : Fin ℓ // nxt < j} → Bool),
      slicePoint r cur (r cur) ((splitTailStep hi).symm (b, tail)) =
        slicePoint r nxt (bitVal b) tail := by
    intro b tail
    funext j
    by_cases hj_lt : j < cur
    · have hj_lt_nxt : j < nxt := lt_trans hj_lt hcur_lt_nxt
      rw [slicePoint_lt _ _ _ _ hj_lt, slicePoint_lt _ _ _ _ hj_lt_nxt]
    · by_cases hj_eq : j = cur
      · subst hj_eq
        rw [slicePoint_eq, slicePoint_lt _ _ _ _ hcur_lt_nxt]
      · have hcur_lt : cur < j := lt_of_le_of_ne (not_lt.mp hj_lt) (Ne.symm hj_eq)
        rw [slicePoint_gt _ _ _ _ hcur_lt]
        by_cases hjnxt : j = nxt
        · subst hjnxt
          simp [splitTailStep, nxt]
        · have hnxt_lt : nxt < j := gt_succ_of_gt_ne hi hcur_lt hjnxt
          rw [slicePoint_gt _ _ _ _ hnxt_lt]
          simp [splitTailStep, nxt, hjnxt]
  have hprod := Fintype.sum_prod_type
    (fun p : Bool × ({j : Fin ℓ // nxt < j} → Bool) =>
      f (slicePoint r cur (r cur) ((splitTailStep hi).symm p)))
  have hequiv := Fintype.sum_equiv (splitTailStep hi).symm
    (fun p : Bool × ({j : Fin ℓ // nxt < j} → Bool) =>
      f (slicePoint r cur (r cur) ((splitTailStep hi).symm p)))
    (fun tail : {j : Fin ℓ // cur < j} → Bool => f (slicePoint r cur (r cur) tail))
    (fun _ => rfl)
  calc
    roundSliceSum r f nxt 0 + roundSliceSum r f nxt 1
        = (∑ tail : ({j : Fin ℓ // nxt < j} → Bool),
            f (slicePoint r cur (r cur) ((splitTailStep hi).symm (false, tail)))) +
          (∑ tail : ({j : Fin ℓ // nxt < j} → Bool),
            f (slicePoint r cur (r cur) ((splitTailStep hi).symm (true, tail)))) := by
            simp only [roundSliceSum, hpt, bitVal_false, bitVal_true]
    _ = ∑ b : Bool, ∑ tail : ({j : Fin ℓ // nxt < j} → Bool),
          f (slicePoint r cur (r cur) ((splitTailStep hi).symm (b, tail))) := by
          rw [Fintype.sum_bool, add_comm]
    _ = ∑ p : Bool × ({j : Fin ℓ // nxt < j} → Bool),
          f (slicePoint r cur (r cur) ((splitTailStep hi).symm p)) := hprod.symm
    _ = roundSliceSum r f cur (r cur) := hequiv

/-- Final round `ℓ - 1` evaluated at `r_{ℓ - 1}` equals `f r`. -/
theorem roundSliceSum_terminal {R : Type*} [AddCommMonoid R] [Zero R] [One R] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (f : (Fin ℓ → R) → R) :
    roundSliceSum r f ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩ (r ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩) =
      f r := by
  let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
  have hempty : IsEmpty {j : Fin ℓ // last < j} := ⟨fun ⟨j, hj⟩ => by
    change ℓ - 1 < (j : ℕ) at hj
    have := j.isLt
    omega⟩
  let tail0 : {j : Fin ℓ // last < j} → Bool := fun j => hempty.elim j
  unfold roundSliceSum
  rw [Finset.sum_eq_single tail0]
  · congr 1
    funext j
    by_cases hj : j < last
    · exact slicePoint_lt r last (r last) tail0 hj
    · have hjeq : j = last := by
        apply Fin.ext
        have := j.isLt
        change ¬ (j : ℕ) < ℓ - 1 at hj
        change (j : ℕ) = ℓ - 1
        omega
      subst hjeq
      exact slicePoint_eq r last (r last) tail0
  · intro t _ hne
    exact False.elim (hne (funext fun j => hempty.elim j))
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ tail0))

/-- Honest round-`i` univariate polynomial of `P : TargetPoly ℓ d R` at challenge vector `r`. -/
def honestRoundPoly {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (P : TargetPoly ℓ d R) (i : Fin ℓ) : RoundPoly d R :=
  fun k =>
    ∑ tail : ({j : Fin ℓ // i < j} → Bool),
      ∑ e ∈ Finset.univ.filter (fun e : Fin ℓ → Fin (d + 1) => e i = k),
        P e * ∏ j ∈ Finset.univ.erase i, (slicePoint r i 0 tail j) ^ (e j : ℕ)

/-- Evaluating `honestRoundPoly r P i` at `x` reproduces `roundSliceSum r (evalTargetPoly P) i x`. -/
theorem eval_honestRoundPoly {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (P : TargetPoly ℓ d R) (i : Fin ℓ) (x : R) :
    evalRoundPoly (honestRoundPoly r P i) x =
      roundSliceSum r (evalTargetPoly P) i x := by
  unfold evalRoundPoly honestRoundPoly roundSliceSum evalTargetPoly
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun tail _ => ?_
  have hpart := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin (d + 1))))
    (t := (Finset.univ : Finset (Fin (d + 1))))
    (g := fun e => e i)
    (fun _ _ => Finset.mem_univ _)
    (fun e => P e * ∏ j : Fin ℓ, (slicePoint r i x tail j) ^ (e j : ℕ))
  refine Eq.trans ?_ hpart
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun e he => ?_
  have hei : e i = k := (Finset.mem_filter.mp he).2
  subst hei
  rw [mul_assoc]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (slicePoint r i x tail j) ^ (e j : ℕ))
    (Finset.mem_univ i)]
  rw [slicePoint_eq, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [slicePoint_ne r i 0 x tail (Finset.ne_of_mem_erase hj)]

/-! ### Separable Mask Space & Closed-Form Round-Mask Polynomials -/

/-- Space of `ℓ`-tuple univariate masking polynomials `g₀, …, g_{ℓ-1}` of degree `≤ d`. -/
abbrev MaskSpace (ℓ d : ℕ) (R : Type*) := Fin ℓ → RoundPoly d R

/-- Multivariate evaluation `g(x) = ∑_{j=0}^{ℓ-1} g_j(x_j)` of `g : MaskSpace ℓ d R`. -/
def evalMask {R : Type*} [Semiring R] {ℓ d : ℕ} (g : MaskSpace ℓ d R) (x : Fin ℓ → R) : R :=
  ∑ j : Fin ℓ, evalRoundPoly (g j) (x j)

/-- Canonical `R`-linear embedding of `MaskSpace ℓ d R` into Mathlib's `MvPolynomial (Fin ℓ) R`. -/
noncomputable def separableMaskToMvPolynomial {R : Type*} [CommSemiring R] {ℓ d : ℕ} :
    MaskSpace ℓ d R →ₗ[R] MvPolynomial (Fin ℓ) R where
  toFun g :=
    ∑ j : Fin ℓ, ∑ k : Fin (d + 1),
      MvPolynomial.C (g j k) * MvPolynomial.X j ^ (k : ℕ)
  map_add' g₁ g₂ := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change MvPolynomial.C (c * g j k) * _ = _
    rw [map_mul, mul_assoc, MvPolynomial.C_mul']

@[simp] theorem eval_separableMaskToMvPolynomial {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (g : MaskSpace ℓ d R) (x : Fin ℓ → R) :
    MvPolynomial.eval x (separableMaskToMvPolynomial g) = evalMask g x := by
  simp [separableMaskToMvPolynomial, evalMask, evalRoundPoly, map_sum, map_mul, map_pow]

theorem cubeSum_evalMask_eq {R : Type*} [Ring R] {ℓ d : ℕ} (hℓ : 1 ≤ ℓ)
    (g : MaskSpace ℓ d R) :
    cubeSum (evalMask g) =
      (2 : R) ^ ℓ * (∑ j : Fin ℓ, g j 0) +
      (2 : R) ^ (ℓ - 1) * ∑ j : Fin ℓ, ∑ k : Fin d, g j k.succ := by
  have h1 := cubeSum_separableFun_eq (fun j y => evalRoundPoly (g j) y)
  change cubeSum (evalMask g) = _ at h1
  rw [h1]
  have hsplit : (∑ j : Fin ℓ, (evalRoundPoly (g j) 0 + evalRoundPoly (g j) 1)) =
      2 * (∑ j : Fin ℓ, g j 0) + ∑ j : Fin ℓ, ∑ k : Fin d, g j k.succ := by
    simp_rw [evalRoundPoly_zero_add_one]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit, mul_add, ← mul_assoc]
  have hpow : (2 : R) ^ (ℓ - 1) * 2 = (2 : R) ^ ℓ := by
    rw [← pow_succ, Nat.sub_add_cancel hℓ]
  rw [hpow]

/-- Closed-form round-`i` polynomial of the separable mask `g` under challenge vector `r`:
`2^{ℓ - 1 - i} (∑_{j < i} g_j(r_j) + g_i(X)) + 2^{ℓ - 2 - i} ∑_{j > i} (g_j(0) + g_j(1))`. -/
def maskRoundPoly {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (g : MaskSpace ℓ d R) (i : Fin ℓ) : RoundPoly d R :=
  fun k =>
    if k = 0 then
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) *
        (g i 0 + ∑ j ∈ Finset.univ.filter (· < i), evalRoundPoly (g j) (r j)) +
      (2 : R) ^ (ℓ - 2 - (i : ℕ)) *
        (∑ j ∈ Finset.univ.filter (i < ·), (evalRoundPoly (g j) 0 + evalRoundPoly (g j) 1))
    else
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) * g i k

@[simp] theorem maskRoundPoly_succ {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (g : MaskSpace ℓ d R) (i : Fin ℓ) (k : Fin d) :
    maskRoundPoly r g i k.succ = (2 : R) ^ (ℓ - 1 - (i : ℕ)) * g i k.succ := by
  simp [maskRoundPoly, Fin.succ_ne_zero]

theorem card_gt_fin {ℓ : ℕ} (i : Fin ℓ) :
    Fintype.card {j : Fin ℓ // i < j} = ℓ - 1 - (i : ℕ) := by
  have heq : (Finset.univ.filter (fun j : Fin ℓ => i < j)).card =
      (Finset.Ioi i).card := by
    congr 1; ext j; simp
  rw [Fintype.card_subtype, heq, Fin.card_Ioi]

/-- Evaluating `maskRoundPoly r g i` at `x` equals `roundSliceSum r (evalMask g) i x`. -/
theorem eval_maskRoundPoly {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (g : MaskSpace ℓ d R) (i : Fin ℓ) (x : R) :
    evalRoundPoly (maskRoundPoly r g i) x = roundSliceSum r (evalMask g) i x := by
  have hevalSplit : ∀ p : RoundPoly d R,
      evalRoundPoly p x = p 0 + ∑ k : Fin d, p k.succ * x ^ (k.succ : ℕ) := by
    intro p
    unfold evalRoundPoly
    rw [Fin.sum_univ_succ]
    simp
  have hlhs : evalRoundPoly (maskRoundPoly r g i) x =
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) * evalRoundPoly (g i) x +
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) *
        (∑ j ∈ Finset.univ.filter (· < i), evalRoundPoly (g j) (r j)) +
      (2 : R) ^ (ℓ - 2 - (i : ℕ)) *
        (∑ j ∈ Finset.univ.filter (i < ·), (evalRoundPoly (g j) 0 + evalRoundPoly (g j) 1)) := by
    rw [hevalSplit (maskRoundPoly r g i), hevalSplit (g i)]
    have h0 : maskRoundPoly r g i 0 =
        (2 : R) ^ (ℓ - 1 - (i : ℕ)) *
          (g i 0 + ∑ j ∈ Finset.univ.filter (· < i), evalRoundPoly (g j) (r j)) +
        (2 : R) ^ (ℓ - 2 - (i : ℕ)) *
          (∑ j ∈ Finset.univ.filter (i < ·), (evalRoundPoly (g j) 0 + evalRoundPoly (g j) 1)) := by
      simp [maskRoundPoly]
    have hmul : ∑ k : Fin d, maskRoundPoly r g i k.succ * x ^ (k.succ : ℕ) =
        (2 : R) ^ (ℓ - 1 - (i : ℕ)) * ∑ k : Fin d, g i k.succ * x ^ (k.succ : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [maskRoundPoly_succ, mul_assoc]
    rw [h0, hmul]
    ring
  -- Evaluate RHS by splitting `j < i`, `j = i`, `i < j`
  unfold roundSliceSum evalMask
  rw [Finset.sum_comm]
  have hsplitJ : ∀ f : Fin ℓ → R,
      (∑ j : Fin ℓ, f j) =
        f i + (∑ j ∈ Finset.univ.filter (· < i), f j) +
          (∑ j ∈ Finset.univ.filter (i < ·), f j) := by
    intro f
    have hdisj1 : Disjoint (Finset.univ.filter (fun j : Fin ℓ => j < i))
        (Finset.univ.filter (fun j : Fin ℓ => i < j)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2; exact lt_asymm h1 h2
    have hunion : (Finset.univ : Finset (Fin ℓ)) =
        insert i (Finset.univ.filter (· < i) ∪ Finset.univ.filter (i < ·)) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        true_and, true_iff]
      rcases lt_trichotomy j i with h | rfl | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
    have hnotmem : i ∉ Finset.univ.filter (· < i) ∪ Finset.univ.filter (i < ·) := by
      simp
    conv_lhs => rw [hunion]
    rw [Finset.sum_insert hnotmem, Finset.sum_union hdisj1, add_assoc]
  rw [hsplitJ]
  have h_eq : (∑ tail : ({k : Fin ℓ // i < k} → Bool),
      evalRoundPoly (g i) (slicePoint r i x tail i)) =
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) * evalRoundPoly (g i) x := by
    simp only [slicePoint_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_bool, card_gt_fin, Nat.cast_pow, Nat.cast_ofNat]
  have h_lt : (∑ j ∈ Finset.univ.filter (· < i),
      ∑ tail : ({k : Fin ℓ // i < k} → Bool),
        evalRoundPoly (g j) (slicePoint r i x tail j)) =
      (2 : R) ^ (ℓ - 1 - (i : ℕ)) *
        ∑ j ∈ Finset.univ.filter (· < i), evalRoundPoly (g j) (r j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < i := (Finset.mem_filter.mp hj).2
    simp only [slicePoint_lt _ _ _ _ hjlt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fun, Fintype.card_bool, card_gt_fin, Nat.cast_pow, Nat.cast_ofNat]
  have h_gt : (∑ j ∈ Finset.univ.filter (i < ·),
      ∑ tail : ({k : Fin ℓ // i < k} → Bool),
        evalRoundPoly (g j) (slicePoint r i x tail j)) =
      (2 : R) ^ (ℓ - 2 - (i : ℕ)) *
        ∑ j ∈ Finset.univ.filter (i < ·), (evalRoundPoly (g j) 0 + evalRoundPoly (g j) 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjgt : i < j := (Finset.mem_filter.mp hj).2
    have hsub := sum_boolCube_singleCoord (⟨j, hjgt⟩ : {k : Fin ℓ // i < k}) (evalRoundPoly (g j))
    rw [card_gt_fin i] at hsub
    have hexp : ℓ - 1 - (i : ℕ) - 1 = ℓ - 2 - (i : ℕ) := by omega
    rw [hexp] at hsub
    simpa [hjgt] using hsub
  rw [hlhs, h_eq, h_lt, h_gt]

/-- **Characteristic-2 Non-Final Positive-Degree Collapse
(`charTwo_maskRoundPoly_posCoeff_eq_zero_of_lt_last`):**
in characteristic `2`, at **every** non-final round `i` (`i + 1 < ℓ`), *every* positive-degree
coefficient `k.succ` of `maskRoundPoly r g i` vanishes (`2^{ℓ - 1 - i} = 0`) — only the final round
`i = ℓ - 1` ever masks positive-degree coefficients! -/
theorem charTwo_maskRoundPoly_posCoeff_eq_zero_of_lt_last
    {R : Type*} [CommRing R] [CharP R 2] {ℓ d : ℕ}
    (r : Fin ℓ → R) (g : MaskSpace ℓ d R) (i : Fin ℓ) (hi : (i : ℕ) + 1 < ℓ) (k : Fin d) :
    maskRoundPoly r g i k.succ = 0 := by
  have hpos : ℓ - 1 - (i : ℕ) ≠ 0 := by omega
  rw [maskRoundPoly_succ, CharTwo.two_eq_zero, zero_pow hpos, zero_mul]

/-- **Characteristic-2 Penultimate-Round Constant Collapse (`charTwo_maskRoundPoly_penultimate_const`):**
for `ℓ ≥ 2` in characteristic `2`, at penultimate round `i = ℓ - 2` (in particular round `0` at
`ℓ = 2`!), `maskRoundPoly r g ⟨ℓ - 2, _⟩` is a **constant polynomial** equal to
`g_{ℓ-1}(0) + g_{ℓ-1}(1)` with `0` in all positive degrees. -/
theorem charTwo_maskRoundPoly_penultimate_const {R : Type*} [CommRing R] [CharP R 2] {ℓ d : ℕ}
    (hℓ : 2 ≤ ℓ) (r : Fin ℓ → R) (g : MaskSpace ℓ d R) :
    let penult : Fin ℓ := ⟨ℓ - 2, by omega⟩
    let last : Fin ℓ := ⟨ℓ - 1, by omega⟩
    maskRoundPoly r g penult 0 = evalRoundPoly (g last) 0 + evalRoundPoly (g last) 1 ∧
    ∀ k : Fin d, maskRoundPoly r g penult k.succ = 0 := by
  intro penult last
  refine ⟨?_, fun k => charTwo_maskRoundPoly_posCoeff_eq_zero_of_lt_last r g penult (by
    change ℓ - 2 + 1 < ℓ; omega) k⟩
  have h1 : ℓ - 1 - (penult : ℕ) = 1 := by change ℓ - 1 - (ℓ - 2) = 1; omega
  have h2 : ℓ - 2 - (penult : ℕ) = 0 := by change ℓ - 2 - (ℓ - 2) = 0; omega
  have hflt : Finset.univ.filter (fun j : Fin ℓ => penult < j) = {last} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
      Fin.lt_def, penult, last]
    have := j.isLt
    omega
  simp only [maskRoundPoly, ↓reduceIte, h1, h2, pow_one, pow_zero, CharTwo.two_eq_zero, zero_mul,
    zero_add, one_mul, hflt, Finset.sum_singleton]

/-- **Characteristic-2 Early-Round Total Collapse (`charTwo_maskRoundPoly_eq_zero_of_lt`):**
in characteristic `2`, for every round `i` with `i + 2 < ℓ` (`ℓ - 2 - i ≥ 1`), the entire round-`i`
mask polynomial `maskRoundPoly r g i` is **identically `0`** (`0` in every coefficient!), so even
blinding the initial claimed sum with an extra scalar `G₀` leaves early sumcheck rounds unmasked. -/
theorem charTwo_maskRoundPoly_eq_zero_of_lt {R : Type*} [CommRing R] [CharP R 2] {ℓ d : ℕ}
    (r : Fin ℓ → R) (g : MaskSpace ℓ d R) (i : Fin ℓ) (hi : (i : ℕ) + 2 < ℓ) :
    maskRoundPoly r g i = 0 := by
  funext k
  have h1 : ℓ - 1 - (i : ℕ) ≠ 0 := by omega
  have h2 : ℓ - 2 - (i : ℕ) ≠ 0 := by omega
  unfold maskRoundPoly
  split_ifs <;> simp [CharTwo.two_eq_zero, zero_pow h1, zero_pow h2]

/-! ### Sum-Consistent Transcript Submodule & Explicit `LinearEquiv` Fiber Decomposition -/

/-- Raw interactive sumcheck transcript `(claimedSum, s₀, …, s_{ℓ-1})`. -/
abbrev RawTranscript (ℓ d : ℕ) (R : Type*) := R × (Fin ℓ → RoundPoly d R)

/-- Sum-consistency equations on `(claimedSum, s₀, …, s_{ℓ-1})`:
`s₀(0) + s₀(1) = claimedSum` and `s_{i+1}(0) + s_{i+1}(1) = s_i(r_i)` for all `i + 1 < ℓ`. -/
def IsSumConsistent {R : Type*} [Semiring R] {ℓ d : ℕ} (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → R) (tr : RawTranscript ℓ d R) : Prop :=
  evalRoundPoly (tr.2 ⟨0, hℓ⟩) 0 + evalRoundPoly (tr.2 ⟨0, hℓ⟩) 1 = tr.1 ∧
  ∀ (i : ℕ) (hi : i + 1 < ℓ),
    evalRoundPoly (tr.2 ⟨i + 1, hi⟩) 0 + evalRoundPoly (tr.2 ⟨i + 1, hi⟩) 1 =
      evalRoundPoly (tr.2 ⟨i, Nat.lt_of_succ_lt hi⟩) (r ⟨i, Nat.lt_of_succ_lt hi⟩)

instance instDecidableIsSumConsistent {R : Type*} [Semiring R] [DecidableEq R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (tr : RawTranscript ℓ d R) :
    Decidable (IsSumConsistent hℓ r tr) := by
  unfold IsSumConsistent
  have hconv : (∀ (i : ℕ) (hi : i + 1 < ℓ),
      evalRoundPoly (tr.2 ⟨i + 1, hi⟩) 0 + evalRoundPoly (tr.2 ⟨i + 1, hi⟩) 1 =
        evalRoundPoly (tr.2 ⟨i, Nat.lt_of_succ_lt hi⟩) (r ⟨i, Nat.lt_of_succ_lt hi⟩)) ↔
      ∀ idx : Fin (ℓ - 1),
        evalRoundPoly (tr.2 ⟨idx.1 + 1, by omega⟩) 0 +
          evalRoundPoly (tr.2 ⟨idx.1 + 1, by omega⟩) 1 =
          evalRoundPoly (tr.2 ⟨idx.1, by omega⟩) (r ⟨idx.1, by omega⟩) := by
    constructor
    · intro h idx; exact h idx.1 (by omega)
    · intro h i hi; exact h ⟨i, by omega⟩
  exact decidable_of_iff
    (evalRoundPoly (tr.2 ⟨0, hℓ⟩) 0 + evalRoundPoly (tr.2 ⟨0, hℓ⟩) 1 = tr.1 ∧
      ∀ idx : Fin (ℓ - 1),
        evalRoundPoly (tr.2 ⟨idx.1 + 1, by omega⟩) 0 +
          evalRoundPoly (tr.2 ⟨idx.1 + 1, by omega⟩) 1 =
          evalRoundPoly (tr.2 ⟨idx.1, by omega⟩) (r ⟨idx.1, by omega⟩))
    (and_congr_right fun _ => hconv.symm)

/-- Submodule of sum-consistent interactive sumcheck transcripts. -/
def ConsistentTranscript {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) : Submodule R (RawTranscript ℓ d R) where
  carrier := {tr | IsSumConsistent hℓ r tr}
  zero_mem' := by
    refine ⟨by simp, fun i hi => by simp⟩
  add_mem' {u v} hu hv := by
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, evalRoundPoly_add]
      calc (evalRoundPoly (u.2 ⟨0, hℓ⟩) 0 + evalRoundPoly (v.2 ⟨0, hℓ⟩) 0) +
           (evalRoundPoly (u.2 ⟨0, hℓ⟩) 1 + evalRoundPoly (v.2 ⟨0, hℓ⟩) 1)
          = (evalRoundPoly (u.2 ⟨0, hℓ⟩) 0 + evalRoundPoly (u.2 ⟨0, hℓ⟩) 1) +
            (evalRoundPoly (v.2 ⟨0, hℓ⟩) 0 + evalRoundPoly (v.2 ⟨0, hℓ⟩) 1) := by ac_rfl
        _ = u.1 + v.1 := by rw [hu.1, hv.1]
    · simp only [Prod.snd_add, Pi.add_apply, evalRoundPoly_add]
      calc (evalRoundPoly (u.2 ⟨i + 1, hi⟩) 0 + evalRoundPoly (v.2 ⟨i + 1, hi⟩) 0) +
           (evalRoundPoly (u.2 ⟨i + 1, hi⟩) 1 + evalRoundPoly (v.2 ⟨i + 1, hi⟩) 1)
          = (evalRoundPoly (u.2 ⟨i + 1, hi⟩) 0 + evalRoundPoly (u.2 ⟨i + 1, hi⟩) 1) +
            (evalRoundPoly (v.2 ⟨i + 1, hi⟩) 0 + evalRoundPoly (v.2 ⟨i + 1, hi⟩) 1) := by ac_rfl
        _ = _ := by rw [hu.2 i hi, hv.2 i hi]
  smul_mem' c {u} hu := by
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, evalRoundPoly_smul, smul_eq_mul,
        ← mul_add, hu.1]
    · simp only [Prod.smul_snd, Pi.smul_apply, evalRoundPoly_smul, ← mul_add, hu.2 i hi]

instance instFintypeConsistentTranscript {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) :
    Fintype (ConsistentTranscript hℓ r (d := d)) :=
  Subtype.fintype (fun tr => IsSumConsistent hℓ r tr)

/-- Unmasked honest transcript `(cubeSum P, P₀(X), …, P_{ℓ-1}(X))` of `P : TargetPoly ℓ d R`. -/
def honestTranscript {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (P : TargetPoly ℓ d R) : RawTranscript ℓ d R :=
  (cubeSum (evalTargetPoly P), honestRoundPoly r P)

theorem honestTranscript_mem_consistent {R : Type*} [CommSemiring R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (P : TargetPoly ℓ d R) :
    honestTranscript r P ∈ ConsistentTranscript hℓ r := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [honestTranscript, eval_honestRoundPoly]
    exact roundSliceSum_zero hℓ r (evalTargetPoly P)
  · simp only [honestTranscript, eval_honestRoundPoly]
    exact roundSliceSum_step r (evalTargetPoly P) hi

/-- Linear map sending a separable mask `g : MaskSpace ℓ d R` to its raw sumcheck transcript. -/
def maskToRawTranscript {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) : MaskSpace ℓ d R →ₗ[R] RawTranscript ℓ d R where
  toFun g := (cubeSum (evalMask g), maskRoundPoly r g)
  map_add' g₁ g₂ := by
    ext
    · simp only [Prod.fst_add, cubeSum, evalMask, Pi.add_apply, evalRoundPoly_add,
        Finset.sum_add_distrib]
    · rename_i i k
      simp only [Prod.snd_add, Pi.add_apply, maskRoundPoly]
      split_ifs with hk
      · simp only [evalRoundPoly_add, Finset.sum_add_distrib]
        ring
      · ring
  map_smul' c g := by
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, RingHom.id_apply, cubeSum, evalMask, Pi.smul_apply,
        evalRoundPoly_smul, ← Finset.mul_sum]
    · rename_i i k
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, maskRoundPoly]
      split_ifs with hk
      · simp only [evalRoundPoly_smul, ← mul_add, ← Finset.mul_sum]
        ring
      · ring

theorem maskToRawTranscript_mem_consistent {R : Type*} [CommRing R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (g : MaskSpace ℓ d R) :
    maskToRawTranscript r g ∈ ConsistentTranscript (d := d) hℓ r := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [maskToRawTranscript, LinearMap.coe_mk, AddHom.coe_mk, eval_maskRoundPoly]
    exact roundSliceSum_zero hℓ r (evalMask g)
  · simp only [maskToRawTranscript, LinearMap.coe_mk, AddHom.coe_mk, eval_maskRoundPoly]
    exact roundSliceSum_step r (evalMask g) hi

/-- Mask-to-view linear map restricted to its target `ConsistentTranscript hℓ r`. -/
def maskToConsistentTranscript {R : Type*} [CommRing R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) :
    MaskSpace ℓ d R →ₗ[R] ConsistentTranscript (d := d) hℓ r :=
  (maskToRawTranscript r).codRestrict (ConsistentTranscript (d := d) hℓ r)
    (maskToRawTranscript_mem_consistent hℓ r)

/-- Masked interactive sumcheck transcript `honestTranscript r P + maskToRawTranscript r g`. -/
def maskedTranscript {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (P : TargetPoly ℓ d R) (g : MaskSpace ℓ d R) : RawTranscript ℓ d R :=
  honestTranscript r P + maskToRawTranscript r g

theorem maskedTranscript_mem_consistent {R : Type*} [CommRing R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (P : TargetPoly ℓ d R) (g : MaskSpace ℓ d R) :
    maskedTranscript r P g ∈ ConsistentTranscript hℓ r :=
  Submodule.add_mem _ (honestTranscript_mem_consistent hℓ r P)
    (maskToRawTranscript_mem_consistent hℓ r g)

/-- Terminal opening identity: at the last round `ℓ - 1`, evaluating `s_{ℓ-1}` at `r_{ℓ-1}` equals
`P(r) + g(r)` identically for every target `P` and mask `g`. -/
theorem maskedTranscript_terminal_eval {R : Type*} [CommRing R] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → R) (P : TargetPoly ℓ d R) (g : MaskSpace ℓ d R) :
    let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
    evalRoundPoly ((maskedTranscript r P g).2 last) (r last) =
      evalTargetPoly P r + evalMask g r := by
  intro last
  simp only [maskedTranscript, honestTranscript, maskToRawTranscript, Prod.snd_add, Pi.add_apply,
    LinearMap.coe_mk, AddHom.coe_mk, evalRoundPoly_add, eval_honestRoundPoly, eval_maskRoundPoly]
  rw [roundSliceSum_terminal hℓ r (evalTargetPoly P), roundSliceSum_terminal hℓ r (evalMask g)]

/-- **Key odd-characteristic uniqueness lemma:** when `(2 : F) ≠ 0`, two sum-consistent transcripts
agreeing on `claimedSum` and all positive-degree coefficients `k.succ` are **equal**. -/
theorem eq_of_consistentTranscript_tail_eq {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F)
    {u v : ConsistentTranscript (d := d) hℓ r}
    (hsum : u.1.1 = v.1.1)
    (htail : ∀ (i : Fin ℓ) (k : Fin d), u.1.2 i k.succ = v.1.2 i k.succ) :
    u = v := by
  apply Subtype.ext
  refine Prod.ext hsum ?_
  have hround : ∀ (n : ℕ) (hn : n < ℓ), u.1.2 ⟨n, hn⟩ = v.1.2 ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hu0 := u.2.1
        have hv0 := v.2.1
        have hchange : (⟨0, hn⟩ : Fin ℓ) = ⟨0, hℓ⟩ := rfl
        rw [← hchange, evalRoundPoly_zero_add_one] at hu0 hv0
        have htsum : (∑ k : Fin d, u.1.2 ⟨0, hn⟩ k.succ) =
            (∑ k : Fin d, v.1.2 ⟨0, hn⟩ k.succ) :=
          Finset.sum_congr rfl fun k _ => htail ⟨0, hn⟩ k
        have h2eq : 2 * u.1.2 ⟨0, hn⟩ 0 = 2 * v.1.2 ⟨0, hn⟩ 0 := by
          apply add_right_cancel (b := ∑ k : Fin d, v.1.2 ⟨0, hn⟩ k.succ)
          rw [← htsum, hu0, hsum, ← hv0, htsum]
        have h0eq : u.1.2 ⟨0, hn⟩ 0 = v.1.2 ⟨0, hn⟩ 0 := mul_left_cancel₀ h2 h2eq
        funext k
        refine Fin.cases h0eq (fun k' => htail ⟨0, hn⟩ k') k
    | succ m ih =>
        intro hn
        have hm : m < ℓ := Nat.lt_of_succ_lt hn
        have ihm := ih hm
        have hus := u.2.2 m hn
        have hvs := v.2.2 m hn
        rw [evalRoundPoly_zero_add_one] at hus hvs
        rw [ihm] at hus
        have htsum : (∑ k : Fin d, u.1.2 ⟨m + 1, hn⟩ k.succ) =
            (∑ k : Fin d, v.1.2 ⟨m + 1, hn⟩ k.succ) :=
          Finset.sum_congr rfl fun k _ => htail ⟨m + 1, hn⟩ k
        have h2eq : 2 * u.1.2 ⟨m + 1, hn⟩ 0 = 2 * v.1.2 ⟨m + 1, hn⟩ 0 := by
          apply add_right_cancel (b := ∑ k : Fin d, v.1.2 ⟨m + 1, hn⟩ k.succ)
          rw [← htsum, hus, ← hvs, htsum]
        have h0eq : u.1.2 ⟨m + 1, hn⟩ 0 = v.1.2 ⟨m + 1, hn⟩ 0 := mul_left_cancel₀ h2 h2eq
        funext k
        refine Fin.cases h0eq (fun k' => htail ⟨m + 1, hn⟩ k') k
  funext i
  exact hround i.1 i.2

/-- Recursive builder reconstructing the unique sum-consistent transcript from `(claimedSum, tails)`
when `(2 : F) ≠ 0`. -/
noncomputable def buildConsistentRounds {F : Type*} [Field F] {ℓ d : ℕ}
    (r : Fin ℓ → F) (claimedSum : F) (tails : Fin ℓ → Fin d → F) :
    (n : ℕ) → n < ℓ → RoundPoly d F
  | 0, hn =>
      let i0 : Fin ℓ := ⟨0, hn⟩
      Fin.cases ((2 : F)⁻¹ * (claimedSum - ∑ k : Fin d, tails i0 k)) (tails i0)
  | m + 1, hn =>
      let prev := buildConsistentRounds r claimedSum tails m (Nat.lt_of_succ_lt hn)
      let cur : Fin ℓ := ⟨m + 1, hn⟩
      Fin.cases
        ((2 : F)⁻¹ * (evalRoundPoly prev (r ⟨m, Nat.lt_of_succ_lt hn⟩) -
          ∑ k : Fin d, tails cur k))
        (tails cur)

theorem buildConsistentRounds_succ_coeff {F : Type*} [Field F] {ℓ d : ℕ}
    (r : Fin ℓ → F) (claimedSum : F) (tails : Fin ℓ → Fin d → F)
    (n : ℕ) (hn : n < ℓ) (k : Fin d) :
    buildConsistentRounds r claimedSum tails n hn k.succ = tails ⟨n, hn⟩ k := by
  cases n with
  | zero => simp [buildConsistentRounds]
  | succ m => simp [buildConsistentRounds]

/-- Free parameter `LinearEquiv` for `ConsistentTranscript hℓ r ≃ₗ[F] F × (Fin ℓ → Fin d → F)`
in characteristic `≠ 2`, proving exact dimension `ℓ d + 1`. -/
noncomputable def consistentTranscriptParamEquiv {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) :
    ConsistentTranscript (d := d) hℓ r ≃ₗ[F] F × (Fin ℓ → Fin d → F) := by
  let fwd : ConsistentTranscript (d := d) hℓ r →ₗ[F] F × (Fin ℓ → Fin d → F) :=
    { toFun := fun v => (v.1.1, fun i k => v.1.2 i k.succ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem : ∀ (cs : F) (tails : Fin ℓ → Fin d → F),
      IsSumConsistent hℓ r (cs, fun i => buildConsistentRounds r cs tails i.1 i.2) := by
    intro cs tails
    refine ⟨?_, fun m hm => ?_⟩
    · simp only [evalRoundPoly_zero_add_one, buildConsistentRounds, Fin.cases_zero, Fin.cases_succ]
      field_simp [h2]; ring
    · simp only [evalRoundPoly_zero_add_one, buildConsistentRounds, Fin.cases_zero, Fin.cases_succ]
      field_simp [h2]; ring
  let bwdFun : F × (Fin ℓ → Fin d → F) → ConsistentTranscript (d := d) hℓ r :=
    fun p => ⟨(p.1, fun i => buildConsistentRounds r p.1 p.2 i.1 i.2), hmem p.1 p.2⟩
  have hbwd_left : ∀ v : ConsistentTranscript (d := d) hℓ r, bwdFun (fwd v) = v := by
    intro v
    refine eq_of_consistentTranscript_tail_eq h2 hℓ r rfl (fun i k => ?_)
    exact buildConsistentRounds_succ_coeff r v.1.1 (fun j k' => v.1.2 j k'.succ) i.1 i.2 k
  have hbwd_right : ∀ p : F × (Fin ℓ → Fin d → F), fwd (bwdFun p) = p := by
    intro ⟨cs, tails⟩
    ext
    · rfl
    · rename_i i k
      exact buildConsistentRounds_succ_coeff r cs tails i.1 i.2 k
  exact LinearEquiv.ofBijective fwd ⟨Function.LeftInverse.injective hbwd_left,
    Function.RightInverse.surjective hbwd_right⟩

/-- Exact cardinality of `ConsistentTranscript hℓ r` over a finite field of characteristic `≠ 2`:
`|ConsistentTranscript| = |F|^{ℓ d + 1}`. -/
theorem card_consistentTranscript {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) :
    Fintype.card (ConsistentTranscript (d := d) hℓ r) = Fintype.card F ^ (ℓ * d + 1) := by
  rw [Fintype.card_congr (consistentTranscriptParamEquiv h2 hℓ r).toEquiv]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_mul, pow_add, pow_one,
    mul_comm (Fintype.card F), mul_comm d ℓ]

/-- Right-inverse mask constructor from `(v, slack) : ConsistentTranscript hℓ r × (Fin (ℓ - 1) → F)`. -/
noncomputable def maskFromTranscriptAndSlack {F : Type*} [Field F] {ℓ d : ℕ}
    (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F)
    (v : ConsistentTranscript (d := d) hℓ r) (slack : Fin (ℓ - 1) → F) :
    MaskSpace ℓ d F :=
  let posCoeff : Fin ℓ → Fin d → F :=
    fun i k => ((2 : F) ^ (ℓ - 1 - (i : ℕ)))⁻¹ * v.1.2 i k.succ
  let totalConst : F :=
    ((2 : F) ^ ℓ)⁻¹ *
      (v.1.1 - (2 : F) ^ (ℓ - 1) * ∑ j : Fin ℓ, ∑ k : Fin d, posCoeff j k)
  fun j =>
    Fin.cases
      (if hj : (j : ℕ) = 0 then
        totalConst - ∑ s : Fin (ℓ - 1), slack s
       else
        slack ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
      (posCoeff j)

/-- **Master Linear Equivalence (`maskTranscriptLinearEquiv`):**
over any `[Field F]` with `(2 : F) ≠ 0` and `ℓ ≥ 1`, `MaskSpace ℓ d F` decomposes canonically via
an `F`-linear isomorphism into `ConsistentTranscript hℓ r × (Fin (ℓ - 1) → F)` whose first
projection is literally `maskToConsistentTranscript hℓ r`. -/
noncomputable def maskTranscriptLinearEquiv {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) :
    MaskSpace ℓ d F ≃ₗ[F] ConsistentTranscript (d := d) hℓ r × (Fin (ℓ - 1) → F) := by
  let fwd : MaskSpace ℓ d F →ₗ[F] ConsistentTranscript (d := d) hℓ r × (Fin (ℓ - 1) → F) :=
    { toFun := fun g =>
        (maskToConsistentTranscript hℓ r g,
         fun s : Fin (ℓ - 1) => g ⟨s.1 + 1, by omega⟩ 0)
      map_add' := fun g₁ g₂ =>
        Prod.ext (map_add (maskToConsistentTranscript hℓ r) g₁ g₂) rfl
      map_smul' := fun c g =>
        Prod.ext (map_smul (maskToConsistentTranscript hℓ r) c g) rfl }
  let bwd : ConsistentTranscript (d := d) hℓ r × (Fin (ℓ - 1) → F) → MaskSpace ℓ d F :=
    fun p => maskFromTranscriptAndSlack hℓ r p.1 p.2
  have hsum_const : ∀ (tc : F) (slack : Fin (ℓ - 1) → F),
      (∑ j : Fin ℓ,
        (if hj : (j : ℕ) = 0 then tc - ∑ s : Fin (ℓ - 1), slack s
         else slack ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)) = tc := by
    intro tc slack
    cases ℓ with
    | zero => omega
    | succ m =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, ↓reduceDIte, Fin.val_succ, Nat.succ_ne_zero,
          Nat.add_sub_cancel]
        have hreindex : (∑ x : Fin m, slack ⟨(x : ℕ), by omega⟩) = ∑ s : Fin m, slack s :=
          Finset.sum_congr rfl fun x _ => rfl
        rw [hreindex]
        change tc - (∑ s : Fin m, slack s) + (∑ s : Fin m, slack s) = tc
        exact sub_add_cancel tc _
  have hright : ∀ p : ConsistentTranscript (d := d) hℓ r × (Fin (ℓ - 1) → F),
      fwd (bwd p) = p := by
    rintro ⟨v, slack⟩
    refine Prod.ext ?_ ?_
    · refine eq_of_consistentTranscript_tail_eq h2 hℓ r ?_ ?_
      · -- `claimedSum` matches `v.1.1`
        change cubeSum (evalMask (maskFromTranscriptAndSlack hℓ r v slack)) = v.1.1
        rw [cubeSum_evalMask_eq hℓ]
        simp only [maskFromTranscriptAndSlack, Fin.cases_zero, Fin.cases_succ]
        rw [hsum_const]
        have h2pow : (2 : F) ^ ℓ ≠ 0 := pow_ne_zero ℓ h2
        rw [mul_inv_cancel_left₀ h2pow]
        ring
      · -- positive-degree coefficients `k.succ` match `v.1.2 i k.succ`
        intro i k
        change maskRoundPoly r (maskFromTranscriptAndSlack hℓ r v slack) i k.succ =
          v.1.2 i k.succ
        rw [maskRoundPoly_succ]
        simp only [maskFromTranscriptAndSlack, Fin.cases_succ]
        exact mul_inv_cancel_left₀ (pow_ne_zero _ h2) _
    · funext s
      simp [fwd, bwd, maskFromTranscriptAndSlack]
  have hleft : ∀ g : MaskSpace ℓ d F, bwd (fwd g) = g := by
    intro g
    funext j k
    refine Fin.cases ?_ (fun k' => ?_) k
    · -- constant term `k = 0`
      simp only [bwd, fwd, LinearMap.coe_mk, AddHom.coe_mk, maskFromTranscriptAndSlack,
        Fin.cases_zero]
      have hpos_cancel : ∀ (i : Fin ℓ) (k' : Fin d),
          ((2 : F) ^ (ℓ - 1 - (i : ℕ)))⁻¹ *
            (maskToConsistentTranscript hℓ r g).1.2 i k'.succ = g i k'.succ := by
        intro i k'
        change ((2 : F) ^ (ℓ - 1 - (i : ℕ)))⁻¹ * maskRoundPoly r g i k'.succ = g i k'.succ
        rw [maskRoundPoly_succ]
        exact inv_mul_cancel_left₀ (pow_ne_zero _ h2) _
      have htc : ((2 : F) ^ ℓ)⁻¹ *
          ((maskToConsistentTranscript hℓ r g).1.1 -
            (2 : F) ^ (ℓ - 1) * ∑ i : Fin ℓ, ∑ k' : Fin d,
              ((2 : F) ^ (ℓ - 1 - (i : ℕ)))⁻¹ *
                (maskToConsistentTranscript hℓ r g).1.2 i k'.succ) =
          ∑ i : Fin ℓ, g i 0 := by
        simp_rw [hpos_cancel]
        change ((2 : F) ^ ℓ)⁻¹ *
          (cubeSum (evalMask g) - (2 : F) ^ (ℓ - 1) * ∑ i : Fin ℓ, ∑ k' : Fin d, g i k'.succ) = _
        rw [cubeSum_evalMask_eq hℓ g, add_sub_cancel_right]
        exact inv_mul_cancel_left₀ (pow_ne_zero ℓ h2) _
      rw [htc]
      by_cases hj : (j : ℕ) = 0
      · simp only [hj, ↓reduceDIte]
        cases ℓ with
        | zero => omega
        | succ m =>
            have hj0 : j = 0 := Fin.ext hj
            subst hj0
            rw [Fin.sum_univ_succ]
            change g 0 0 + (∑ i : Fin m, g i.succ 0) -
              (∑ s : Fin m, g ⟨s.1 + 1, by omega⟩ 0) = g 0 0
            have hreindex : (∑ s : Fin m, g ⟨s.1 + 1, by omega⟩ 0) = ∑ x : Fin m, g x.succ 0 :=
              Finset.sum_congr rfl fun s _ => rfl
            rw [hreindex, add_sub_cancel_right]
      · simp only [hj, ↓reduceDIte]
        have hidx : (⟨(j : ℕ) - 1 + 1, by have := j.isLt; omega⟩ : Fin ℓ) = j := by
          apply Fin.ext; dsimp; omega
        rw [hidx]
    · -- positive-degree term `k = k'.succ`
      simp only [bwd, fwd, maskFromTranscriptAndSlack, Fin.cases_succ]
      change ((2 : F) ^ (ℓ - 1 - (j : ℕ)))⁻¹ * maskRoundPoly r g j k'.succ = g j k'.succ
      rw [maskRoundPoly_succ]
      exact inv_mul_cancel_left₀ (pow_ne_zero _ h2) _
  exact LinearEquiv.ofBijective fwd ⟨Function.LeftInverse.injective hleft,
    Function.RightInverse.surjective hright⟩

@[simp] theorem maskTranscriptLinearEquiv_fst {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) (g : MaskSpace ℓ d F) :
    (maskTranscriptLinearEquiv h2 hℓ r g).1 = maskToConsistentTranscript hℓ r g := rfl

/-- **Surjectivity of the Mask-to-View Map (`hvzkSumcheck_maskToView_surjective`):**
for `(2 : F) ≠ 0` and `ℓ ≥ 1`, every sum-consistent transcript is realized by a separable mask. -/
theorem hvzkSumcheck_maskToView_surjective {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F) :
    Function.Surjective (maskToConsistentTranscript (d := d) hℓ r) := by
  intro v
  refine ⟨(maskTranscriptLinearEquiv h2 hℓ r).symm (v, 0), ?_⟩
  have h := (maskTranscriptLinearEquiv h2 hℓ r).apply_symm_apply (v, 0)
  exact congrArg Prod.fst h

/-- Explicit bijection between the fiber of masks sending target `P` to sum-consistent transcript `v`
and the `(ℓ - 1)`-dimensional slack space `Fin (ℓ - 1) → F`. -/
noncomputable def hvzkSumcheckFiberEquiv {F : Type*} [Field F] {ℓ d : ℕ}
    (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → F)
    (P : TargetPoly ℓ d F) (v : ConsistentTranscript (d := d) hℓ r) :
    {g : MaskSpace ℓ d F // maskedTranscript r P g = v.1} ≃ (Fin (ℓ - 1) → F) where
  toFun g := (maskTranscriptLinearEquiv h2 hℓ r g.1).2
  invFun slack :=
    let targetMaskView : ConsistentTranscript (d := d) hℓ r :=
      v - ⟨honestTranscript r P, honestTranscript_mem_consistent hℓ r P⟩
    ⟨(maskTranscriptLinearEquiv h2 hℓ r).symm (targetMaskView, slack), by
      have h := congrArg Prod.fst
        ((maskTranscriptLinearEquiv h2 hℓ r).apply_symm_apply (targetMaskView, slack))
      have hval : maskToRawTranscript r
          ((maskTranscriptLinearEquiv h2 hℓ r).symm (targetMaskView, slack)) =
          v.1 - honestTranscript r P :=
        congrArg Subtype.val h
      unfold maskedTranscript
      rw [hval, add_sub_cancel]⟩
  left_inv g := by
    apply Subtype.ext
    dsimp only
    have hg : (maskTranscriptLinearEquiv h2 hℓ r g.1).1 =
        v - ⟨honestTranscript r P, honestTranscript_mem_consistent hℓ r P⟩ := by
      apply Subtype.ext
      change maskToRawTranscript r g.1 = v.1 - honestTranscript r P
      exact eq_sub_of_add_eq' g.2
    rw [← hg, Prod.eta, LinearEquiv.symm_apply_apply]
  right_inv slack := by
    dsimp only
    exact congrArg Prod.snd
      ((maskTranscriptLinearEquiv h2 hℓ r).apply_symm_apply (_, slack))

/-- **Odd-Characteristic Fiber Regularity (`hvzkSumcheck_fiber_card_eq`):**
over any finite field `F` with `(2 : F) ≠ 0`, `ℓ ≥ 1`, and any per-variable degree bound `d : ℕ`
(including `d ≥ 1`, where `{0, 1}` evaluations are distinct coordinates of `(d + 1)`-point tables),
every target polynomial `P : TargetPoly ℓ d F` and every sum-consistent transcript `v` has **exact
constant fiber cardinality `|F|^{ℓ - 1}`**. -/
theorem hvzkSumcheck_fiber_card_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → F) (P : TargetPoly ℓ d F)
    (v : ConsistentTranscript (d := d) hℓ r) :
    Fintype.card {g : MaskSpace ℓ d F // maskedTranscript r P g = v.1} =
      Fintype.card F ^ (ℓ - 1) := by
  rw [Fintype.card_congr (hvzkSumcheckFiberEquiv h2 hℓ r P v),
    Fintype.card_fun, Fintype.card_fin]

/-- **Joint PCS Terminal-Relation Fiber Regularity (`hvzkSumcheck_terminal_fiber_card_eq`):**
when the verifier discharges the terminal relation `P(r) + g(r) = s_{ℓ-1}(r_{ℓ-1})` **jointly inside
a hiding PCS linear check** (without opening `g(r)` in the clear — see
`clearMaskEval_reveals_targetEval_not_gapAtMost` below for why revealing `g(r)` in the clear breaks
HVZK!), the constraint `g(r) = s_{ℓ-1}(r_{ℓ-1}) - P(r)` is already implied by `maskedTranscript r P g = v.1`,
preserving exact fiber cardinality `|F|^{ℓ - 1}`. -/
theorem hvzkSumcheck_terminal_fiber_card_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → F) (P : TargetPoly ℓ d F)
    (v : ConsistentTranscript (d := d) hℓ r) :
    let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
    Fintype.card {g : MaskSpace ℓ d F //
      maskedTranscript r P g = v.1 ∧
      evalMask g r = evalRoundPoly (v.1.2 last) (r last) - evalTargetPoly P r} =
      Fintype.card F ^ (ℓ - 1) := by
  intro last
  have hequiv : {g : MaskSpace ℓ d F //
      maskedTranscript r P g = v.1 ∧
      evalMask g r = evalRoundPoly (v.1.2 last) (r last) - evalTargetPoly P r} ≃
      {g : MaskSpace ℓ d F // maskedTranscript r P g = v.1} :=
    { toFun := fun g => ⟨g.1, g.2.1⟩
      invFun := fun g => ⟨g.1, g.2, by
        have hterm := maskedTranscript_terminal_eval hℓ r P g.1
        dsimp only at hterm
        rw [g.2] at hterm
        exact eq_sub_of_add_eq' hterm.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr hequiv]
  exact hvzkSumcheck_fiber_card_eq h2 hℓ r P v

/-- **Clear Mask-Evaluation Leakage Tooth (`clearMaskEval_reveals_targetEval_not_gapAtMost`):**
if a broken protocol reveals `evalMask g r` (`g(r)`) **in the clear** alongside the masked sumcheck
transcript (rather than checking `P(r) + g(r) = s_{ℓ-1}(r_{ℓ-1})` inside a hiding PCS), then
`s_{ℓ-1}(r_{ℓ-1}) - g(r) = P(r)` exposes `P(r)` deterministically, separating any `P₀, P₁` with
`P₀(r) ≠ P₁(r)` with advantage `1`! -/
theorem clearMaskEval_reveals_targetEval_not_gapAtMost
    {R : Type*} [CommRing R] [DecidableEq R]
    {ℓ d tapes num den : ℕ} (hℓ : 1 ≤ ℓ) (hsmall : num < den)
    (r : Fin ℓ → R) (P₀ P₁ : TargetPoly ℓ d R)
    (hdiff : evalTargetPoly P₀ r ≠ evalTargetPoly P₁ r)
    (maskAt : Fin tapes → MaskSpace ℓ d R) :
    let last : Fin ℓ := ⟨ℓ - 1, Nat.sub_lt hℓ Nat.one_pos⟩
    let D : RawTranscript ℓ d R × R → Bool :=
      fun p => decide (evalRoundPoly (p.1.2 last) (r last) - p.2 = evalTargetPoly P₀ r)
    ¬ GapAtMost tapes num den
      (fun t => D (maskedTranscript r P₀ (maskAt t), evalMask (maskAt t) r))
      (fun t => D (maskedTranscript r P₁ (maskAt t), evalMask (maskAt t) r)) := by
  intro last D
  apply not_gapAtMost_of_separating hsmall
  · intro t
    dsimp only [D]
    have hterm := maskedTranscript_terminal_eval hℓ r P₀ (maskAt t)
    dsimp only at hterm
    rw [hterm, add_sub_cancel_right]
    exact decide_eq_true rfl
  · intro t
    dsimp only [D]
    have hterm := maskedTranscript_terminal_eval hℓ r P₁ (maskAt t)
    dsimp only at hterm
    rw [hterm, add_sub_cancel_right]
    exact decide_eq_false hdiff.symm

/-- Submodule of zero-hypercube-sum separable masks (`cubeSum (evalMask g) = 0`), used when the
public sumcheck claim `S = cubeSum P` is unmasked (`P₀, P₁` share `cubeSum P₀ = cubeSum P₁`). -/
def ZeroSumMaskSubmodule {R : Type*} [CommRing R] (ℓ d : ℕ) : Submodule R (MaskSpace ℓ d R) :=
  LinearMap.ker ((LinearMap.fst R R (Fin ℓ → RoundPoly d R)).comp (maskToRawTranscript (fun _ => 0)))

@[simp] theorem mem_zeroSumMaskSubmodule {R : Type*} [CommRing R] {ℓ d : ℕ} {g : MaskSpace ℓ d R} :
    g ∈ ZeroSumMaskSubmodule ℓ d ↔ cubeSum (evalMask g) = 0 := Iff.rfl

instance instFintypeZeroSumMaskSubmodule {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ℓ d : ℕ) : Fintype (ZeroSumMaskSubmodule ℓ d (R := F)) :=
  Subtype.fintype (fun g => cubeSum (evalMask g) = 0)

/-- **Public-Sum Fiber Regularity (`hvzkSumcheck_publicSum_fiber_card_eq`):**
when `g` ranges over `ZeroSumMaskSubmodule ℓ d` (`cubeSum g = 0`), every sum-consistent transcript
`v` matching `P`'s public hypercube sum (`v.1.1 = cubeSum (evalTargetPoly P)`) ALSO has exact
constant fiber cardinality `|F|^{ℓ - 1}`. -/
theorem hvzkSumcheck_publicSum_fiber_card_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → F) (P : TargetPoly ℓ d F)
    (v : ConsistentTranscript (d := d) hℓ r)
    (hpub : v.1.1 = cubeSum (evalTargetPoly P)) :
    Fintype.card {g : ZeroSumMaskSubmodule ℓ d (R := F) // maskedTranscript r P g.1 = v.1} =
      Fintype.card F ^ (ℓ - 1) := by
  have hequiv : {g : ZeroSumMaskSubmodule ℓ d (R := F) // maskedTranscript r P g.1 = v.1} ≃
      {g : MaskSpace ℓ d F // maskedTranscript r P g = v.1} :=
    { toFun := fun g => ⟨g.1.1, g.2⟩
      invFun := fun g => ⟨⟨g.1, by
        rw [mem_zeroSumMaskSubmodule]
        have h1 : (maskedTranscript r P g.1).1 = v.1.1 := congrArg Prod.fst g.2
        simp only [maskedTranscript, honestTranscript, maskToRawTranscript, Prod.fst_add,
          LinearMap.coe_mk, AddHom.coe_mk, hpub] at h1
        exact add_left_cancel (h1.trans (add_zero _).symm)⟩, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr hequiv]
  exact hvzkSumcheck_fiber_card_eq h2 hℓ r P v

/-- **Public-Sum Zero `FiniteTapeGap` (`hvzkSumcheck_publicSum_gapAtMost_zero`):**
for any two witnesses `P₀, P₁` sharing the same public hypercube sum (`cubeSum P₀ = cubeSum P₁`),
sampling `g` uniformly from `ZeroSumMaskSubmodule ℓ d` achieves zero distinguishing gap without
requiring an auxiliary sum-blinding scalar. -/
theorem hvzkSumcheck_publicSum_gapAtMost_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d tapes den : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (hden : 0 < den)
    (r : Fin ℓ → F) (P₀ P₁ : TargetPoly ℓ d F)
    (hpub : cubeSum (evalTargetPoly P₀) = cubeSum (evalTargetPoly P₁))
    (enum : Fin tapes ≃ ZeroSumMaskSubmodule ℓ d (R := F))
    (D : RawTranscript ℓ d F → Bool) :
    GapAtMost tapes 0 den
      (fun t => D (maskedTranscript r P₀ (enum t).1))
      (fun t => D (maskedTranscript r P₁ (enum t).1)) := by
  have htapes : 0 < tapes := by
    rw [← Fintype.card_fin tapes, Fintype.card_congr enum]
    exact Fintype.card_pos
  let diffView : ConsistentTranscript (d := d) hℓ r :=
    ⟨honestTranscript r P₀, honestTranscript_mem_consistent hℓ r P₀⟩ -
    ⟨honestTranscript r P₁, honestTranscript_mem_consistent hℓ r P₁⟩
  let gDeltaRaw : MaskSpace ℓ d F := (maskTranscriptLinearEquiv h2 hℓ r).symm (diffView, 0)
  have hgDeltaRaw : maskToRawTranscript r gDeltaRaw = honestTranscript r P₀ - honestTranscript r P₁ := by
    have h := congrArg Prod.fst
      ((maskTranscriptLinearEquiv h2 hℓ r).apply_symm_apply (diffView, 0))
    exact congrArg Subtype.val h
  have hgDeltaZero : gDeltaRaw ∈ ZeroSumMaskSubmodule ℓ d (R := F) := by
    rw [mem_zeroSumMaskSubmodule]
    have hfst := congrArg Prod.fst hgDeltaRaw
    simp only [maskToRawTranscript, honestTranscript, Prod.fst_sub, LinearMap.coe_mk,
      AddHom.coe_mk, hpub, sub_self] at hfst
    exact hfst
  let gDelta : ZeroSumMaskSubmodule ℓ d (R := F) := ⟨gDeltaRaw, hgDeltaZero⟩
  let shift : ZeroSumMaskSubmodule ℓ d (R := F) ≃ ZeroSumMaskSubmodule ℓ d (R := F) :=
    Equiv.addRight gDelta
  let relabel : Equiv.Perm (Fin tapes) := enum.trans (shift.trans enum.symm)
  have hcomp : ((fun t => D (maskedTranscript r P₁ (enum t).1)) ∘ relabel) =
      (fun t => D (maskedTranscript r P₀ (enum t).1)) := by
    funext t
    simp only [Function.comp_apply, relabel, Equiv.trans_apply, Equiv.apply_symm_apply]
    congr 1
    have hsh : (shift (enum t)).1 = (enum t).1 + gDeltaRaw := rfl
    rw [hsh, maskedTranscript, maskedTranscript, map_add, hgDeltaRaw]
    abel
  rw [← hcomp]
  exact GapAtMost.zero_of_perm htapes hden _ relabel

/-- **Pointwise Transcript Probability Equality (`hvzkSumcheck_view_prob_eq`):**
over `[Field F] [Fintype F]` with `(2 : F) ≠ 0` and `ℓ ≥ 1`, any two target polynomials
`P₀, P₁ : TargetPoly ℓ d F` assign the **exact same probability** (and exact same mask count:
`|F|^{ℓ - 1}` inside `ConsistentTranscript`, `0` outside) to *every* raw transcript `tr`. -/
theorem hvzkSumcheck_view_prob_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ d : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → F) (P₀ P₁ : TargetPoly ℓ d F) (tr : RawTranscript ℓ d F) :
    ((Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₀ g = tr).card : ℚ) /
        (Fintype.card (MaskSpace ℓ d F) : ℚ) =
      ((Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₁ g = tr).card : ℚ) /
        (Fintype.card (MaskSpace ℓ d F) : ℚ) := by
  congr 2
  by_cases hmem : tr ∈ ConsistentTranscript hℓ r
  · have hc0 : (Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₀ g = tr).card =
        Fintype.card F ^ (ℓ - 1) := by
      rw [← Fintype.card_subtype]
      exact hvzkSumcheck_fiber_card_eq h2 hℓ r P₀ ⟨tr, hmem⟩
    have hc1 : (Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₁ g = tr).card =
        Fintype.card F ^ (ℓ - 1) := by
      rw [← Fintype.card_subtype]
      exact hvzkSumcheck_fiber_card_eq h2 hℓ r P₁ ⟨tr, hmem⟩
    rw [hc0, hc1]
  · have he0 : (Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₀ g = tr) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro g _ heq
      exact hmem (heq ▸ maskedTranscript_mem_consistent hℓ r P₀ g)
    have he1 : (Finset.univ.filter fun g : MaskSpace ℓ d F => maskedTranscript r P₁ g = tr) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro g _ heq
      exact hmem (heq ▸ maskedTranscript_mem_consistent hℓ r P₁ g)
    rw [he0, he1]

/-- **Zero `FiniteTapeGap` Theorem (`hvzkSumcheck_gapAtMost_zero`):**
for *every* boolean distinguisher `D : RawTranscript ℓ d F → Bool`, *every* tape enumeration
`enum : Fin tapes ≃ MaskSpace ℓ d F`, and *every* `0 < den`, the distinguishing gap between
`P₀` and `P₁` is **literally `0`**. -/
theorem hvzkSumcheck_gapAtMost_zero {F : Type*} [Field F] [Fintype F]
    {ℓ d tapes den : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (hden : 0 < den)
    (r : Fin ℓ → F) (P₀ P₁ : TargetPoly ℓ d F)
    (enum : Fin tapes ≃ MaskSpace ℓ d F)
    (D : RawTranscript ℓ d F → Bool) :
    GapAtMost tapes 0 den
      (fun t => D (maskedTranscript r P₀ (enum t)))
      (fun t => D (maskedTranscript r P₁ (enum t))) := by
  have htapes : 0 < tapes := by
    rw [← Fintype.card_fin tapes, Fintype.card_congr enum]
    exact Fintype.card_pos
  let diffView : ConsistentTranscript (d := d) hℓ r :=
    ⟨honestTranscript r P₀, honestTranscript_mem_consistent hℓ r P₀⟩ -
    ⟨honestTranscript r P₁, honestTranscript_mem_consistent hℓ r P₁⟩
  let gDelta : MaskSpace ℓ d F := (maskTranscriptLinearEquiv h2 hℓ r).symm (diffView, 0)
  have hgDelta : maskToRawTranscript r gDelta = honestTranscript r P₀ - honestTranscript r P₁ := by
    have h := congrArg Prod.fst
      ((maskTranscriptLinearEquiv h2 hℓ r).apply_symm_apply (diffView, 0))
    exact congrArg Subtype.val h
  let shift : MaskSpace ℓ d F ≃ MaskSpace ℓ d F := Equiv.addRight gDelta
  let relabel : Equiv.Perm (Fin tapes) := enum.trans (shift.trans enum.symm)
  have hcomp : ((fun t => D (maskedTranscript r P₁ (enum t))) ∘ relabel) =
      (fun t => D (maskedTranscript r P₀ (enum t))) := by
    funext t
    simp only [Function.comp_apply, relabel, Equiv.trans_apply, Equiv.apply_symm_apply]
    congr 1
    have hsh : shift (enum t) = enum t + gDelta := rfl
    rw [hsh, maskedTranscript, maskedTranscript, map_add, hgDelta]
    abel
  rw [← hcomp]
  exact GapAtMost.zero_of_perm htapes hden _ relabel

/-- `GMask` `ρ`-scaled transcript `honestTranscript r P + ρ • maskToRawTranscript r g` (`P + ρ g`). -/
def maskedTranscriptScaled {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (ρ : R) (P : TargetPoly ℓ d R) (g : MaskSpace ℓ d R) : RawTranscript ℓ d R :=
  honestTranscript r P + ρ • maskToRawTranscript r g

theorem maskedTranscriptScaled_eq {R : Type*} [CommRing R] {ℓ d : ℕ}
    (r : Fin ℓ → R) (ρ : R) (P : TargetPoly ℓ d R) (g : MaskSpace ℓ d R) :
    maskedTranscriptScaled r ρ P g = maskedTranscript r P (ρ • g) := by
  rw [maskedTranscriptScaled, maskedTranscript, map_smul]

/-- **Nonzero Batching Scalar `ρ ≠ 0` Preserves Zero `FiniteTapeGap`
(`hvzkSumcheck_scaled_gapAtMost_zero`):**
scaling the separable mask by any verifier batching challenge `ρ ≠ 0` preserves uniform transcripts. -/
theorem hvzkSumcheck_scaled_gapAtMost_zero {F : Type*} [Field F] [Fintype F]
    {ℓ d tapes den : ℕ} (h2 : (2 : F) ≠ 0) (hℓ : 1 ≤ ℓ) (hden : 0 < den)
    {ρ : F} (hρ : ρ ≠ 0)
    (r : Fin ℓ → F) (P₀ P₁ : TargetPoly ℓ d F)
    (enum : Fin tapes ≃ MaskSpace ℓ d F)
    (D : RawTranscript ℓ d F → Bool) :
    GapAtMost tapes 0 den
      (fun t => D (maskedTranscriptScaled r ρ P₀ (enum t)))
      (fun t => D (maskedTranscriptScaled r ρ P₁ (enum t))) := by
  let scaleEquiv : MaskSpace ℓ d F ≃ MaskSpace ℓ d F :=
    { toFun := fun g => ρ • g
      invFun := fun g => ρ⁻¹ • g
      left_inv := fun g => inv_smul_smul₀ hρ g
      right_inv := fun g => smul_inv_smul₀ hρ g }
  have h := hvzkSumcheck_gapAtMost_zero h2 hℓ hden r P₀ P₁ (enum.trans scaleEquiv) D
  have hfn : ∀ P : TargetPoly ℓ d F,
      (fun t => D (maskedTranscriptScaled r ρ P (enum t))) =
      (fun t => D (maskedTranscript r P ((enum.trans scaleEquiv) t))) := by
    intro P
    funext t
    simp [maskedTranscriptScaled_eq, scaleEquiv]
  rw [hfn P₀, hfn P₁]
  exact h

/-- **Zero Batching Scalar `ρ = 0` Falsifier Tooth (`rhoZero_scaledMask_not_gapAtMost`):**
if the verifier fails to reject/re-squeeze `ρ = 0`, `maskedTranscriptScaled r 0 P g` collapses to
`honestTranscript r P`, separating any `P₀, P₁` with distinct honest transcripts with advantage `1`! -/
theorem rhoZero_scaledMask_not_gapAtMost {R : Type*} [CommRing R] [DecidableEq R]
    {ℓ d tapes num den : ℕ} (hsmall : num < den)
    (r : Fin ℓ → R) (P₀ P₁ : TargetPoly ℓ d R)
    (hdiff : honestTranscript r P₀ ≠ honestTranscript r P₁)
    (maskAt : Fin tapes → MaskSpace ℓ d R) :
    let D : RawTranscript ℓ d R → Bool := fun tr => decide (tr = honestTranscript r P₀)
    ¬ GapAtMost tapes num den
      (fun t => D (maskedTranscriptScaled r 0 P₀ (maskAt t)))
      (fun t => D (maskedTranscriptScaled r 0 P₁ (maskAt t))) := by
  intro D
  apply not_gapAtMost_of_separating hsmall
  · intro t
    simp [D, maskedTranscriptScaled]
  · intro t
    dsimp only [D]
    rw [maskedTranscriptScaled, zero_smul, add_zero]
    exact decide_eq_false hdiff.symm

/-! ## §4. Under-Degree Leakage Tooth & Concrete `ZMod 2` / `ZMod 7` Keystones -/

/-- Embed an under-degree separable mask `MaskSpace ℓ (d - 1) R` into `MaskSpace ℓ d R` by setting
each polynomial's degree-`d` coefficient (`Fin.last d`) to `0`. -/
def embedUnderDegreeMask {R : Type*} [Semiring R] {ℓ d : ℕ} (hd : 1 ≤ d) :
    MaskSpace ℓ (d - 1) R →ₗ[R] MaskSpace ℓ d R where
  toFun g j k :=
    if hk : (k : ℕ) < d then g j ⟨(k : ℕ), by omega⟩ else 0
  map_add' g₁ g₂ := by
    funext j k
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem embedUnderDegreeMask_last {R : Type*} [Semiring R] {ℓ d : ℕ}
    (hd : 1 ≤ d) (g : MaskSpace ℓ (d - 1) R) (j : Fin ℓ) :
    embedUnderDegreeMask hd g j (Fin.last d) = 0 := by
  simp [embedUnderDegreeMask]

/-- **Under-Degree Top-Coefficient Leakage (`underDegreeMask_topCoeff_eq`):**
when `1 ≤ d` and `g` has degree `≤ d - 1`, the degree-`d` coefficient of *every* masked round
polynomial `s_i(X)` equals the unmasked degree-`d` coefficient of `P_i(X)` identically. -/
theorem underDegreeMask_topCoeff_eq {R : Type*} [CommRing R] {ℓ d : ℕ}
    (hd : 1 ≤ d) (r : Fin ℓ → R) (P : TargetPoly ℓ d R)
    (g : MaskSpace ℓ (d - 1) R) (i : Fin ℓ) :
    (maskedTranscript r P (embedUnderDegreeMask hd g)).2 i (Fin.last d) =
      honestRoundPoly r P i (Fin.last d) := by
  have hne : (Fin.last d : Fin (d + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp only [maskedTranscript, honestTranscript, maskToRawTranscript, Prod.snd_add, Pi.add_apply,
    LinearMap.coe_mk, AddHom.coe_mk, maskRoundPoly, hne, ↓reduceIte, embedUnderDegreeMask_last,
    mul_zero, add_zero]

/-- **Under-Degree Distinguishing Advantage 1 (`underDegreeMask_distinguishes`):**
if `P₀` and `P₁` differ in the degree-`d` coefficient of round `0`, an under-degree mask of degree
`d - 1 < d` fails to hide: reading `s₀`'s degree-`d` coefficient distinguishes `P₀` from `P₁` with
probability `1` across all tapes, refuting `GapAtMost tapes num den` for every `num < den`. -/
theorem underDegreeMask_distinguishes {R : Type*} [CommRing R] [DecidableEq R]
    {ℓ d tapes num den : ℕ} (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) (hsmall : num < den)
    (r : Fin ℓ → R) (P₀ P₁ : TargetPoly ℓ d R)
    (hdiff : honestRoundPoly r P₀ ⟨0, hℓ⟩ (Fin.last d) ≠
             honestRoundPoly r P₁ ⟨0, hℓ⟩ (Fin.last d))
    (maskAt : Fin tapes → MaskSpace ℓ (d - 1) R) :
    let D : RawTranscript ℓ d R → Bool :=
      fun tr => decide (tr.2 ⟨0, hℓ⟩ (Fin.last d) = honestRoundPoly r P₀ ⟨0, hℓ⟩ (Fin.last d))
    ¬ GapAtMost tapes num den
      (fun t => D (maskedTranscript r P₀ (embedUnderDegreeMask hd (maskAt t))))
      (fun t => D (maskedTranscript r P₁ (embedUnderDegreeMask hd (maskAt t)))) := by
  intro D
  apply not_gapAtMost_of_separating hsmall
  · intro t
    dsimp only [D]
    rw [underDegreeMask_topCoeff_eq hd r P₀ (maskAt t) ⟨0, hℓ⟩]
    exact decide_eq_true rfl
  · intro t
    dsimp only [D]
    rw [underDegreeMask_topCoeff_eq hd r P₁ (maskAt t) ⟨0, hℓ⟩]
    exact decide_eq_false hdiff.symm

/-! ### Concrete Kernel-Checked Keystones on `ZMod 2` (`ℓ = 2`) and `ZMod 7` (`d = 2`) -/

section ConcreteKeystones

/-- On `ZMod 2` at `ℓ = 2`, `P_and(x₀, x₁) = x₀ · x₁` has hypercube sum `1`, while `0` has sum `0`. -/
def zmod2AndPoly : TargetPoly 2 1 (ZMod 2) :=
  fun e => if e 0 = 1 ∧ e 1 = 1 then 1 else 0

/-- **Kernel-checked `ZMod 2` (`ℓ = 2`) Characteristic-2 Falsifier:**
across all `16` affine separable masks `g : MaskSpace 2 1 (ZMod 2)`, `cubeSum (evalMask g) = 0` AND
the masked sum of `P_and` is always `1` while the masked sum of `0` is always `0`. -/
theorem zmod2_ell2_separableMask_leaks :
    (∀ g : MaskSpace 2 1 (ZMod 2), cubeSum (evalMask g) = 0) ∧
    (∀ g : MaskSpace 2 1 (ZMod 2),
      (maskedTranscript (fun _ => 0) zmod2AndPoly g).1 = 1 ∧
      (maskedTranscript (fun _ => 0) 0 g).1 = 0) := by
  decide

/-- Concrete `tapes = 16 > 0` (`Fintype.card (MaskSpace 2 1 (ZMod 2)) = 16`) `GapAtMost` refutation
on `ZMod 2` (`ℓ = 2`) between `zmod2AndPoly` (`x₀ · x₁`) and `0`. -/
theorem zmod2_ell2_separableMask_not_gapAtMost_concrete {num den : ℕ} (hsmall : num < den) :
    let enum16 := (Fintype.equivFin (MaskSpace 2 1 (ZMod 2))).symm
    ¬ GapAtMost (Fintype.card (MaskSpace 2 1 (ZMod 2))) num den
      (fun t => decide ((maskedTranscript (fun _ => 0) zmod2AndPoly (enum16 t)).1 = 1))
      (fun t => decide ((maskedTranscript (fun _ => 0) 0 (enum16 t)).1 = 1)) := by
  intro enum16
  apply not_gapAtMost_of_separating hsmall
  · intro t
    rw [(zmod2_ell2_separableMask_leaks.2 (enum16 t)).1]
    rfl
  · intro t
    rw [(zmod2_ell2_separableMask_leaks.2 (enum16 t)).2]
    decide

/-- On `ZMod 7` (`d = 2`, quadratic Gruen sumcheck), `P_quad(X₀, X₁) = X₀²` and `P_lin(X₀, X₁) = X₀`
agree on *every* boolean vertex (`b² = b`), hence share the **exact same hypercube sum**! -/
def zmod7QuadTarget : TargetPoly 2 2 (ZMod 7) :=
  fun e => if e 0 = 2 ∧ e 1 = 0 then 1 else 0

def zmod7LinTarget : TargetPoly 2 2 (ZMod 7) :=
  fun e => if e 0 = 1 ∧ e 1 = 0 then 1 else 0

/-- `zmod7QuadTarget` and `zmod7LinTarget` share the identical public sum `2 : ZMod 7`, yet differ
in round-0 degree-2 coefficient (`2 ≠ 0`). -/
theorem zmod7_same_cubeSum_ne_topCoeff :
    cubeSum (evalTargetPoly zmod7QuadTarget) = (2 : ZMod 7) ∧
    cubeSum (evalTargetPoly zmod7LinTarget) = (2 : ZMod 7) ∧
    honestRoundPoly ![3, 5] zmod7QuadTarget 0 (Fin.last 2) = (2 : ZMod 7) ∧
    honestRoundPoly ![3, 5] zmod7LinTarget 0 (Fin.last 2) = (0 : ZMod 7) := by
  decide

/-- **Kernel-checked `ZMod 7` Under-Degree Evaluation-Difference Tooth (`decide`):**
at `ℓ = 1, d = 2`, an affine mask (`d_mask = 1`, `49` masks) leaves even the 3-point evaluation
second difference `s₀(2) - 2 s₀(1) + s₀(0)` invariant (`2` for `X₀²` vs `0` for `X₀`). -/
def zmod7UnivarQuad : TargetPoly 1 2 (ZMod 7) := fun e => if e 0 = 2 then 1 else 0
def zmod7UnivarLin  : TargetPoly 1 2 (ZMod 7) := fun e => if e 0 = 1 then 1 else 0

theorem zmod7_affineMask_evalDiff_kernel :
    cubeSum (evalTargetPoly zmod7UnivarQuad) = cubeSum (evalTargetPoly zmod7UnivarLin) ∧
    ∀ g : MaskSpace 1 1 (ZMod 7),
      let sQuad := (maskedTranscript ![4] zmod7UnivarQuad (embedUnderDegreeMask (by decide) g)).2 0
      let sLin  := (maskedTranscript ![4] zmod7UnivarLin  (embedUnderDegreeMask (by decide) g)).2 0
      evalRoundPoly sQuad 2 - 2 * evalRoundPoly sQuad 1 + evalRoundPoly sQuad 0 = 2 ∧
      evalRoundPoly sLin  2 - 2 * evalRoundPoly sLin  1 + evalRoundPoly sLin  0 = 0 := by
  decide

/-- **Negative Pole on `ZMod 7` (`ℓ = 2, d = 2`, affine mask `d_mask = 1 < 2`):**
refutes `GapAtMost` for every `num < den` on `(zmod7QuadTarget, zmod7LinTarget)`. -/
theorem zmod7_quadratic_affineMask_not_gapAtMost {tapes num den : ℕ} (hsmall : num < den)
    (maskAt : Fin tapes → MaskSpace 2 1 (ZMod 7)) :
    let D : RawTranscript 2 2 (ZMod 7) → Bool :=
      fun tr => decide (tr.2 0 (Fin.last 2) = (2 : ZMod 7))
    ¬ GapAtMost tapes num den
      (fun t => D (maskedTranscript ![3, 5] zmod7QuadTarget (embedUnderDegreeMask (Nat.le_add_left 1 1) (maskAt t))))
      (fun t => D (maskedTranscript ![3, 5] zmod7LinTarget  (embedUnderDegreeMask (Nat.le_add_left 1 1) (maskAt t)))) := by
  have hfacts := zmod7_same_cubeSum_ne_topCoeff
  have hdiff : honestRoundPoly ![3, 5] zmod7QuadTarget 0 (Fin.last 2) ≠
               honestRoundPoly ![3, 5] zmod7LinTarget 0 (Fin.last 2) := by
    rw [hfacts.2.2.1, hfacts.2.2.2]; decide
  have h := underDegreeMask_distinguishes (hℓ := Nat.le_add_left 1 1) (hd := Nat.le_add_left 1 1)
    hsmall ![3, 5] zmod7QuadTarget zmod7LinTarget hdiff maskAt
  have htop : honestRoundPoly ![3, 5] zmod7QuadTarget ⟨0, Nat.le_add_left 1 1⟩ (Fin.last (1 + 1)) =
      (2 : ZMod 7) := hfacts.2.2.1
  dsimp only at h ⊢
  rw [htop] at h
  exact h

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **Positive Pole on `ZMod 7` (`ℓ = 2, d = 2`, full degree-`2` separable mask):**
on the *exact same* pair `(zmod7QuadTarget, zmod7LinTarget)`, upgrading `d_mask` from `1` to `2`
restores exact fiber cardinality `7^(2-1) = 7` AND zero `FiniteTapeGap` against *every* test `D`! -/
theorem zmod7_quadratic_deg2Mask_fiber_and_gap_zero
    (v : ConsistentTranscript (R := ZMod 7) (ℓ := 2) (d := 2) (Nat.le_add_left 1 1) ![3, 5])
    (D : RawTranscript 2 2 (ZMod 7) → Bool) :
    Fintype.card {g : MaskSpace 2 2 (ZMod 7) // maskedTranscript ![3, 5] zmod7QuadTarget g = v.1} = 7 ∧
    GapAtMost (Fintype.card (MaskSpace 2 2 (ZMod 7))) 0 1
      (fun t => D (maskedTranscript ![3, 5] zmod7QuadTarget ((Fintype.equivFin _).symm t)))
      (fun t => D (maskedTranscript ![3, 5] zmod7LinTarget  ((Fintype.equivFin _).symm t))) := by
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  refine ⟨?_, ?_⟩
  · have hcard := hvzkSumcheck_fiber_card_eq h2 (Nat.le_add_left 1 1)
      ![3, 5] zmod7QuadTarget v
    rw [hcard, ZMod.card]
    rfl
  · exact hvzkSumcheck_gapAtMost_zero h2 (Nat.le_add_left 1 1) Nat.one_pos
      ![3, 5] zmod7QuadTarget zmod7LinTarget (Fintype.equivFin _).symm D

end ConcreteKeystones

/-! ## §5. Axiom Audit Pins -/

#assert_axioms cubeSum_separableMask_eq
#assert_axioms charTwo_cubeSum_separableMask_eq_zero
#assert_axioms tower256_cubeSum_separableMask_eq_zero
#assert_axioms tower256_ell1_separableMask_nonzero_sum
#assert_axioms charTwo_separableMask_not_gapAtMost
#assert_axioms charTwo_maskRoundPoly_posCoeff_eq_zero_of_lt_last
#assert_axioms charTwo_maskRoundPoly_penultimate_const
#assert_axioms charTwo_maskRoundPoly_eq_zero_of_lt
#assert_axioms eval_targetPolyToMvPolynomial
#assert_axioms eval_separableMaskToMvPolynomial
#assert_axioms evalAtNodesLinearEquiv
#assert_axioms maskTranscriptLinearEquiv
#assert_axioms hvzkSumcheck_maskToView_surjective
#assert_axioms hvzkSumcheck_fiber_card_eq
#assert_axioms hvzkSumcheck_terminal_fiber_card_eq
#assert_axioms clearMaskEval_reveals_targetEval_not_gapAtMost
#assert_axioms hvzkSumcheck_publicSum_fiber_card_eq
#assert_axioms hvzkSumcheck_publicSum_gapAtMost_zero
#assert_axioms hvzkSumcheck_view_prob_eq
#assert_axioms hvzkSumcheck_gapAtMost_zero
#assert_axioms hvzkSumcheck_scaled_gapAtMost_zero
#assert_axioms rhoZero_scaledMask_not_gapAtMost
#assert_axioms underDegreeMask_distinguishes
#assert_axioms zmod2_ell2_separableMask_leaks
#assert_axioms zmod2_ell2_separableMask_not_gapAtMost_concrete
#assert_axioms zmod7_affineMask_evalDiff_kernel
#assert_axioms zmod7_quadratic_affineMask_not_gapAtMost
#assert_axioms zmod7_quadratic_deg2Mask_fiber_and_gap_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.cubeSum_separableMask_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeSum_separableMask_eq

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.charTwo_cubeSum_separableMask_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_cubeSum_separableMask_eq_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.tower256_cubeSum_separableMask_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tower256_cubeSum_separableMask_eq_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.tower256_ell1_separableMask_nonzero_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tower256_ell1_separableMask_nonzero_sum

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.charTwo_separableMask_not_gapAtMost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_separableMask_not_gapAtMost

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.charTwo_maskRoundPoly_penultimate_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_maskRoundPoly_penultimate_const

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.charTwo_maskRoundPoly_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms charTwo_maskRoundPoly_eq_zero_of_lt

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.evalAtNodesLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalAtNodesLinearEquiv

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.maskTranscriptLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskTranscriptLinearEquiv

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_maskToView_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_maskToView_surjective

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_fiber_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_fiber_card_eq

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_terminal_fiber_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_terminal_fiber_card_eq

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.clearMaskEval_reveals_targetEval_not_gapAtMost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clearMaskEval_reveals_targetEval_not_gapAtMost

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_publicSum_fiber_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_publicSum_fiber_card_eq

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_publicSum_gapAtMost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_publicSum_gapAtMost_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_view_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_view_prob_eq

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_gapAtMost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_gapAtMost_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.hvzkSumcheck_scaled_gapAtMost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hvzkSumcheck_scaled_gapAtMost_zero

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.rhoZero_scaledMask_not_gapAtMost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhoZero_scaledMask_not_gapAtMost

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.underDegreeMask_distinguishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms underDegreeMask_distinguishes

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.zmod2_ell2_separableMask_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod2_ell2_separableMask_leaks

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.zmod2_ell2_separableMask_not_gapAtMost_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod2_ell2_separableMask_not_gapAtMost_concrete

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.zmod7_affineMask_evalDiff_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod7_affineMask_evalDiff_kernel

/-- info: 'Minidregg.Theory.SumcheckHvzkMask.zmod7_quadratic_deg2Mask_fiber_and_gap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zmod7_quadratic_deg2Mask_fiber_and_gap_zero

end Minidregg.Theory.SumcheckHvzkMask
