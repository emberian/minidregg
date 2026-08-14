/-
# `Assurance/AirSumcheckCubic.lean` — the degree-3 rung

**Substrate, said out loud: this is Lean-authored.** The round engine, the degree bound, the
boolean-sum chain and the factored terminal check are theorems about the objects the Lean
`adaptive_sumcheck_soundness` consumes. The Rust prover (`prover/src/sumcheck.rs`) only
RE-COMPUTES these shapes and is bound to them by a conformance vector
(`Compiler/SumcheckConformance.lean`) — never by a refinement claim.

## Why degree 3, and why ONE file serves two consumers

`Selvage/MultilinearExtension.lean` built the degree-1 engine (a single MLE's hypercube sum);
`Assurance/AirSumcheckQuadratic.lean` built the degree-2 engine (`Â·B̂ − Ĉ`, terminal check
FACTORED). Both live consumers of the next rung are degree 3:

* a **GKR fraction-tree layer** is `eq(z,x)·(p_L(x)·q_R(x) + p_R(x)·q_L(x))`;
* a **zkML matmul** claim is `eq(z,x)·(Â(x)·B̂(x) − Ĉ(x))`.

So the engine here is built at the shape that covers both — a head factor times a sum of two
products, all five multi-affine:

  `cubicForm E A B C D (x) = Ê(x)·(Â(x)·B̂(x) + Ĉ(x)·D̂(x))`

and the two consumers are named as THEOREMS, not prose: `cubicForm_fraction_layer` (the `eq`
head, via `Selvage/EqPolynomial.lean`'s `eqMle_eq_mle`) and `cubicForm_hadamard` (`D ≡ 1`,
`C` negated).

⚠ **`cubicForm_hadamard` was originally named `cubicForm_matmul` and that name was wrong.**
`Â·B̂` is a POINTWISE product of two tables on one cube; a matmul contracts an inner index
that appears in neither output coordinate, and `Assurance/ZkmlMatmulSumcheck.lean`'s
`matmul_is_not_hadamard` computes the two on a 2×2 example and they differ. The matmul face
is `mle₂_contraction` + `cubicForm_contraction` in that file, and it uses this engine at a
DIFFERENT instance (head `E ≡ 1`, no `eq` factor, because the outer indices are bound by
challenges before the sumcheck starts). `cubicForm_subsumes_prodDiff` proves the degree-2 engine is a SPECIAL CASE of
this one rather than a parallel twin — the same object, not a second implementation.

## The engine

The protocol layer needed nothing: `Selvage/Sumcheck.lean` carries `{d : ℕ}` through
`sumcheckRound_prob` / `adaptive_sumcheck_soundness` (→ `v·d/|F|`) / `AdaptiveUnionBound`,
and the round-chain skeleton (`roundSum_fold/_zero/_succ/_last`, `glue`, `suffixSplit`) is
proved for an ARBITRARY `g` with no multilinearity hypothesis. Degree entered only at the
realizer. So this file builds one realizer and cites everything else.

The line restriction is COEFFICIENT-FORM, not interpolation-form: for multi-affine `f`,
`f̂(x[i↦t]) = f₀ + t·Δf` with `f₀ = f̂(x[i↦0])` and `Δf = f̂(x[i↦1]) − f̂(x[i↦0])`
(`lineBase`/`lineSlope`), so the product of a head and two pair-products expands to an
explicit cubic `k₀ + t·k₁ + t²·k₂ + t³·k₃` (`cubicForm_line`, one `ring`). This form needs
**no division and no characteristic hypothesis** — it works over any commutative ring, which
matters because the char-2 (binary-tower) instantiation cannot use `{0,1,2,3}` interpolation
nodes at all.

**What is proved (no `sorry`):**

* `cubicForm_line` / `roundSum_cubicForm` — the line is cubic, and the round partial sum is
  that cubic summed over the suffix cube (`glue_update` rides the running coordinate out).
* `cubicRoundPoly_eval` — the round message IS the round partial sum at EVERY point (no
  affineness hypothesis: the cubic identity carries it), `cubicRoundPoly_degree` — `d = 3`.
* `cubicHonest_prefixMeasurable` / `_degree` / `_boolean_sum` / `cubicHonest_complete` —
  the family inhabits every honest-side hypothesis of the adaptive protocol.
* `scChain_cubicHonest_final` — **the terminal check, FACTORED** as
  `Ê(r)·(Â(r)·B̂(r) + Ĉ(r)·D̂(r))`: five oracle openings the verifier combines itself, which
  is the whole point of a factored terminal check and the reason the round degree is 3.
* `cubic_sumcheck_soundness` — `≤ m·3/|F|`, one `simpa` from `adaptive_sumcheck_soundness`
  at `d = 3`. The bound is CITED, never re-derived.
* `cubic_retires_constraint` — any `LinearConstraint` on a word of cubic form that the word
  violates is retired at `m·3/|F|` with the honest side BUILT; the mask folds into the HEAD
  factor (`wt·(E·(A·B+C·D)) = (wt·E)·(A·B+C·D)`), which is cleaner than the quadratic case.

**Teeth (ZMod 7, m = 1 and m = 2, computed):** `cubicRoundPoly` is genuinely cubic — the
degree-3 coefficient is NONZERO on data (`cubic_leading_ne_zero`), so the rung is not a
degree-2 engine wearing a cubic type; a degree-2 message cannot represent the round
polynomial (`cubic_not_quadratic`); the chain computes; and the soundness pipeline fires
END-TO-END with a NONEMPTY accept event (`cubic_cheat_caught` + `cubic_cheat_witness`).

**Residual, named.** The single-shot zero-test `Σ_b eq(z,b)·D(b) = mle D z` is now an
identity (`Selvage.eqMle_fold`); turning it into a TEST needs
`Pr_z[mle D z = 0] ≤ m/|F|` for `D ≠ 0` — that is `Selvage/MultilinearZeroTest.lean`, this
rung's sibling, not a gap in this file's statements.
-/
import Assurance.AirSumcheckQuadratic
import Selvage.EqPolynomial

namespace Minidregg.Assurance

open Minidregg.Compiler Minidregg.Selvage Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. The cubic summand and its line restriction -/

section CubicEngine

variable {m : ℕ}

/-- **The degree-3 summand**: a head factor times a sum of two products of multilinear
extensions — `Ê·(Â·B̂ + Ĉ·D̂)`. Both live consumers of this rung are instances
(`cubicForm_fraction_layer`, `cubicForm_hadamard`). -/
def cubicForm (E A B C D : (Fin m → Bool) → F) : (Fin m → F) → F :=
  fun x => mle E x * (mle A x * mle B x + mle C x * mle D x)

omit [Fintype F] [DecidableEq F] in
/-- The sum-claim on the cube: the extension's hypercube sum is the table claim. -/
theorem cubicForm_cube_sum (E A B C D : (Fin m → Bool) → F) :
    ∑ b, cubicForm E A B C D (cubePt b) = ∑ b, (E b * (A b * B b + C b * D b)) :=
  Finset.sum_congr rfl fun b _ => by simp only [cubicForm, mle_agrees]

/-- The value of a table's MLE at the foot of the axis-`i` line through `x`. -/
def lineBase (f : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  mle f (Function.update x i 0)

/-- The slope of a table's MLE along the axis-`i` line through `x`. Multi-affineness
(`mle_multilinear`) says the line is exactly `lineBase + t · lineSlope`. -/
def lineSlope (f : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  mle f (Function.update x i 1) - mle f (Function.update x i 0)

omit [Fintype F] [DecidableEq F] in
/-- The line, in base/slope form — `mle_multilinear`, rearranged. -/
theorem mle_line (f : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) (t : F) :
    mle f (Function.update x i t) = lineBase f i x + t * lineSlope f i x := by
  rw [mle_multilinear f i x t]
  simp only [lineBase, lineSlope]
  ring

/-- The constant coefficient of the INNER factor `Â·B̂ + Ĉ·D̂` on the axis-`i` line. -/
def innerC0 (A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineBase A i x * lineBase B i x + lineBase C i x * lineBase D i x

/-- The linear coefficient of the inner factor. -/
def innerC1 (A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineBase A i x * lineSlope B i x + lineSlope A i x * lineBase B i x
    + (lineBase C i x * lineSlope D i x + lineSlope C i x * lineBase D i x)

/-- The quadratic coefficient of the inner factor — the two cross terms. -/
def innerC2 (A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineSlope A i x * lineSlope B i x + lineSlope C i x * lineSlope D i x

/-- Cubic coefficient 0: `e₀·s₀`. -/
def cubicC0 (E A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineBase E i x * innerC0 A B C D i x

/-- Cubic coefficient 1: `e₀·s₁ + Δe·s₀`. -/
def cubicC1 (E A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineBase E i x * innerC1 A B C D i x + lineSlope E i x * innerC0 A B C D i x

/-- Cubic coefficient 2: `e₀·s₂ + Δe·s₁`. -/
def cubicC2 (E A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineBase E i x * innerC2 A B C D i x + lineSlope E i x * innerC1 A B C D i x

/-- Cubic coefficient 3 — **the leading coefficient**, `Δe·s₂`: the product of the head's
slope with the two cross terms. This is the term the quadratic engine does not have, and
`cubic_leading_ne_zero` shows it is not identically zero. -/
def cubicC3 (E A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) : F :=
  lineSlope E i x * innerC2 A B C D i x

omit [Fintype F] [DecidableEq F] in
/-- **The line restriction is cubic, explicitly.** On every axis-`i` line the summand is
`k₀ + t·k₁ + t²·k₂ + t³·k₃` with the coefficients above — five applications of
`mle_multilinear` and one `ring`. Coefficient form: no division, no characteristic
hypothesis, so the char-2 instantiation is not excluded. -/
theorem cubicForm_line (E A B C D : (Fin m → Bool) → F) (i : Fin m) (x : Fin m → F) (t : F) :
    cubicForm E A B C D (Function.update x i t)
      = cubicC0 E A B C D i x + t * cubicC1 E A B C D i x
        + t ^ 2 * cubicC2 E A B C D i x + t ^ 3 * cubicC3 E A B C D i x := by
  simp only [cubicForm, mle_line, cubicC0, cubicC1, cubicC2, cubicC3,
    innerC0, innerC1, innerC2]
  ring

/-! ## §2. The round polynomial -/

/-- Round `i`'s constant coefficient: `cubicC0` summed over the suffix cube. -/
def cubicRound0 (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) : F :=
  ∑ b : SuffixCube m (i.val + 1), cubicC0 E A B C D i (glue r (i.val + 1) b)

/-- Round `i`'s linear coefficient. -/
def cubicRound1 (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) : F :=
  ∑ b : SuffixCube m (i.val + 1), cubicC1 E A B C D i (glue r (i.val + 1) b)

/-- Round `i`'s quadratic coefficient. -/
def cubicRound2 (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) : F :=
  ∑ b : SuffixCube m (i.val + 1), cubicC2 E A B C D i (glue r (i.val + 1) b)

/-- Round `i`'s CUBIC coefficient — the summed leading term. -/
def cubicRound3 (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) : F :=
  ∑ b : SuffixCube m (i.val + 1), cubicC3 E A B C D i (glue r (i.val + 1) b)

omit [Fintype F] [DecidableEq F] in
/-- **The round partial sum is cubic in the running variable** — `cubicForm_line`, summed
over the suffix cube (`glue_update` rides the running coordinate outside the glue). -/
theorem roundSum_cubicForm (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m)
    (t : F) :
    roundSum (cubicForm E A B C D) r i t
      = cubicRound0 E A B C D r i + t * cubicRound1 E A B C D r i
        + t ^ 2 * cubicRound2 E A B C D r i + t ^ 3 * cubicRound3 E A B C D r i := by
  simp only [roundSum, cubicRound0, cubicRound1, cubicRound2, cubicRound3, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [glue_update t]
  exact cubicForm_line E A B C D i (glue r (i.val + 1) b) t

/-- The round polynomial of the cubic engine, as an actual `Polynomial F`. Degree ≤ 3 by
shape; evaluates to `roundSum` everywhere. -/
noncomputable def cubicRoundPoly (E A B C D : (Fin m → Bool) → F) (r : Fin m → F)
    (i : Fin m) : Polynomial F :=
  Polynomial.C (cubicRound3 E A B C D r i) * X ^ 3
    + Polynomial.C (cubicRound2 E A B C D r i) * X ^ 2
    + Polynomial.C (cubicRound1 E A B C D r i) * X
    + Polynomial.C (cubicRound0 E A B C D r i)

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial IS the round partial sum, at every point. -/
theorem cubicRoundPoly_eval (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m)
    (t : F) :
    (cubicRoundPoly E A B C D r i).eval t = roundSum (cubicForm E A B C D) r i t := by
  rw [roundSum_cubicForm]
  simp only [cubicRoundPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

omit [Fintype F] [DecidableEq F] in
/-- The round polynomial has degree ≤ 3 — the `d = 3` the sumcheck bound consumes. -/
theorem cubicRoundPoly_degree (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) (i : Fin m) :
    (cubicRoundPoly E A B C D r i).degree < ((3 + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_cubic_le (by decide)

/-! ## §3. The honest cubic prover -/

/-- **The honest cubic prover.** Round `i` sends the degree-≤3 partial-sum polynomial of
`Ê·(Â·B̂ + Ĉ·D̂)`; the challenge stream is read only below `i` (constant `0` junk past the
last round, never consulted). -/
noncomputable def cubicHonest (E A B C D : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ) :
    Polynomial F :=
  if h : i < m then cubicRoundPoly E A B C D (fun j : Fin m => χ j.val) ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
/-- The glued line point reads the challenge tuple only strictly below `i` — the ONE
combinatorial fact behind prefix-measurability of all four round coefficients. -/
theorem glue_update_congr_prefix {i : Fin m} {r r' : Fin m → F}
    (h : ∀ j : Fin m, j.val < i.val → r j = r' j) (b : SuffixCube m (i.val + 1)) (t : F) :
    Function.update (glue r (i.val + 1) b) i t
      = Function.update (glue r' (i.val + 1) b) i t := by
  funext j
  rcases eq_or_ne j i with rfl | hne
  · rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hne, Function.update_of_ne hne]
    simp only [glue_apply]
    by_cases hj : i.val + 1 ≤ j.val
    · rw [dif_pos hj, dif_pos hj]
    · rw [dif_neg hj, dif_neg hj]
      have hv : j.val ≠ i.val := fun hv => hne (Fin.ext hv)
      exact h j (by omega)

omit [Fintype F] [DecidableEq F] in
/-- `lineBase` at a glued point reads the challenges only below `i`. -/
theorem lineBase_glue_congr_prefix (f : (Fin m → Bool) → F) {i : Fin m} {r r' : Fin m → F}
    (h : ∀ j : Fin m, j.val < i.val → r j = r' j) (b : SuffixCube m (i.val + 1)) :
    lineBase f i (glue r (i.val + 1) b) = lineBase f i (glue r' (i.val + 1) b) := by
  simp only [lineBase, glue_update_congr_prefix h b]

omit [Fintype F] [DecidableEq F] in
/-- `lineSlope` at a glued point reads the challenges only below `i`. -/
theorem lineSlope_glue_congr_prefix (f : (Fin m → Bool) → F) {i : Fin m} {r r' : Fin m → F}
    (h : ∀ j : Fin m, j.val < i.val → r j = r' j) (b : SuffixCube m (i.val + 1)) :
    lineSlope f i (glue r (i.val + 1) b) = lineSlope f i (glue r' (i.val + 1) b) := by
  simp only [lineSlope, glue_update_congr_prefix h b]

omit [Fintype F] [DecidableEq F] in
/-- All four round coefficients are prefix-measurable. -/
theorem cubicRound_congr_prefix (E A B C D : (Fin m → Bool) → F) {i : Fin m}
    {r r' : Fin m → F} (h : ∀ j : Fin m, j.val < i.val → r j = r' j) :
    cubicRound0 E A B C D r i = cubicRound0 E A B C D r' i
      ∧ cubicRound1 E A B C D r i = cubicRound1 E A B C D r' i
      ∧ cubicRound2 E A B C D r i = cubicRound2 E A B C D r' i
      ∧ cubicRound3 E A B C D r i = cubicRound3 E A B C D r' i := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    refine Finset.sum_congr rfl fun b _ => ?_ <;>
      simp only [cubicC0, cubicC1, cubicC2, cubicC3, innerC0, innerC1, innerC2,
        lineBase_glue_congr_prefix _ h b, lineSlope_glue_congr_prefix _ h b]

omit [Fintype F] [DecidableEq F] in
/-- The honest cubic family is prefix-measurable. -/
theorem cubicHonest_prefixMeasurable (E A B C D : (Fin m → Bool) → F) :
    PrefixMeasurable (cubicHonest E A B C D) := by
  intro χ χ' i hpre
  unfold cubicHonest
  by_cases h : i < m
  · rw [dif_pos h, dif_pos h]
    obtain ⟨h0, h1, h2, h3⟩ :=
      cubicRound_congr_prefix (i := ⟨i, h⟩) E A B C D (fun j hj => hpre j.val hj)
    unfold cubicRoundPoly
    rw [h0, h1, h2, h3]
  · rw [dif_neg h, dif_neg h]

omit [Fintype F] [DecidableEq F] in
/-- The honest cubic family's degree bound: `d = 3`, every round. -/
theorem cubicHonest_degree (E A B C D : (Fin m → Bool) → F) (χ : ℕ → F) (i : ℕ)
    (hi : i < m) :
    (cubicHonest E A B C D χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ) := by
  rw [cubicHonest, dif_pos hi]
  exact cubicRoundPoly_degree E A B C D _ _

omit [Fintype F] [DecidableEq F] in
/-- **Boolean-sum consistency of the cubic honest family** along the truth chain anchored at
the table claim: round 0's target is the claimed total (`roundSum_zero` +
`cubicForm_cube_sum`), every later round's target is the previous round polynomial folded at
the challenge (`roundSum_succ`) — the landed sum-splitting, cited, not re-derived. -/
theorem cubicHonest_boolean_sum (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) :
    ∀ i, i < m →
      (cubicHonest E A B C D (chalOf r) i).eval 0
          + (cubicHonest E A B C D (chalOf r) i).eval 1
        = scChain (∑ b, (E b * (A b * B b + C b * D b)))
            (cubicHonest E A B C D (chalOf r)) (chalOf r) i := by
  intro i hi
  rw [cubicHonest, dif_pos hi, chalOf_restrict, cubicRoundPoly_eval, cubicRoundPoly_eval]
  cases i with
  | zero =>
    show _ = ∑ b, (E b * (A b * B b + C b * D b))
    rw [roundSum_zero hi (cubicForm E A B C D) r, cubicForm_cube_sum]
  | succ n =>
    show _ = (cubicHonest E A B C D (chalOf r) n).eval (chalOf r n)
    have hn : n < m := Nat.lt_of_succ_lt hi
    rw [cubicHonest, dif_pos hn, chalOf_restrict, cubicRoundPoly_eval,
      chalOf_coe r ⟨n, hn⟩]
    exact roundSum_succ hi (cubicForm E A B C D) r

omit [Fintype F] [DecidableEq F] in
/-- **The terminal check, FACTORED.** After all `m` rounds the honest truth chain's value is
`Ê(r)·(Â(r)·B̂(r) + Ĉ(r)·D̂(r))` — FIVE oracle openings the verifier combines itself. This is
the whole reason the round degree is 3: a degree-1 engine would have to target the MLE of the
PRODUCT, which is not the product of the MLEs. -/
theorem scChain_cubicHonest_final (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) :
    scChain (∑ b, (E b * (A b * B b + C b * D b)))
        (cubicHonest E A B C D (chalOf r)) (chalOf r) m
      = mle E r * (mle A r * mle B r + mle C r * mle D r) := by
  cases m with
  | zero =>
    show ∑ b, (E b * (A b * B b + C b * D b)) = _
    have key : ∀ f : (Fin 0 → Bool) → F, mle f r = f default := by
      intro f
      rw [mle,
        Fintype.sum_eq_single default fun b hb =>
          absurd (Subsingleton.elim b default) hb,
        chiEval, Fintype.prod_empty, mul_one]
    rw [key E, key A, key B, key C, key D,
      Fintype.sum_eq_single default fun b hb => absurd (Subsingleton.elim b default) hb]
  | succ n =>
    show (cubicHonest E A B C D (chalOf r) n).eval (chalOf r n) = _
    have hn : n < n + 1 := Nat.lt_succ_self n
    rw [cubicHonest, dif_pos hn, chalOf_restrict, cubicRoundPoly_eval,
      chalOf_coe r ⟨n, hn⟩, roundSum_last rfl (cubicForm E A B C D) r,
      Function.update_eq_self]
    rfl

omit [Fintype F] [DecidableEq F] in
/-- **Completeness of the cubic realizer**: the honest family, run as both prover and truth
chain on the true table total, passes every check on EVERY challenge vector. -/
theorem cubicHonest_complete (E A B C D : (Fin m → Bool) → F) (r : Fin m → F) :
    SumcheckAccepts (v := m) (cubicHonest E A B C D (chalOf r))
      (cubicHonest E A B C D (chalOf r))
      (∑ b, (E b * (A b * B b + C b * D b))) (∑ b, (E b * (A b * B b + C b * D b))) r :=
  ⟨fun i hi => cubicHonest_boolean_sum E A B C D r i hi, rfl⟩

/-- **Soundness against the built cubic realizer.** With the honest side INSTANTIATED at
`cubicHonest`, any prefix-measurable degree-≤3 prover opening with a false total is accepted
with probability at most `m·3/|F|` — `adaptive_sumcheck_soundness` consumed at `d = 3`. The
protocol layer was ALREADY degree-generic; this is the one `simpa` that consumes it. -/
theorem cubic_sumcheck_soundness {E A B C D : (Fin m → Bool) → F}
    {prover : (ℕ → F) → ℕ → Polynomial F} {H : F}
    (hpm : PrefixMeasurable prover)
    (hProverDeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F)
      (AdaptiveAcceptsFalse prover (cubicHonest E A B C D) H
        (∑ b, (E b * (A b * B b + C b * D b))))
      ≤ (m : ℝ) * (3 / Fintype.card F) := by
  have h := adaptive_sumcheck_soundness (v := m) (d := 3) (H := H)
    hpm (cubicHonest_prefixMeasurable E A B C D) hProverDeg
    (fun χ i hi => cubicHonest_degree E A B C D χ i hi)
    (fun r i hi => cubicHonest_boolean_sum E A B C D r i hi)
  simpa using h

/-- The cubic retirement bundle: every admissible prover run against the BUILT honest family
on the constraint's claim, mask folded into the HEAD factor. -/
def CubicRetired {m : ℕ} (E A B C D : (Fin m → Bool) → F)
    (c : LinearConstraint (Fin m → Bool) F) : Prop :=
  ∀ prover : (ℕ → F) → ℕ → Polynomial F,
    PrefixMeasurable prover →
    (∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) →
    uniformProb (Fin m → F)
      (fun r => SumcheckAccepts (prover (chalOf r))
        (cubicHonest (fun b => c.wt b * E b) A B C D (chalOf r))
        c.target (trueSum c (fun b => E b * (A b * B b + C b * D b))) r)
      ≤ (m : ℝ) * (3 / Fintype.card F)

/-- **The cubic retirement keystone.** Any `LinearConstraint` on a cubic-form word that the
word violates is retired by the proven sumcheck with the honest side BUILT: the weight folds
into the HEAD factor (`wt·(E·(A·B+C·D)) = (wt·E)·(A·B+C·D)`, pointwise `ring`), so the
summand keeps its shape and `cubicHonest` realizes the rounds at `d = 3`.
`adaptive_sumcheck_retires_constraint`, cited — no probability re-derived. -/
theorem cubic_retires_constraint {m : ℕ} {E A B C D : (Fin m → Bool) → F}
    {c : LinearConstraint (Fin m → Bool) F}
    (hviol : ¬ Satisfies (fun b => E b * (A b * B b + C b * D b)) c) :
    CubicRetired E A B C D c := by
  intro prover hpm hProverDeg
  have hsum : trueSum c (fun b => E b * (A b * B b + C b * D b))
      = ∑ b, (c.wt b * E b * (A b * B b + C b * D b)) := by
    simp only [trueSum, constraintSummand]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h := adaptive_sumcheck_retires_constraint (v := m) (d := 3)
    (prover := prover)
    (honest := cubicHonest (fun b => c.wt b * E b) A B C D)
    hviol hpm (cubicHonest_prefixMeasurable _ _ _ _ _) hProverDeg
    (fun χ i hi => cubicHonest_degree _ _ _ _ _ χ i hi)
    (fun r i hi => by
      rw [hsum]
      exact cubicHonest_boolean_sum _ _ _ _ _ r i hi)
  simpa using h

end CubicEngine

/-! ## §2. The two consumers, named as THEOREMS

The claim "the same rung serves GKR fraction trees and zkML matmul" is discharged here, not
asserted in prose: each target is exhibited as an INSTANCE of `cubicForm`, so both inherit
`cubic_sumcheck_soundness` and `cubic_retires_constraint` verbatim. -/

section Consumers

variable {m : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- The MLE of a constant table is that constant — uniqueness (`multiAffine_ext`) fires. -/
theorem mle_const (c : F) :
    mle (fun _ : Fin m → Bool => c) = fun _ : Fin m → F => c :=
  multiAffine_ext (mle_multilinear _) (fun _ _ t => by ring)
    (fun b => mle_agrees (fun _ => c) b)

omit [Fintype F] [DecidableEq F] in
/-- `mle` is linear in the table, on the negation side. -/
theorem mle_neg (f : (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => -(f b)) x = -mle f x := by
  simp only [mle, neg_mul, Finset.sum_neg_distrib]

omit [Fintype F] [DecidableEq F] in
/-- **CONSUMER 1 — the elementwise-product zerocheck** `eq·(Â·B̂ − Ĉ)` IS a `cubicForm`:
take the head `E`, the product pair `A, B`, and the second pair `(−C, 1)`.

⚠ This was named `cubicForm_matmul`; it is NOT a matmul (`Â·B̂` is pointwise, a contraction
sums an inner index — `Assurance/ZkmlMatmulSumcheck.lean`'s `matmul_is_not_hadamard`
decides it on data). It is the Hadamard gate's zerocheck face, which is a real consumer. -/
theorem cubicForm_hadamard (E A B C : (Fin m → Bool) → F) :
    cubicForm E A B (fun b => -(C b)) (fun _ => 1)
      = fun x => mle E x * (mle A x * mle B x - mle C x) := by
  funext x
  simp only [cubicForm, mle_neg, mle_const]
  ring

omit [Fintype F] [DecidableEq F] in
/-- **CONSUMER 2 — the GKR fraction-tree layer** `eq(z,x)·(p_L·q_R + p_R·q_L)` IS a
`cubicForm` whose head is the `eq` table `b ↦ χ_b(z)`: `Selvage.eqMle_eq_mle` says that
table's MLE is exactly `eqMle z`. The inversion-free fraction-tree numerator step, inside
this engine. -/
theorem cubicForm_fraction_layer (z : Fin m → F) (pL qR pR qL : (Fin m → Bool) → F) :
    cubicForm (fun b => chiEval b z) pL qR pR qL
      = fun x => eqMle z x * (mle pL x * mle qR x + mle pR x * mle qL x) := by
  funext x
  rw [cubicForm, eqMle_eq_mle z]

omit [Fintype F] [DecidableEq F] in
/-- **The degree-2 engine is a SPECIAL CASE, not a parallel twin**: `prodDiff A B C` is
`cubicForm` with a constant-`1` head and the pair `(−C, 1)`. Anything proved of `cubicForm`
therefore applies to the landed quadratic face's summand, and the two files denote ONE
object. -/
theorem cubicForm_subsumes_prodDiff (A B C : (Fin m → Bool) → F) :
    cubicForm (fun _ => 1) A B (fun b => -(C b)) (fun _ => 1) = prodDiff A B C := by
  funext x
  simp only [cubicForm, prodDiff, mle_neg, mle_const]
  ring

end Consumers

/-! ## §3. Teeth over ZMod 7 — the rung is genuinely cubic

The danger this section exists to refute: a "degree-3 engine" whose leading coefficient is
always zero is a degree-2 engine wearing a cubic type, and every theorem above would still
be true. So the leading coefficient is exhibited NONZERO on data, and a degree-≤2 message is
exhibited INSUFFICIENT to carry the round polynomial. -/

namespace CubicExample

/-- A one-variable instance over F₇: five tables on `{0,1}`. Chosen so all five slopes are
nonzero and the cross terms do not cancel. -/
def tE : (Fin 1 → Bool) → ZMod 7 := fun b => if b 0 then 3 else 1
def tA : (Fin 1 → Bool) → ZMod 7 := fun b => if b 0 then 5 else 2
def tB : (Fin 1 → Bool) → ZMod 7 := fun b => if b 0 then 4 else 1
def tC : (Fin 1 → Bool) → ZMod 7 := fun b => if b 0 then 6 else 2
def tD : (Fin 1 → Bool) → ZMod 7 := fun b => if b 0 then 1 else 3

/-- **TEETH — the rung is genuinely cubic.** The leading coefficient
`Δe·(Δa·Δb + Δc·Δd)` is NONZERO: `Δe = 2`, `Δa·Δb = 3·3 = 2`, `Δc·Δd = 4·(−2) = 4·5 = 6`,
so `s₂ = 1` and `k₃ = 2`. A degree-2 engine cannot produce this message. -/
theorem cubic_leading_ne_zero :
    cubicRound3 tE tA tB tC tD ![0] ⟨0, by norm_num⟩ = 2 := by decide

/-- **TEETH — the round polynomial is not affine and not quadratic.** Its values at
`0, 1, 2, 3` are not fitted by any degree-≤2 polynomial: the third finite difference is the
leading coefficient times `3! = 6`, and it is nonzero here. Stated as the finite-difference
identity, computed. -/
theorem cubic_not_quadratic :
    roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 3
        - 3 * roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 2
        + 3 * roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 1
        - roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 0
      = 6 * cubicRound3 tE tA tB tC tD ![0] ⟨0, by norm_num⟩ := by decide

/-- **TEETH — the round message evaluates to the partial sum off the interpolation nodes.**
The engine is not merely fitted at `{0,1,2,3}`. -/
theorem cubic_round_eval_offnode :
    (cubicRoundPoly tE tA tB tC tD ![0] ⟨0, by norm_num⟩).eval 5
      = roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 5 :=
  cubicRoundPoly_eval tE tA tB tC tD ![0] ⟨0, by norm_num⟩ 5

/-- **TEETH — the boolean check target is the table claim**, computed at m = 1. -/
theorem cubic_chain0 :
    roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 0
        + roundSum (cubicForm tE tA tB tC tD) ![0] ⟨0, by norm_num⟩ 1
      = ∑ b, (tE b * (tA b * tB b + tC b * tD b)) := by decide

/-- **TEETH — the terminal check is FACTORED**, computed: the final fold is the product of
the head opening with the two pair openings, at the challenge `r = 5`. -/
theorem cubic_final_factored :
    roundSum (cubicForm tE tA tB tC tD) ![5] ⟨0, by norm_num⟩ 5
      = mle tE ![5] * (mle tA ![5] * mle tB ![5] + mle tC ![5] * mle tD ![5]) := by decide

/-! ### The soundness pipeline, END-TO-END with a NONEMPTY accept event

A bound over an empty event is a true statement about nothing. So the cheat below is
constructed BACKWARDS from a challenge that accepts it: the round polynomial of the honest
family at `m = 1` is `f(t) = 1 + 5t + 2t³` over F₇, and `cubicCheat` is the affine message
through `(0, 2)` and `(1, 4)` — its boolean check sums to the FALSE total `6` (the truth is
`2`), and it meets the honest fold at `t = 2`, where `f(2) = 6`. -/

/-- A cheating prover: the affine message `2X + 2`, sent every round regardless of the
challenge stream. Its boolean check sums to `6`, a total the tables do not have. -/
noncomputable def cubicCheat : (ℕ → ZMod 7) → ℕ → Polynomial (ZMod 7) :=
  fun _ _ => Polynomial.C 2 * X + Polynomial.C 2

/-- The true total is `2`; the cheat claims `6`. -/
theorem cubic_true_total : (∑ b, (tE b * (tA b * tB b + tC b * tD b))) = 2 := by decide

/-- **The soundness bound FIRES end-to-end on the built cubic realizer**: the cheating
prover claiming `6` against the honest cubic family is accepted with probability at most
`3/7` — `cubic_sumcheck_soundness` at `m = 1`, `d = 3`. -/
theorem cubic_cheat_caught :
    uniformProb (Fin 1 → ZMod 7)
      (AdaptiveAcceptsFalse cubicCheat (cubicHonest tE tA tB tC tD) 6
        (∑ b, (tE b * (tA b * tB b + tC b * tD b))))
      ≤ 3 / 7 := by
  have h := cubic_sumcheck_soundness (E := tE) (A := tA) (B := tB) (C := tC) (D := tD)
    (prover := cubicCheat) (H := 6)
    (fun _ _ _ _ => rfl)
    (fun _ i _ => by
      unfold cubicCheat
      exact lt_of_le_of_lt Polynomial.degree_linear_le (by decide))
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- **The caught-event is NONEMPTY**: at the challenge `r = 2` the cheat IS accepted — the
round check passes on the false total `6`, and the fold value `2·2+2 = 6` equals the honest
factored terminal value `Ê(2)·(Â(2)·B̂(2) + Ĉ(2)·D̂(2)) = 6`. So `cubic_cheat_caught`
constrains a real event, not a vacuum. -/
theorem cubic_cheat_witness :
    AdaptiveAcceptsFalse cubicCheat (cubicHonest tE tA tB tC tD) 6
      (∑ b, (tE b * (tA b * tB b + tC b * tD b))) ![2] := by
  refine ⟨fun i hi => ?_, ?_, by decide⟩
  · have h0 : i = 0 := by omega
    subst h0
    simp only [cubicCheat, scChain, eval_add, eval_mul, eval_C, eval_X]
    decide
  · show scChain (6 : ZMod 7) _ _ 1 = _
    rw [scChain_cubicHonest_final tE tA tB tC tD ![2]]
    show (cubicCheat (chalOf ![2]) 0).eval (chalOf ![(2 : ZMod 7)] 0) = _
    unfold cubicCheat
    simp
    decide

end CubicExample

/-! ## §4. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.cubicForm_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicForm_line
/-- info: 'Minidregg.Assurance.roundSum_cubicForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundSum_cubicForm
/-- info: 'Minidregg.Assurance.cubicRoundPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicRoundPoly_eval
/-- info: 'Minidregg.Assurance.cubicRoundPoly_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicRoundPoly_degree
/-- info: 'Minidregg.Assurance.cubicHonest_prefixMeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicHonest_prefixMeasurable
/-- info: 'Minidregg.Assurance.cubicHonest_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicHonest_degree
/-- info: 'Minidregg.Assurance.cubicHonest_boolean_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicHonest_boolean_sum
/-- info: 'Minidregg.Assurance.scChain_cubicHonest_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scChain_cubicHonest_final
/-- info: 'Minidregg.Assurance.cubicHonest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicHonest_complete
/-- info: 'Minidregg.Assurance.cubic_sumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubic_sumcheck_soundness
/-- info: 'Minidregg.Assurance.cubic_retires_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubic_retires_constraint
/-- info: 'Minidregg.Assurance.cubicForm_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicForm_hadamard
/-- info: 'Minidregg.Assurance.cubicForm_fraction_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicForm_fraction_layer
/-- info: 'Minidregg.Assurance.cubicForm_subsumes_prodDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicForm_subsumes_prodDiff
/-- info: 'Minidregg.Assurance.CubicExample.cubic_leading_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CubicExample.cubic_leading_ne_zero
/-- info: 'Minidregg.Assurance.CubicExample.cubic_not_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CubicExample.cubic_not_quadratic
/-- info: 'Minidregg.Assurance.CubicExample.cubic_cheat_caught' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CubicExample.cubic_cheat_caught
/-- info: 'Minidregg.Assurance.CubicExample.cubic_cheat_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CubicExample.cubic_cheat_witness

end Minidregg.Assurance
