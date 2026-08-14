/-
# `Assurance/SpartanR1CS.lean` — Spartan's two sumcheck phases, over the landed engines

**Substrate, said out loud: this is Lean-authored.** Every object below is a Lean definition and
every claim about it is a Lean theorem over Selvage's proven sumcheck. No Rust AIR is written,
extended or implied by this file.

## What Spartan is, and what this file settles

Spartan (Setty, CRYPTO 2020) proves R1CS satisfiability — `(Az) ∘ (Bz) = Cz` — by three moves:

1. a **zerocheck randomization**: `Q(τ) = Σ_a eq(τ,a)·((Az)(a)·(Bz)(a) − (Cz)(a))`, which is `0`
   for every `τ` when `z` satisfies and is nonzero at a random `τ` when it does not;
2. an **outer sumcheck** of degree 3 on `eq(τ,x)·(Âz(x)·B̂z(x) − Ĉz(x))` over the CONSTRAINT cube,
   whose terminal check is factored into openings the verifier combines itself;
3. an **inner sumcheck** of degree 2 on `Σ_y wtγ(y)·z̃(y)` over the VARIABLE cube, where `wtγ` is
   a γ-power batch of the three rows `Ã(r_x,·)`, `B̃(r_x,·)`, `C̃(r_x,·)`, terminating in two
   openings: `wt̃γ(r_y)` and `z̃(r_y)`.

Everything needed for (1)–(3) was already in the tree, at three different files, aimed at three
different consumers. This file composes them at the R1CS instance and states the result as
`spartan_outer_sound`, `spartan_inner_batch_sound`, `spartan_inner_sound` and — the object the
PCS/commitment lanes can aim at — `spartanTerminal_eq_honest` and `spartan_inner_terminal`.

## The pieces, and where each comes from (nothing here re-derives a probability)

* zerocheck bridge — `Selvage.eqMle_fold` (identity) and `Selvage.mle_zero_uniform_bound`
  (multilinear Schwartz–Zippel, `≤ m/|F|`). ⚑ Both are LANDED; the residual (ii) that
  `Assurance/AirSumcheckQuadratic.lean`'s docblock still names as "not yet vocabulary" was closed
  by `Selvage/MultilinearZeroTest.lean`. That docblock is stale, not a gap.
* outer round engine — `Assurance.cubicForm` / `cubicHonest` / `cubic_sumcheck_soundness`
  (`≤ m·3/|F|`). The `eq` head arrives through `cubicForm_fraction_layer`'s vocabulary
  (`Selvage.eqMle_eq_mle`) and the `Â·B̂ − Ĉ` body through `cubicForm_hadamard`; Spartan's outer
  summand is the COMPOSITION of the rung's two named consumers, which is why it costs no new
  realizer.
* inner round engine — `Selvage.quadHonest` / `quad_sumcheck_soundness` (`≤ m·2/|F|`), with the
  FACTORED terminal `scChain_quadHonest_final`.
* the batch — `Selvage.batch_survives_prob_le` at `length − 1 = 2`. ⚑ The three inner claims are
  literally three `Selvage.LinearConstraint` values ON THE WITNESS WORD (`innerClaim`), so the
  landed γ-batching machinery applies verbatim with nothing new proved.
* the matrix-times-witness identity — `Assurance.mle₂_contraction` at `ν = 0`. `matVec` is
  exhibited as that instance (`matVec_is_contraction_at_nu_zero`) rather than restated, so the
  contraction file and this one denote ONE object.

## What is proved here (no `sorry`)

* `r1csSat_iff_defect_zero` — satisfaction IS the vanishing of the defect word.
* `mle_matVec` — **the inner-sumcheck identity**: `(Az)^(x) = Σ_y Ã(x,y)·z̃(y)`, at every `x`.
* `spartanOuterForm` / `spartanOuterTotal` — the outer summand is a `cubicForm` and its cube total
  is `defect^(τ)`. (`spartanOuterForm` is not consumed by the soundness proof; it is the statement
  that the engine instance really is Spartan's summand, and would be the thing to distrust first.)
* `spartan_outer_sound` — **the outer reduction.** An UNSATISFIED R1CS is accepted with
  probability at most `s/|F| + s·3/|F|` over the joint draw of `τ` and the `s` sumcheck
  challenges. Two events, two causes, added; the flattering half is not quoted alone.
* `spartanTerminal_eq_honest` — **the hand-off.** The verifier's own terminal expression
  `eq(τ,r_x)·(v_A·v_B − v_C)` equals the honest truth chain's final value exactly when the three
  `v`s are the three true row-openings. This names, as a theorem rather than prose, what phase 2
  must certify.
* `innerClaim_satisfied_iff` — a phase-2 claim is a linear constraint on the witness word, and it
  holds iff the claimed value is the true one.
* `spartan_inner_batch_sound` — a wrong triple survives the γ-batch for at most `2/|F|` of γ.
* `spartan_inner_sound` — **the inner reduction**, `≤ t·2/|F|`, honest side BUILT.
* `spartan_inner_terminal` — the inner terminal, FACTORED as `wt̃γ(r_y)·z̃(r_y)`, and
  `mle_rowPartial_eq_mle₂` identifies an unbatched row opening with `Ã(r_x,r_y)`.
* `spartan_reduces_to_two_openings` — the scope statement as a theorem: with the three row values
  correct, the whole outer terminal is determined by data the verifier already holds.

## What is NOT proved here, named

`[SPARTAN-pcs]` — the two terminal openings (`z̃(r_y)` and `wt̃γ(r_y)`) are handed to the
verifier as values. `Selvage/MultilinearCommitment.lean`'s `MleEvalClaim` is the claim object and
`basefoldWord_injective` is the binding step; the OPENING PROTOCOL is BaseFold's braided reduction
(or, in the BinarySpartan shape, Ligerito). `spartanOpeningsBound` states the binding consequence
this file needs, and `SpartanOpeningProtocol` is the named obligation for the protocol itself.

`[SPARTAN-sparse]` — ⚑ **and this is a COST obligation, not a soundness one.** The row weights
`rowPartial A r_x` and the openings `Ã(r_x,r_y)` are here computed from the DENSE table `A`. That
is sound (`spartanOpeningsBound` closes it against a binding commitment to `flatten₂ A`), and it
is what makes the verifier LINEAR in the matrix rather than sublinear. Spartan's SPARK layer —
sparse multilinear commitment by offline memory checking — is what buys sublinearity, and it does
not exist in this tree at all (no timestamp vectors, no multiset check). `SpartanSparseEvalOracle`
names the interface a sparse scheme must present; nothing here discharges it.

`[SPARTAN-fs]` — the two phases are analyzed over independent uniform draws. The deployed object
is one Fiat–Shamir transcript; Selvage's RBR→FS/BCS cone is the compiler, and threading these two
sumchecks through it is not attempted here.

## The characteristic question, since it is why this file exists

Nothing below carries a characteristic hypothesis. The binders are `[Field F] [Fintype F]
[DecidableEq F]` throughout, inherited from the engines: the cubic rung's line restriction is
COEFFICIENT-form (`AirSumcheckCubic.cubicForm_line`), the quadratic rung's is the same shape, and
`mle_zero_uniform_bound` peels the LSB coordinate with no division. In particular **nothing here
is downstream of `Selvage/Proximity.lean`'s `FoldingData`**, whose `two_ne : (2 : F) ≠ 0` field is
uninhabitable in characteristic two — `Selvage.mle_lsb_recurrence` takes no `FoldingData`
argument, and no theorem in this file mentions one. What is char-sensitive is the USEFULNESS of
the bounds, not their proofs: every term is `k/|F|`, so the sumchecks must run in a large
extension. That is what ring-switching is for, and it is a parameter fact, not a proof obstruction.

## Teeth (ZMod 7, `s = t = 1`)

The instance is the SQUARING gate `w·w = v` over F₇, deliberately not a `C = 0` instance (which
the zero witness would satisfy for free). Against the vacuity that would survive a build: the bad
witness is genuinely UNSATISFYING (`badZ_unsat`) while a DIFFERENT witness on the same instance
satisfies (`goodZ_sat`), so the hypothesis of `spartan_outer_sound` discriminates between two live
witnesses rather than describing an empty relation; the defect word's extension really does vanish
at a specific zerocheck point (`badZ_survives_at_one` — the `s/|F|` event is NONEMPTY and
exhibited) and is separated elsewhere (`badZ_caught_at_three`), so the zerocheck is not a
formality; the inner claim predicate fires BOTH ways (`innerClaim_fires` through the iff,
`innerClaim_refuses` by computation); and `terminal_fires` computes the hand-off expression to a
specific nonzero field element, so `spartanTerminal_eq_honest` is not an equation between two
constants.
-/
import Assurance.ZkmlMatmulCommitment
import Assurance.ZkmlLowRankUpdate

namespace Minidregg.Assurance

open Minidregg.Selvage Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. R1CS on the hypercube, and the defect word

`s` indexes the CONSTRAINT cube (`2^s` rows), `t` the VARIABLE cube (`2^t` witness entries).
Padding a non-dyadic R1CS to a power of two is deployment bookkeeping, exactly as in the gate
encodings of `AirSumcheckQuadratic`. -/

section R1CS

variable {s t : ℕ}

/-- One R1CS coefficient matrix, as a table on (constraint cube) × (variable cube). -/
abbrev R1CSMatrix (F : Type) (s t : ℕ) := (Fin s → Bool) → (Fin t → Bool) → F

/-! `matVec` — `(Az)(a) = Σ_y A a y · z y` — is NOT defined here. It is
`Assurance/ZkmlLowRankUpdate.lean`'s, imported: the low-rank file needed the same object for
`matVec_matmulTable` ("the cheap evaluation order is legal") and defining a second one would have
been a twin that agrees today. This file's first draft did define one; the umbrella build caught
it as a name clash, which is the cheapest possible way to be told. -/

/-- The witness presented as a one-column matrix — the `ν = 0` right factor. -/
def asColumn (z : (Fin t → Bool) → F) : (Fin t → Bool) → (Fin 0 → Bool) → F := fun y _ => z y

omit [Fintype F] [DecidableEq F] in
/-- **`matVec` IS the landed contraction at `ν = 0`** — one object, not a twin. The contraction
file's `matmulTable` at a trivial output-column index is `matVec` definitionally, which is why
`mle_matVec` below is `mle₂_contraction` specialized rather than a second reordering proof. -/
theorem matVec_is_contraction_at_nu_zero (A : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (a : Fin s → Bool) (b : Fin 0 → Bool) :
    matmulTable A (asColumn z) a b = matVec A z a := rfl

omit [Fintype F] [DecidableEq F] in
/-- **THE INNER-SUMCHECK IDENTITY.** `(Az)^(x) = Σ_y Ã(x,y)·z̃(y)` at EVERY `x`, not just at cube
corners — `mle₂_contraction` at `ν = 0`, with the trivial column index collapsed by `mle_const`.
This is what turns the outer sumcheck's terminal opening `v_A` into a sum-claim over the variable
cube, i.e. it is the whole reason Spartan has a second phase. -/
theorem mle_matVec (A : R1CSMatrix F s t) (z : (Fin t → Bool) → F) (x : Fin s → F) :
    mle (matVec A z) x = ∑ y, rowPartial A x y * z y := by
  have hcol : ∀ p : Fin t → Bool, colPartial (asColumn z) (![] : Fin 0 → F) p = z p := by
    intro p
    exact congrFun (mle_const (m := 0) (z p)) _
  have hleft : mle₂ (matmulTable A (asColumn z)) x (![] : Fin 0 → F) = mle (matVec A z) x := by
    rw [mle₂_col]
    congr 1
    funext a
    exact congrFun (mle_const (m := 0) (matVec A z a)) _
  rw [← hleft, mle₂_contraction]
  exact Finset.sum_congr rfl fun p _ => by rw [hcol p]

/-- R1CS satisfaction: the Hadamard identity holds at every constraint corner. -/
def R1CSSat (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F) : Prop :=
  ∀ a, matVec A z a * matVec B z a = matVec C z a

/-- The defect word on the constraint cube: `D(a) = (Az)(a)·(Bz)(a) − (Cz)(a)`. -/
def r1csDefect (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F) : (Fin s → Bool) → F :=
  fun a => matVec A z a * matVec B z a - matVec C z a

omit [Fintype F] [DecidableEq F] in
/-- Satisfaction IS the vanishing of the defect word — the reshaping every later step consumes. -/
theorem r1csSat_iff_defect_zero (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F) :
    R1CSSat A B C z ↔ r1csDefect A B C z = 0 := by
  constructor
  · intro h
    funext a
    show matVec A z a * matVec B z a - matVec C z a = 0
    rw [h a, sub_self]
  · intro h a
    have ha : matVec A z a * matVec B z a - matVec C z a = 0 := congrFun h a
    exact sub_eq_zero.mp ha

end R1CS

/-! ## §2. The outer phase — Spartan's zerocheck as a `cubicForm` instance

The head is the `eq(τ,·)` table on the constraint cube; the body is `Âz·B̂z − Ĉz`. Both are named
consumers of the degree-3 rung (`cubicForm_fraction_layer`, `cubicForm_hadamard`); Spartan's outer
summand is their composition, so no realizer is built here. -/

section Outer

variable {s t : ℕ}

/-- The outer summand's head table: `a ↦ χ_a(τ)`, whose MLE is `eq(τ,·)` (`eqMle_eq_mle`). -/
def eqHead (τ : Fin s → F) : (Fin s → Bool) → F := fun a => chiEval a τ

omit [Fintype F] [DecidableEq F] in
/-- **The outer summand IS Spartan's**: the degree-3 rung at head `eqHead τ`, pair
`(Âz, B̂z)`, second pair `(−Ĉz, 1)`, evaluates to `eq(τ,x)·(Âz(x)·B̂z(x) − Ĉz(x))` at every `x`. -/
theorem spartanOuterForm (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F) (τ : Fin s → F) :
    cubicForm (eqHead τ) (matVec A z) (matVec B z)
        (fun a => -(matVec C z a)) (fun _ => 1)
      = fun x => eqMle τ x
          * (mle (matVec A z) x * mle (matVec B z) x - mle (matVec C z) x) := by
  rw [cubicForm_hadamard]
  funext x
  rw [show mle (eqHead τ) x = eqMle τ x from (congrFun (eqMle_eq_mle τ) x).symm]

omit [Fintype F] [DecidableEq F] in
/-- **The outer claim total is `D^(τ)`** — `eqMle_fold` in the cubic engine's exact syntactic
shape, so `cubic_sumcheck_soundness` can be consumed without restating the claim. -/
theorem spartanOuterTotal (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F) (τ : Fin s → F) :
    (∑ a, (eqHead τ a
        * (matVec A z a * matVec B z a + (-(matVec C z a)) * (1 : F))))
      = mle (r1csDefect A B C z) τ := by
  rw [mle]
  exact Finset.sum_congr rfl fun a _ => by
    simp only [eqHead, r1csDefect]
    ring

/-- The honest outer prover: the landed cubic realizer at Spartan's instance. Nothing new is
realized — all four honest-side hypotheses are already discharged for `cubicHonest`. -/
noncomputable def spartanOuterHonest (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (τ : Fin s → F) : (ℕ → F) → ℕ → Polynomial F :=
  cubicHonest (eqHead τ) (matVec A z) (matVec B z) (fun a => -(matVec C z a)) (fun _ => 1)

/-- One draw of the outer phase: the zerocheck point `τ`, then the `s` sumcheck challenges. The
prover's CLAIMED total is the constant `0` — that is exactly the zerocheck's assertion — and the
honest truth chain is anchored at the actual value `D^(τ)`. -/
def SpartanOuterAccepts (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (w : (Fin s → F) × (Fin s → F)) : Prop :=
  SumcheckAccepts (v := s) (prover (chalOf w.2))
    (spartanOuterHonest A B C z w.1 (chalOf w.2))
    0 (mle (r1csDefect A B C z) w.1) w.2

/-- **THE OUTER REDUCTION.** A witness that does NOT satisfy the R1CS is accepted by the outer
phase with probability at most

  `s/|F|`      — the zerocheck point failed to separate the defect word from zero,
  `+ s·3/|F|`  — the degree-3 sumcheck was laundered,

with the honest side BUILT (`spartanOuterHonest`) and only adversary-side hypotheses assumed. The
two terms are different events with different causes; adding them is the content, and quoting
either alone would be quoting a flattering half. -/
theorem spartan_outer_sound {A B C : R1CSMatrix F s t} {z : (Fin t → Bool) → F}
    (hunsat : ¬ R1CSSat A B C z)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < s →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb ((Fin s → F) × (Fin s → F)) (SpartanOuterAccepts A B C z prover)
      ≤ (s : ℝ) / Fintype.card F + (s : ℝ) * (3 / Fintype.card F) := by
  have hD : r1csDefect A B C z ≠ 0 := fun h => hunsat ((r1csSat_iff_defect_zero A B C z).mpr h)
  have hstep : ∀ w : (Fin s → F) × (Fin s → F), SpartanOuterAccepts A B C z prover w →
      (mle (r1csDefect A B C z) w.1 = 0
        ∨ AdaptiveAcceptsFalse prover (spartanOuterHonest A B C z w.1)
            0 (mle (r1csDefect A B C z) w.1) w.2) := by
    intro w hw
    by_cases hEq : (0 : F) = mle (r1csDefect A B C z) w.1
    · exact Or.inl hEq.symm
    · exact Or.inr (acceptsFalse_iff_accepts.mpr ⟨hw, hEq⟩)
  refine le_trans (uniformProb_mono hstep) ?_
  refine le_trans (uniformProb_or_le _ _) (add_le_add ?_ ?_)
  · -- The zerocheck point failed to separate: multilinear Schwartz–Zippel.
    exact uniformProb_fst_le _ (fun τ => mle (r1csDefect A B C z) τ = 0)
      (fun _ => Iff.rfl) (by positivity) (mle_zero_uniform_bound hD)
  · -- The sumcheck was laundered: the cubic bound, at every fixed zerocheck point.
    refine uniformProb_prod_le (by positivity) fun τ => ?_
    show uniformProb (Fin s → F)
      (fun r => AdaptiveAcceptsFalse prover (spartanOuterHonest A B C z τ)
        0 (mle (r1csDefect A B C z) τ) r) ≤ _
    have h := cubic_sumcheck_soundness (E := eqHead τ) (A := matVec A z) (B := matVec B z)
      (C := fun a => -(matVec C z a)) (D := fun _ => (1 : F)) (H := (0 : F)) hpm hdeg
    rwa [spartanOuterTotal A B C z τ] at h

end Outer

/-! ## §3. The hand-off — exactly which three values phase 2 must certify

The outer verifier's terminal check compares its own folded claim against the honest chain's final
value, which `scChain_cubicHonest_final` renders as the FACTORED product of five openings. Four of
the five the verifier can compute itself (the `eq` head at `(τ, r_x)`, and the constant `1`); the
remaining three are `v_A = Âz(r_x)`, `v_B`, `v_C`. THAT is Spartan's phase-2 obligation, stated
here as a theorem rather than as prose. -/

section Handoff

variable {s t : ℕ}

/-- The expression the outer verifier evaluates for itself at the end of phase 1, given the three
claimed row values. `eq(τ,r_x)` is computed by the verifier; `v_A, v_B, v_C` are supplied. -/
def spartanTerminal (τ rx : Fin s → F) (vA vB vC : F) : F :=
  eqMle τ rx * (vA * vB - vC)

omit [Fintype F] [DecidableEq F] in
/-- **THE HAND-OFF, as a theorem.** The verifier's own terminal expression equals the honest truth
chain's final value exactly when the three supplied values are the three true row openings. So the
outer phase is complete precisely modulo certifying `Âz(r_x)`, `B̂z(r_x)`, `Ĉz(r_x)` — no more and
no fewer obligations, and the `eq` factor is NOT one of them. -/
theorem spartanTerminal_eq_honest (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (τ rx : Fin s → F) {vA vB vC : F}
    (hA : vA = mle (matVec A z) rx) (hB : vB = mle (matVec B z) rx)
    (hC : vC = mle (matVec C z) rx) :
    spartanTerminal τ rx vA vB vC
      = scChain (mle (r1csDefect A B C z) τ)
          (spartanOuterHonest A B C z τ (chalOf rx)) (chalOf rx) s := by
  rw [← spartanOuterTotal A B C z τ, spartanOuterHonest, scChain_cubicHonest_final,
    spartanTerminal, hA, hB, hC, mle_neg,
    show mle (eqHead τ) rx = eqMle τ rx from (congrFun (eqMle_eq_mle τ) rx).symm,
    show mle (fun _ : Fin s → Bool => (1 : F)) rx = 1 from congrFun (mle_const (1 : F)) rx]
  ring

omit [Fintype F] [DecidableEq F] in
/-- **The scope statement, as a theorem.** With the three row values certified, the whole of phase
1's terminal check is determined by data the verifier holds: it never needs the witness table, the
matrices, or any further oracle. What remains after this equation is exactly phase 2 plus the two
openings it terminates in. -/
theorem spartan_reduces_to_two_openings (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (τ rx : Fin s → F) :
    scChain (mle (r1csDefect A B C z) τ)
        (spartanOuterHonest A B C z τ (chalOf rx)) (chalOf rx) s
      = spartanTerminal τ rx
          (mle (matVec A z) rx) (mle (matVec B z) rx) (mle (matVec C z) rx) :=
  (spartanTerminal_eq_honest A B C z τ rx rfl rfl rfl).symm

end Handoff

/-! ## §4. The inner phase — three linear constraints on the WITNESS word

⚑ The observation that makes this cheap: `v_A = Âz(r_x) = Σ_y Ã(r_x,y)·z̃(y)` (`mle_matVec`) is a
`Selvage.LinearConstraint` on the witness word `z`, with weight the matrix row `rowPartial A r_x`
and target the claimed value. So the landed constraint machinery — γ-batching included — applies
verbatim, and the batched claim's summand `wtγ(y)·z(y)` is a `prodDiff` with `C ≡ 0`, i.e. the
landed degree-2 engine with a FACTORED terminal `wt̃γ(r_y)·z̃(r_y)`. -/

section Inner

variable {s t : ℕ}

/-- One phase-2 claim, as a linear constraint on the witness word. -/
def innerClaim (A : R1CSMatrix F s t) (rx : Fin s → F) (v : F) :
    LinearConstraint (Fin t → Bool) F :=
  ⟨rowPartial A rx, v⟩

omit [Fintype F] [DecidableEq F] in
/-- The claim predicate is faithful: it holds iff the claimed value is the true row opening. -/
theorem innerClaim_satisfied_iff (A : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (rx : Fin s → F) (v : F) :
    Satisfies z (innerClaim A rx v) ↔ v = mle (matVec A z) rx := by
  rw [Satisfies, innerClaim, dotWt, ← mle_matVec]
  exact eq_comm

/-- The three phase-2 claims, in the order Spartan batches them. -/
def innerBatch (A B C : R1CSMatrix F s t) (rx : Fin s → F) (vA vB vC : F) :
    List (LinearConstraint (Fin t → Bool) F) :=
  [innerClaim A rx vA, innerClaim B rx vB, innerClaim C rx vC]

/-- **The γ-batch retires a wrong triple.** If ANY of the three claimed values is wrong, the
γ-power batch is satisfied for at most `2/|F|` of γ — `batch_survives_prob_le` at
`length − 1 = 2`, cited, no probability re-derived. -/
theorem spartan_inner_batch_sound (A B C : R1CSMatrix F s t) (z : (Fin t → Bool) → F)
    (rx : Fin s → F) {vA vB vC : F}
    (hbad : vA ≠ mle (matVec A z) rx ∨ vB ≠ mle (matVec B z) rx
      ∨ vC ≠ mle (matVec C z) rx) :
    uniformProb F
        (fun γ => Satisfies z (batchConstraint γ (innerBatch A B C rx vA vB vC)))
      ≤ (2 : ℝ) / Fintype.card F := by
  have hex : ∃ c ∈ innerBatch A B C rx vA vB vC, ¬ Satisfies z c := by
    rcases hbad with h | h | h
    · exact ⟨innerClaim A rx vA, by simp [innerBatch],
        fun hs => h ((innerClaim_satisfied_iff A z rx vA).mp hs)⟩
    · exact ⟨innerClaim B rx vB, by simp [innerBatch],
        fun hs => h ((innerClaim_satisfied_iff B z rx vB).mp hs)⟩
    · exact ⟨innerClaim C rx vC, by simp [innerBatch],
        fun hs => h ((innerClaim_satisfied_iff C z rx vC).mp hs)⟩
  have h := batch_survives_prob_le (f := z) hex
  simpa [innerBatch] using h

/-- The honest inner prover: the landed degree-2 realizer on the summand `wtγ(y)·z(y)` — a
`prodDiff` with the third table identically zero, so the terminal check is FACTORED. -/
noncomputable def spartanInnerHonest (cγ : LinearConstraint (Fin t → Bool) F)
    (z : (Fin t → Bool) → F) : (ℕ → F) → ℕ → Polynomial F :=
  quadHonest cγ.wt z (fun _ => 0)

omit [Fintype F] [DecidableEq F] in
/-- The inner claim's true total is the constraint pairing `dotWt wtγ z`. -/
theorem spartanInnerTotal (cγ : LinearConstraint (Fin t → Bool) F)
    (z : (Fin t → Bool) → F) :
    (∑ y, (cγ.wt y * z y - (0 : F))) = dotWt cγ.wt z := by
  rw [dotWt]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **THE INNER REDUCTION.** Any prefix-measurable degree-≤2 prover opening the batched claim with
a false total is accepted with probability at most `t·2/|F|`, honest side BUILT
(`spartanInnerHonest`) — `quad_sumcheck_soundness` at Spartan's instance, bound cited. -/
theorem spartan_inner_sound {cγ : LinearConstraint (Fin t → Bool) F}
    {z : (Fin t → Bool) → F} {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < t →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin t → F)
      (AdaptiveAcceptsFalse prover (spartanInnerHonest cγ z) cγ.target (dotWt cγ.wt z))
      ≤ (t : ℝ) * (2 / Fintype.card F) := by
  have h := quad_sumcheck_soundness (A := cγ.wt) (B := z) (C := fun _ => (0 : F))
    (H := cγ.target) hpm hdeg
  rwa [spartanInnerTotal cγ z] at h

omit [Fintype F] [DecidableEq F] in
/-- **The inner terminal, FACTORED**: after `t` rounds the honest chain's value is
`wt̃γ(r_y)·z̃(r_y)` — TWO openings, which is the whole reason the inner rung is degree 2 and not
degree 1. -/
theorem spartan_inner_terminal (cγ : LinearConstraint (Fin t → Bool) F)
    (z : (Fin t → Bool) → F) (ry : Fin t → F) :
    scChain (dotWt cγ.wt z) (spartanInnerHonest cγ z (chalOf ry)) (chalOf ry) t
      = mle cγ.wt ry * mle z ry := by
  rw [← spartanInnerTotal cγ z, spartanInnerHonest, scChain_quadHonest_final,
    show mle (fun _ : Fin t → Bool => (0 : F)) ry = 0 from congrFun (mle_const (0 : F)) ry,
    sub_zero]

omit [Fintype F] [DecidableEq F] in
/-- An unbatched row weight's opening IS the matrix's two-block MLE at `(r_x, r_y)` — so the
inner terminal's first factor is Spartan's `Ã(r_x,r_y)` and not some other object. -/
theorem mle_rowPartial_eq_mle₂ (A : R1CSMatrix F s t) (rx : Fin s → F) (ry : Fin t → F) :
    mle (rowPartial A rx) ry = mle₂ A rx ry :=
  (mle₂_row A rx ry).symm

end Inner

/-! ## §5. The two named obligations

House law: what is not proved is a named `Prop`, not prose and not a placeholder that quietly reads
as `True`. Both obligations below are stated so that they are REFUTABLE — each has an instance a
counterexample would break — and neither is discharged here. -/

section Obligations

variable {s t : ℕ}

/-- **`[SPARTAN-pcs]` — the opening-protocol obligation.** A phase-2 transcript terminates in two
claimed values at the point `r_y`. This `Prop` says a scheme delivers them SOUNDLY: every claim it
accepts at a root is the true evaluation of the table that root commits.

Stated over `Selvage.MleEvalClaim`, the landed claim object, so a discharging lane (BaseFold's
braided reduction, or Ligerito) proves exactly this and not a re-spelling. It is refutable: a
scheme that accepts any value at any root falsifies it as soon as two values differ. -/
def SpartanOpeningProtocol {Root ι Op : Type} (S : BindingCommitment Root F ι Op)
    (dom : ι ↪ F) (Accepts : MleEvalClaim Root F t → Prop) : Prop :=
  ∀ c : MleEvalClaim Root F t, Accepts c → c.Holds S dom

omit [Fintype F] in
/-- The binding consequence this file actually needs, and it is PROVED, not assumed: at a known
honest root inside the degree window, a true claim's value is the table's MLE. The obligation
above is about the PROTOCOL that produces accepted claims; binding itself is landed
(`basefoldWord_injective`). -/
theorem spartanOpeningsBound {Root ι Op : Type} [Fintype ι]
    (S : BindingCommitment Root F ι Op) (dom : ι ↪ F)
    (hcard : 2 ^ t ≤ Fintype.card ι) (table : (Fin t → Bool) → F)
    (c : MleEvalClaim Root F t) (hrt : c.rt = S.commit (basefoldWord dom table))
    (hc : c.Holds S dom) :
    c.val = mle table c.pt :=
  ((MleEvalClaim.holds_iff_of_committed S dom hcard table c hrt).mp hc).symm

/-- **`[SPARTAN-sparse]` — the COST obligation, and it is deliberately not a soundness one.**
Everything above computes the row weights `rowPartial A r_x` and the openings `Ã(r_x,r_y)` from
the DENSE matrix table. That is sound; it is also linear in `2^(s+t)`, which is what Spartan's
SPARK layer (sparse multilinear commitment by offline memory checking) exists to remove.

This `Prop` names the interface such a layer must present: an accepted evaluation claim about the
matrix agrees with the dense MLE. Discharging it requires machinery that does not exist in this
tree at all — no timestamp vectors, no multiset/permutation check, no computation commitment.
Refutable by construction: an oracle that accepts a wrong value at `(r_x, r_y)` falsifies it. -/
def SpartanSparseEvalOracle (A : R1CSMatrix F s t)
    (Accepts : (Fin s → F) → (Fin t → F) → F → Prop) : Prop :=
  ∀ (x : Fin s → F) (y : Fin t → F) (v : F), Accepts x y v → v = mle₂ A x y

omit [Fintype F] [DecidableEq F] in
/-- **The obligations are not vacuous — the sparse one is REFUTABLE.** The all-accepting oracle
falsifies `SpartanSparseEvalOracle` for any matrix whose MLE is not constantly `0` at the probed
point, so the `Prop` genuinely constrains an oracle rather than holding for free. -/
theorem sparseEvalOracle_refutable (A : R1CSMatrix F s t) {x : Fin s → F} {y : Fin t → F}
    (h : mle₂ A x y ≠ 0) :
    ¬ SpartanSparseEvalOracle A (fun _ _ _ => True) := by
  intro hO
  exact h (hO x y 0 trivial).symm

end Obligations

/-! ## §6. Teeth over ZMod 7, `s = t = 1`

The dangers this section exists to refute, each of which survives a green build: the R1CS could be
unsatisfiable for a trivial reason (so `spartan_outer_sound`'s hypothesis is never met by anything
interesting), the `s/|F|` event could be EMPTY (a true bound about nothing), the inner claim
predicate could hold vacuously, and `spartanTerminal_eq_honest` could be an equation between two
constants. -/

namespace SpartanExample

open Minidregg.Selvage

/-! The instance is the SQUARING gate `w · w = v` over two variables — the smallest R1CS that is
not satisfied by the zero witness, which a `C = 0` instance would have been. Variable cube:
`y = false ↦ w`, `y = true ↦ v`. Constraint cube: row `a = false` carries the gate, row
`a = true` is the zero row (the padding a non-dyadic R1CS always brings). -/

/-- `A`: the gate row reads variable `w`; the padding row is empty. -/
def sA : R1CSMatrix (ZMod 7) 1 1 :=
  fun a y => if a 0 then 0 else (if y 0 then 0 else 1)

/-- `B = A`: both factors of the gate are `w`, because the gate is a squaring. -/
def sB : R1CSMatrix (ZMod 7) 1 1 :=
  fun a y => if a 0 then 0 else (if y 0 then 0 else 1)

/-- `C`: the gate row reads variable `v`. -/
def sC : R1CSMatrix (ZMod 7) 1 1 :=
  fun a y => if a 0 then 0 else (if y 0 then 1 else 0)

/-- The satisfying witness `(w, v) = (3, 2)`: `3² = 9 = 2` in F₇. -/
def goodZ : (Fin 1 → Bool) → ZMod 7 := fun y => if y 0 then 2 else 3

/-- `(w, v) = (3, 1)` — the same `w`, a wrong square. Defect `3·3 − 1 = 1` on the gate row. -/
def badZ : (Fin 1 → Bool) → ZMod 7 := fun y => if y 0 then 1 else 3

/-- **TEETH — the good side is inhabited**, and NOT by the zero witness, so
`spartan_outer_sound`'s hypothesis is a real discrimination between two live witnesses. -/
theorem goodZ_sat : R1CSSat sA sB sC goodZ := by
  unfold R1CSSat matVec
  decide

/-- **TEETH — the bad side is genuinely unsatisfying.** -/
theorem badZ_unsat : ¬ R1CSSat sA sB sC badZ := by
  unfold R1CSSat matVec
  decide

/-- The defect word is nonzero, so `mle_zero_uniform_bound` applies to a real word. -/
theorem badZ_defect_ne_zero : r1csDefect sA sB sC badZ ≠ 0 := by
  intro h
  have hf := congrFun h (fun _ => false)
  revert hf
  decide

/-- **TEETH — the `s/|F|` event is NONEMPTY.** The defect word `(1, 0)` really does have a
vanishing zerocheck point — its extension is `1 − τ`, zero at `τ = 1` — so `spartan_outer_sound`'s
first term bounds a real event rather than a vacuum, and the zerocheck is not a formality. -/
theorem badZ_survives_at_one : mle (r1csDefect sA sB sC badZ) ![1] = 0 := by decide

/-- **TEETH — and it is separated elsewhere**, so the surviving point above is a genuine root of a
nonconstant extension rather than a degenerate word. -/
theorem badZ_caught_at_three : mle (r1csDefect sA sB sC badZ) ![3] ≠ 0 := by decide

/-- The true row opening of `A` at `r_x = 2`, computed: `Âz(2) = 4`. -/
theorem rowOpening_A_at_two : mle (matVec sA badZ) ![2] = 4 := by decide

/-- **TEETH — the inner claim predicate FIRES**, through the iff rather than by computation: the
true row opening is accepted as a linear constraint on the witness word. -/
theorem innerClaim_fires : Satisfies badZ (innerClaim sA ![2] 4) :=
  (innerClaim_satisfied_iff sA badZ ![2] 4).mpr rowOpening_A_at_two.symm

/-- **TEETH — and it REFUSES.** Changing only the claimed value breaks it, so the predicate is a
test and not a tautology. -/
theorem innerClaim_refuses : ¬ Satisfies badZ (innerClaim sA ![2] 5) := by decide

/-- **TEETH — the hand-off computes on real numbers.** `spartanTerminal_eq_honest` is not an
equation between two zeros: at `τ = 3`, `r_x = 2` the terminal value is `1 · (4·4 − 6) = 3`,
computed here from the three true row openings. -/
theorem terminal_fires :
    spartanTerminal (![3] : Fin 1 → ZMod 7) ![2]
        (mle (matVec sA badZ) ![2]) (mle (matVec sB badZ) ![2])
        (mle (matVec sC badZ) ![2]) = 3 := by decide

end SpartanExample

/-! ## §7. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.mle_matVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_matVec
/-- info: 'Minidregg.Assurance.r1csSat_iff_defect_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms r1csSat_iff_defect_zero
/-- info: 'Minidregg.Assurance.spartanOuterForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartanOuterForm
/-- info: 'Minidregg.Assurance.spartanOuterTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartanOuterTotal
/-- info: 'Minidregg.Assurance.spartan_outer_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartan_outer_sound
/-- info: 'Minidregg.Assurance.spartanTerminal_eq_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartanTerminal_eq_honest
/-- info: 'Minidregg.Assurance.innerClaim_satisfied_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms innerClaim_satisfied_iff
/-- info: 'Minidregg.Assurance.spartan_inner_batch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartan_inner_batch_sound
/-- info: 'Minidregg.Assurance.spartan_inner_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartan_inner_sound
/-- info: 'Minidregg.Assurance.spartan_inner_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartan_inner_terminal
/-- info: 'Minidregg.Assurance.spartanOpeningsBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms spartanOpeningsBound
/-- info: 'Minidregg.Assurance.sparseEvalOracle_refutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sparseEvalOracle_refutable
/-- info: 'Minidregg.Assurance.SpartanExample.badZ_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SpartanExample.badZ_unsat
/-- info: 'Minidregg.Assurance.SpartanExample.badZ_survives_at_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SpartanExample.badZ_survives_at_one
/-- info: 'Minidregg.Assurance.SpartanExample.terminal_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SpartanExample.terminal_fires

end Minidregg.Assurance
