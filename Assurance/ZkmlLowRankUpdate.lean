/-
# `Assurance/ZkmlLowRankUpdate.lean` — the LOW-RANK update, and why the CHAIN is cheap

**Substrate, said out loud: this is Lean-authored constraint semantics.** The relation, its
completeness, its two soundness accountings and the inference-side identity are theorems
about the objects `Selvage/`'s sumcheck and `Assurance/ZkmlMatmulSumcheck.lean`'s
contraction already consume. Rust is prover and harness only
(`prover/src/bin/low_rank_commit_cost.rs` is a COST COUNTER, not a checker).

## The measurement that forces this file

`Selvage/Rank1GradientCheck.lean` made the gradient PROOF for a linear layer ~7·10⁴×
cheaper (`O(2^{m/2})` against `O(2^m)`), and `sgd_step_sound` certifies a whole SGD step in
three openings at one common point with zero rounds. Its honest half is the brief here:

  **the check removes the `n²` PROOF, it does not remove the `n²` COMMITMENT.**

`W' = W − η·∇W` still commits `2^24` felts at `d = 4096`, and the prover is hash-bound by
5.0–7.2× (`notes/field-op-counts.md`), so a committed felt IS the expensive thing. The
structural answer is to stop committing `W'` at all: commit the base ONCE, and let each step
commit only a rank-`r` factor pair.

## What is proved here

**§1 — the relation.** For committed `W`, `A` (`d×r`), `B` (`r×d`) and a claimed `W'`:

  `Ŵ'(x,y) = Ŵ(x,y) + Σ_{p ∈ {0,1}^κ} Â(x,p)·B̂(p,y)`,  `r = 2^κ`.

* `mle₂_lowRankUpdate` — the identity, at EVERY `(x,y)`. It is `mle₂_contraction` plus
  additivity of the block extension; **the delta table `W' − W` is exactly the matmul's
  output table** (`lowRank_delta_is_the_matmul_output`), which is the whole reason nothing
  needs reproving.
* `lowRank_target_from_two_openings` — the verifier never touches the delta table: its
  target is `Ŵ'(x,y) − Ŵ(x,y)`, two openings it already has.

**⚑ §1's real content is a CORRECTION, and it is the reason this file is not one line.**
The brief asked whether the rank-`r` case is literally `rankK_sound`, whose bound famously
does not grow with `K`. It is — *for one of the two designs*, and they are not the same
protocol:

* **`r`-openings design.** `A` and `B` are handed over as `2r` separately-opened vectors.
  The verifier evaluates the sum itself in `r` multiplications, and
  `lowRank_summand_is_rankK_summand` shows the summand is `rankK`'s summand **by `rfl`**.
  `lowRank_sound` gives `(μ+ν)/|F|`, with **no `κ`** — `rankK_sound`'s statement, and it
  should not be reproved. It costs `2r` openings.
* **one-commitment design.** `A` and `B` are each ONE committed matrix — which is the entire
  point, `2rd` felts in two commitments rather than `2r` of them. Then the verifier has one
  opening of each and **cannot evaluate the inner sum**; it must sumcheck `κ = log₂ r`
  variables. `lowRank_sumcheck_soundness` is the composed bound,

    `(μ+ν)/|F| + κ·3/|F|`,

  and **it does grow with `r`.** Logarithmically, so it is cheap — but "the bound does not
  grow with `K`" is a fact about the design that does not save the commitment, and quoting
  it for the design that does would be quoting the flattering half of a pair.

**§2 — the chain, where the accumulator state IS the model.** `chainUpdate` applies deltas
one at a time; `chainUpdate_eq_base_plus_deltas` proves that equals adding all of them to
the base at once. **The base is never recommitted**, and `mle₂_chainUpdate` opens the whole
history at one point: `Ŵ_T(x,y) = Ŵ₀(x,y) + Σ_t Σ_p Â_t(x,p)·B̂_t(p,y)`.

**§3 — the inference-side identity, and the part that makes the CHAIN cheap rather than
just the step.** `matVec_matmulTable` is the load-bearing fact:

  `(A·B)·v = A·(B·v)`,

i.e. **the cheap evaluation order is available** — `2rd` multiplies instead of `d²r + d²`.
On top of it, `matVec_lowRankUpdate` : `(W + A·B)·v = W·v + A·(B·v)`, and the chain form
`matVec_chainUpdate` : serving `T` stacked adapters is **ONE base matvec plus `T` thin
pairs**, with the `d²` term appearing exactly once on the right-hand side however long the
list is. `mle_matVec_lowRankUpdate` is the same statement in the unit a verifier consumes.

**§4 — scope as theorems.** `lowRankUpdate_gauge`: for ANY invertible `r×r` change of basis
`S`, the pair `(A·S, S⁻¹·B)` is the SAME update — the check pins the PRODUCT and says
nothing about `A` and `B` individually (the scalar case is `lowRankUpdate_rescale`, the
exact analogue of `outerTable_rescale`). `lowRank_blind_to_the_projection`: for ANY `A'`,
`B'` the relation is accepted at every point, so **whether `A,B` is the correct low-rank
projection of the true gradient is a SEPARATE obligation.**

**§5 — teeth.** The vacuity to fear here is precise and is not the rank-1 file's: it is that
the check certifies *"the delta is low rank"* rather than *"the delta is THIS low-rank
delta"*. `lowRank_refuses_another_low_rank_update` refuses a genuinely different rank-2
update of a 4×4 matrix, and `lowRankUpdate_gauge_is_real` exhibits a nonidentity `S` that
the check genuinely cannot see, so the gauge scope item bounds a real freedom rather than an
empty one.

**Not made a theorem, deliberately.** "The base evaluation `W·v` does not depend on `A` or
`B`, so it is shared across every adapter" is `rfl` — a vacuous statement of exactly the
class this repo keeps finding, and a reader seeing it in the theorem list would credit the
file with a check it does not perform. The non-vacuous form of that claim is
`matVec_chainUpdate`, which says the `d²` term appears ONCE for a list of any length, and it
is proved.

**One thing this file is NOT.** `mle₂` is not a parallel multilinear extension: `mle₂_row`
proves it IS a composition of the landed one-block `mle`. And the rank-1 object is not a
sibling of this one — `matmulTable_rank_one` collapses `κ = 0` to the outer product
`A(a)·B(b)`, so the previous rung is the `r = 1` instance of this relation.
-/
import Assurance.ZkmlMatmulSumcheck
import Selvage.Rank1GradientCheck

namespace Minidregg.Assurance

open Minidregg.Selvage

/-! ## §1. The low-rank update relation

`W' = W + A·B` with `A : d×r`, `B : r×d` and `r = 2^κ`. The committed object per step is
`2rd` felts instead of `d²`; the base `W` is committed once and is the registry. -/

section Update

variable {F : Type} [Field F] {μ κ ν : ℕ}

/-- Block-extension additivity — the mirror of the landed `mle₂_sub`, and the only new
linearity fact this file needs. -/
theorem mle₂_add (f g : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (fun a b => f a b + g a b) x y = mle₂ f x y + mle₂ g x y := by
  simp only [mle₂, add_mul, Finset.sum_add_distrib]

/-- **The low-rank update.** `W' = W + A·B`. Nothing here requires `r < d`; that is a
statement about the COMMITMENT shape, fixed by the type, and it is what buys the `2rd`
against `d²`. -/
def lowRankUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) :
    (Fin μ → Bool) → (Fin ν → Bool) → F :=
  fun a b => W a b + matmulTable A B a b

/-- **The delta table IS the matmul's output table.** This one line is why the whole landed
contraction argument — identity, honest prover, composed soundness — transfers to the update
relation with nothing reproved. -/
theorem lowRank_delta_is_the_matmul_output
    (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) :
    (fun a b => lowRankUpdate W A B a b - W a b) = matmulTable A B := by
  funext a b
  unfold lowRankUpdate
  ring

/-- **THE RELATION.** `Ŵ'(x,y) = Ŵ(x,y) + Σ_p Â(x,p)·B̂(p,y)`, an identity of the
extensions at EVERY `(x,y)` — no probability, no `eq` factor, and no appeal to multilinear
uniqueness. -/
theorem mle₂_lowRankUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (lowRankUpdate W A B) x y
      = mle₂ W x y + ∑ p, rowPartial A x p * colPartial B y p := by
  unfold lowRankUpdate
  rw [mle₂_add, mle₂_contraction]

/-- **The check.** The verifier holds openings of `W`, `W'`, `A`, `B` at a common random
`(x,y)` and tests one equation. -/
def LowRankAccepts (W W' : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) : Prop :=
  mle₂ W' x y = mle₂ W x y + ∑ p, rowPartial A x p * colPartial B y p

/-- The check is an EQUATION in the field, so it is decidable over a decidable field — which
is what lets §6's teeth range over a whole challenge space with `decide` while still naming
`LowRankAccepts` rather than a hand-unfolded copy of it. -/
instance instDecidableLowRankAccepts {F : Type} [Field F] [DecidableEq F] {μ κ ν : ℕ}
    (W W' : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    Decidable (LowRankAccepts W W' A B x y) := by
  unfold LowRankAccepts
  infer_instance

/-- **Completeness** — the honest update is accepted at EVERY challenge. -/
theorem lowRank_complete (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    LowRankAccepts W (lowRankUpdate W A B) A B x y :=
  mle₂_lowRankUpdate W A B x y

/-- **The verifier never touches the delta table.** Its sumcheck target is the difference of
two openings it already holds — which is what makes `W'` and `W` separate commitments rather
than a materialized `W' − W`. -/
theorem lowRank_target_from_two_openings (W W' : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (fun a b => W' a b - W a b) x y = mle₂ W' x y - mle₂ W x y :=
  mle₂_sub W' W x y

/-- **⚑ THE CORRESPONDENCE WITH `rankK`, and it is `rfl`.** The summand of the low-rank
relation is exactly `Selvage/Rank1GradientCheck.lean`'s rank-`K` summand: `rowPartial A x p`
IS the one-block MLE of `A`'s `p`-th COLUMN, and `colPartial B y p` IS the one-block MLE of
`B`'s `p`-th ROW. So the `r`-openings design's relation and its `(μ+ν)/|F|` bound are
`rankK_sound`'s statement, reindexed from `Fin K` to the cube `{0,1}^κ`, and are not
reproved below. -/
theorem lowRank_summand_is_rankK_summand
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F)
    (p : Fin κ → Bool) :
    rowPartial A x p * colPartial B y p
      = mle (fun a => A a p) x * mle (fun b => B p b) y :=
  rfl

/-- **⚑ The rank-1 rung is the `r = 1` instance, not a sibling.** At `κ = 0` the inner cube
is a single point and the delta collapses to the outer product `A(a)·B(b)` — the object
`Selvage/Rank1GradientCheck.lean`'s `outerTable` names in the flat index convention. -/
theorem matmulTable_rank_one (A : (Fin μ → Bool) → (Fin 0 → Bool) → F)
    (B : (Fin 0 → Bool) → (Fin ν → Bool) → F) (a : Fin μ → Bool) (b : Fin ν → Bool) :
    matmulTable A B a b = A a Fin.elim0 * B Fin.elim0 b := by
  unfold matmulTable
  rw [Finset.sum_eq_single Fin.elim0]
  · intro p _ hp
    exact absurd (funext fun i => i.elim0) hp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Update

/-! ## §2. Soundness — the two designs, and the term that separates them -/

section Soundness

variable {F : Type} [Field F] [Fintype F] {μ κ ν : ℕ}

/-- **SOUNDNESS of the `r`-openings design.** A `W'` that is not `W + A·B` — a wrong delta,
a tampered base, a swapped factor — survives a uniformly random `(x,y)` with probability at
most `(μ+ν)/|F|`. **No `κ` appears**: the inner index costs the verifier `r`
multiplications and costs the soundness nothing, because no round is added.

This is `rankK_sound`'s content in the block representation (see
`lowRank_summand_is_rankK_summand`), obtained from the landed two-block Schwartz–Zippel
applied to the defect table. It buys its `κ`-freedom with **`2r` openings**, which is the
cost the next theorem removes. -/
theorem lowRank_sound {W W' : (Fin μ → Bool) → (Fin ν → Bool) → F}
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F}
    {B : (Fin κ → Bool) → (Fin ν → Bool) → F} (hW : W' ≠ lowRankUpdate W A B) :
    uniformProb ((Fin μ → F) × (Fin ν → F))
        (fun w => LowRankAccepts W W' A B w.1 w.2)
      ≤ ((μ : ℝ) + ν) / Fintype.card F := by
  have hD : (fun a b => W' a b - lowRankUpdate W A B a b) ≠ 0 := by
    intro h
    refine hW (funext fun a => funext fun b => ?_)
    have hab : W' a b - lowRankUpdate W A B a b = 0 := by
      simpa using congrFun (congrFun h a) b
    exact sub_eq_zero.mp hab
  refine le_trans (le_of_eq (uniformProb_congr fun w => ?_)) (mle₂_zero_uniform_bound hD)
  unfold LowRankAccepts
  rw [mle₂_sub, sub_eq_zero, mle₂_lowRankUpdate]

end Soundness

section SumcheckSoundness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {μ κ ν : ℕ}

/-- One draw of the ONE-COMMITMENT protocol: the outer point `(x,y)`, then the `κ` sumcheck
challenges on the inner index. The verifier's target is the DIFFERENCE of its two weight
openings (`lowRank_target_from_two_openings`), and the sumcheck runs against the landed
contraction family — so the whole engine is reused, unmodified. -/
def LowRankUpdateAccepts (W W' : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (w : ((Fin μ → F) × (Fin ν → F)) × (Fin κ → F)) : Prop :=
  MatmulAccepts A B (fun a b => W' a b - W a b) prover w

/-- **⚑ SOUNDNESS of the ONE-COMMITMENT design — and the term `rankK_sound` does not have.**
When `A` and `B` are each ONE committed matrix (`2rd` felts in two commitments, which is the
entire point of the low-rank route), the verifier holds one opening of each and cannot
evaluate the inner sum. It must sumcheck `κ = log₂ r` variables, and the bound becomes

  `(μ+ν)/|F|` — the outer point failed to separate the claimed `W'` from `W + A·B`,
  `+ κ·3/|F|` — the sumcheck on the rank index was laundered.

**So the bound DOES grow with `r`** — logarithmically, hence cheaply, but it grows, and
"`rankK_sound`'s bound does not grow with `K`" is a fact about the `2r`-openings design that
does not save the commitment. Reporting only the first term would be quoting the flattering
half of a pair.

Proved by exhibiting the update relation as the landed matmul relation on the DELTA table
(`lowRank_delta_is_the_matmul_output`); nothing about sumchecks is re-derived here. -/
theorem lowRank_sumcheck_soundness {W W' : (Fin μ → Bool) → (Fin ν → Bool) → F}
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F}
    {B : (Fin κ → Bool) → (Fin ν → Bool) → F} (hW : W' ≠ lowRankUpdate W A B)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < κ →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (((Fin μ → F) × (Fin ν → F)) × (Fin κ → F))
        (LowRankUpdateAccepts W W' A B prover)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) := by
  refine matmul_sumcheck_soundness (C := fun a b => W' a b - W a b) ?_ hpm hdeg
  intro hEq
  refine hW (funext fun a => funext fun b => ?_)
  have hab : W' a b - W a b = matmulTable A B a b := congrFun (congrFun hEq a) b
  unfold lowRankUpdate
  exact sub_eq_iff_eq_add'.mp hab

end SumcheckSoundness

/-! ## §3. The chain — the accumulator state IS the model

A step commits `2rd` felts. A HISTORY of `T` steps commits `d²` ONCE plus `T·2rd`, and the
theorem below is what licenses that: applying the deltas one at a time and adding them all
to the base at once are the same matrix, so the base never has to be recommitted. -/

section Chain

variable {F : Type} [Field F] {μ κ ν : ℕ}

/-- A step's committed object: the factor pair. -/
abbrev Delta (F : Type) [Field F] (μ κ ν : ℕ) : Type :=
  ((Fin μ → Bool) → (Fin κ → Bool) → F) × ((Fin κ → Bool) → (Fin ν → Bool) → F)

/-- **The accumulator.** Deltas applied in sequence, each one a `lowRankUpdate` of the
previous state. This is the shape a training run actually has. -/
def chainUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F) :
    List (Delta F μ κ ν) → (Fin μ → Bool) → (Fin ν → Bool) → F
  | [] => W
  | AB :: rest => chainUpdate (lowRankUpdate W AB.1 AB.2) rest

/-- **⚑ THE ACCUMULATOR THEOREM — the base is committed ONCE.** Applying `T` deltas one at a
time equals adding all of them to the base, so no intermediate `W_t` is ever a committed
object: the history is `W₀` plus a list of factor pairs, and the state is recovered from
them. -/
theorem chainUpdate_eq_base_plus_deltas (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (L : List (Delta F μ κ ν)) :
    chainUpdate W L
      = fun a b => W a b + (L.map (fun AB => matmulTable AB.1 AB.2 a b)).sum := by
  induction L generalizing W with
  | nil => funext a b; simp [chainUpdate]
  | cons AB rest ih =>
      funext a b
      rw [chainUpdate, ih]
      simp only [List.map_cons, List.sum_cons, lowRankUpdate]
      ring

/-- **The whole history at one point.** `Ŵ_T(x,y) = Ŵ₀(x,y) + Σ_t Σ_p Â_t(x,p)·B̂_t(p,y)` —
the verifier opens the base once and each delta once, and never opens an intermediate
state. -/
theorem mle₂_chainUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (L : List (Delta F μ κ ν)) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (chainUpdate W L) x y
      = mle₂ W x y
        + (L.map (fun AB => ∑ p, rowPartial AB.1 x p * colPartial AB.2 y p)).sum := by
  induction L generalizing W with
  | nil => simp [chainUpdate]
  | cons AB rest ih =>
      rw [chainUpdate, ih, mle₂_lowRankUpdate]
      simp only [List.map_cons, List.sum_cons]
      ring

end Chain

/-! ## §4. The inference-side identity — what makes the CHAIN cheap, not just the step

Serving a low-rank-updated model is the BASE evaluation plus two thin matmuls. The
load-bearing fact is associativity: `(A·B)·v = A·(B·v)`, i.e. **the cheap evaluation order
is available** (`2rd` multiplies rather than `d²r + d²`). Cost is not in this model; the
availability of the cheap order is, and it is the whole content of the claim. -/

section Inference

variable {F : Type} [Field F] {μ κ ν ξ : ℕ}

/-- Matrix times vector, on the cubes: `(M·v)(a) = Σ_b M(a,b)·v(b)`. -/
def matVec (M : (Fin μ → Bool) → (Fin ν → Bool) → F) (v : (Fin ν → Bool) → F) :
    (Fin μ → Bool) → F :=
  fun a => ∑ b, M a b * v b

/-- `matVec` is additive in the matrix — how the base and the delta separate. -/
theorem matVec_add (M N : (Fin μ → Bool) → (Fin ν → Bool) → F) (v : (Fin ν → Bool) → F) :
    matVec (fun a b => M a b + N a b) v = fun a => matVec M v a + matVec N v a := by
  funext a
  simp only [matVec, add_mul, Finset.sum_add_distrib]

/-- Matrix multiplication is associative on the cubes — needed for the gauge scope item. -/
theorem matmulTable_assoc (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin ν → Bool) → (Fin ξ → Bool) → F) :
    matmulTable (matmulTable A B) C = matmulTable A (matmulTable B C) := by
  funext a d
  simp only [matmulTable, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- **⚑ THE LOAD-BEARING FACT: `(A·B)·v = A·(B·v)`.** The right-hand side never
materializes the `d×d` product — it is a `r×d` matvec followed by a `d×r` matvec, `2rd`
multiplies against the `d²r` of forming `A·B` first. The identity is what makes that order
LEGAL; the count is in §5 of the note, not in this model. -/
theorem matVec_matmulTable (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (v : (Fin ν → Bool) → F) :
    matVec (matmulTable A B) v = matVec A (matVec B v) := by
  funext a
  simp only [matVec, matmulTable, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun b _ => by ring

/-- **⚑ THE INFERENCE IDENTITY.** `(W + A·B)·v = W·v + A·(B·v)`. Serving a low-rank-updated
model is the BASE evaluation — shared across every adapter and every step — plus two thin
matmuls. -/
theorem matVec_lowRankUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (v : (Fin ν → Bool) → F) :
    matVec (lowRankUpdate W A B) v = fun a => matVec W v a + matVec A (matVec B v) a := by
  unfold lowRankUpdate
  rw [matVec_add, matVec_matmulTable]

/-- **⚑ THE CHAIN FORM — the `d²` term appears ONCE for a list of any length.** This is the
non-vacuous version of "the base is shared": serving a model carrying `T` stacked adapters
is one base matvec plus `T` thin pairs, and the base term on the right-hand side does not
depend on the list at all. -/
theorem matVec_chainUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (L : List (Delta F μ κ ν)) (v : (Fin ν → Bool) → F) :
    matVec (chainUpdate W L) v
      = fun a => matVec W v a + (L.map (fun AB => matVec AB.1 (matVec AB.2 v) a)).sum := by
  induction L generalizing W with
  | nil => funext a; simp [chainUpdate]
  | cons AB rest ih =>
      funext a
      rw [chainUpdate, ih]
      simp only [List.map_cons, List.sum_cons]
      have h := congrFun (matVec_lowRankUpdate W AB.1 AB.2 v) a
      rw [h]
      ring

/-- The inference identity in the unit a VERIFIER consumes: the output vector's multilinear
extension splits the same way, so the base claim and the adapter claim are separate openings
at one point. -/
theorem mle_matVec_lowRankUpdate (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (v : (Fin ν → Bool) → F) (x : Fin μ → F) :
    mle (matVec (lowRankUpdate W A B) v) x
      = mle (matVec W v) x + mle (matVec A (matVec B v)) x := by
  rw [matVec_lowRankUpdate]
  exact mle_add _ _ x

end Inference

/-! ## §5. Scope, as theorems rather than prose -/

section Scope

variable {F : Type} [Field F] {μ κ ν : ℕ}

/-- The identity matrix on the rank index. -/
def oneTable (κ : ℕ) (F : Type) [Field F] : (Fin κ → Bool) → (Fin κ → Bool) → F :=
  fun p q => if p = q then 1 else 0

theorem matmulTable_oneTable_left (B : (Fin κ → Bool) → (Fin ν → Bool) → F) :
    matmulTable (oneTable κ F) B = B := by
  funext p b
  unfold matmulTable oneTable
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Ne.symm hq]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **⚑ SCOPE — the check pins the PRODUCT `A·B`, never `A` and `B`.** For ANY invertible
`r×r` change of basis `S` (with inverse `T`), the pair `(A·S, T·B)` is the SAME update and
is accepted identically. So nothing downstream may read `A` as "the adapter": the object the
proof binds is the `d×d` delta, and the factorization is gauge. -/
theorem lowRankUpdate_gauge (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (S T : (Fin κ → Bool) → (Fin κ → Bool) → F) (h : matmulTable S T = oneTable κ F) :
    lowRankUpdate W (matmulTable A S) (matmulTable T B) = lowRankUpdate W A B := by
  unfold lowRankUpdate
  rw [matmulTable_assoc, ← matmulTable_assoc S T B, h, matmulTable_oneTable_left]

/-- The scalar case, the exact analogue of `Rank1GradientCheck`'s `outerTable_rescale`:
`(c·A, c⁻¹·B)` is the same update. -/
theorem matmulTable_rescale (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (c : F) (hc : c ≠ 0) :
    matmulTable (fun a p => c * A a p) (fun p b => c⁻¹ * B p b) = matmulTable A B := by
  funext a b
  unfold matmulTable
  refine Finset.sum_congr rfl fun p _ => ?_
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  calc c * A a p * (c⁻¹ * B p b) = c * c⁻¹ * (A a p * B p b) := by ring
    _ = A a p * B p b := by rw [hcc, one_mul]

theorem lowRankUpdate_rescale (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (c : F) (hc : c ≠ 0) :
    lowRankUpdate W (fun a p => c * A a p) (fun p b => c⁻¹ * B p b)
      = lowRankUpdate W A B := by
  unfold lowRankUpdate
  rw [matmulTable_rescale A B c hc]

/-- **⚑ SCOPE — blind to whether `A,B` is the CORRECT low-rank projection.** For ANY factor
pair the relation holds at every challenge. That the pair is the true (or even a good)
low-rank approximation of the gradient is a SEPARATE obligation, and nothing in this file
touches it. -/
theorem lowRank_blind_to_the_projection (W : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (A' : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B' : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    LowRankAccepts W (lowRankUpdate W A' B') A' B' x y :=
  lowRank_complete W A' B' x y

end Scope

/-! ## §6. Teeth

The vacuity to fear here is NOT the rank-1 file's. It is that the relation might certify
*"the delta is low rank"* rather than *"the delta is THIS low-rank delta"* — a check with
the weaker meaning would accept every `A'·B`, and would be worthless for a training log.
Point teeth run at `μ = ν = 2, κ = 1` over F₅: a 4×4 weight matrix with a genuinely
low-rank (rank ≤ 2 of 4) update. Counting teeth run at `μ = ν = 1, κ = 0` — a 2×2 matrix
with a rank-1 update — where the whole 25-point challenge space is kernel-checked. -/

namespace LowRankExample

/-- A 4-index as a `Fin 4`, LSB-first (`a 0` is the low bit). -/
def ix2 (a : Fin 2 → Bool) : Fin 4 :=
  if a 0 then (if a 1 then 3 else 1) else (if a 1 then 2 else 0)

/-- A 2-index as a `Fin 2`. -/
def ix1 (p : Fin 1 → Bool) : Fin 2 := if p 0 then 1 else 0

/-- The base weight matrix `W₀`, 4×4 over F₅. -/
def eW : (Fin 2 → Bool) → (Fin 2 → Bool) → ZMod 5 :=
  fun a b => (![![1, 2, 3, 4], ![0, 1, 2, 3], ![4, 4, 0, 1], ![2, 0, 3, 1]] :
    Fin 4 → Fin 4 → ZMod 5) (ix2 a) (ix2 b)

/-- The left factor `A`, 4×2. -/
def eA : (Fin 2 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun a p => (![![1, 2], ![3, 0], ![4, 1], ![0, 2]] : Fin 4 → Fin 2 → ZMod 5) (ix2 a) (ix1 p)

/-- A DIFFERENT left factor `A'` — a genuinely different rank-≤2 update, the sharp tooth. -/
def eA' : (Fin 2 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun a p => (![![1, 2], ![3, 0], ![4, 1], ![0, 3]] : Fin 4 → Fin 2 → ZMod 5) (ix2 a) (ix1 p)

/-- The right factor `B`, 2×4. -/
def eB : (Fin 1 → Bool) → (Fin 2 → Bool) → ZMod 5 :=
  fun p b => (![![2, 1, 0, 3], ![1, 4, 2, 2]] : Fin 2 → Fin 4 → ZMod 5) (ix1 p) (ix2 b)

/-- The honest updated model `W' = W + A·B`. -/
def eW' : (Fin 2 → Bool) → (Fin 2 → Bool) → ZMod 5 := lowRankUpdate eW eA eB

/-- **TOOTH — the relation FIRES on data**, at the challenge `(x,y) = ((2,3),(1,4))`. -/
theorem lowRank_fires :
    LowRankAccepts eW eW' eA eB (![2, 3] : Fin 2 → ZMod 5) (![1, 4] : Fin 2 → ZMod 5) := by
  decide

/-- **TOOTH — the relation is not an artefact of the cube corners.** The challenge above is
off-cube in both blocks, so the identity is tested where it could fail. -/
theorem lowRank_offcube_challenge :
    mle₂ eW' (![2, 3] : Fin 2 → ZMod 5) (![1, 4] : Fin 2 → ZMod 5) ≠ 0 := by decide

/-- **⚑ THE SHARP TOOTH — a genuinely different LOW-RANK update is REFUSED.** `A'·B` is a
perfectly good rank-≤2 delta of the same shape; the check refuses it. A relation meaning
"the delta is low rank" would accept here, and this file would be worthless for a training
log. -/
theorem lowRank_refuses_another_low_rank_update :
    ¬ LowRankAccepts eW (lowRankUpdate eW eA' eB) eA eB
        (![2, 3] : Fin 2 → ZMod 5) (![1, 4] : Fin 2 → ZMod 5) := by decide

/-- The other update really is a different matrix, so the tooth above is not refusing a
spelling. -/
theorem the_other_update_is_different : lowRankUpdate eW eA' eB ≠ eW' := by decide

/-- **TOOTH — the BASE is bound.** Shifting every entry of `W'` by one is refused: the
relation pins `W` as well as the delta, which is what makes a chain auditable. -/
theorem lowRank_refuses_a_tampered_base :
    ¬ LowRankAccepts eW (fun a b => eW' a b + 1) eA eB
        (![2, 3] : Fin 2 → ZMod 5) (![1, 4] : Fin 2 → ZMod 5) := by decide

/-- **TOOTH — the index ORDER is pinned.** The TRANSPOSED update is refused; a transposed
row/column convention in `rowPartial`/`colPartial` would survive every symmetric test and
this one catches it. -/
theorem lowRank_refuses_the_transposed_update :
    ¬ LowRankAccepts eW (fun a b => eW' b a) eA eB
        (![2, 3] : Fin 2 → ZMod 5) (![1, 4] : Fin 2 → ZMod 5) := by decide

/-- The transposed update is genuinely a different matrix (the base is not symmetric). -/
theorem the_transpose_is_different : (fun a b => eW' b a) ≠ eW' := by decide

/-! ### The gauge freedom is REAL, not a hypothetical -/

/-- A nonidentity 2×2 change of basis on the rank index. -/
def eS : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun p q => (![![1, 1], ![0, 1]] : Fin 2 → Fin 2 → ZMod 5) (ix1 p) (ix1 q)

/-- Its inverse. -/
def eT : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun p q => (![![1, 4], ![0, 1]] : Fin 2 → Fin 2 → ZMod 5) (ix1 p) (ix1 q)

theorem eS_eT_inverse : matmulTable eS eT = oneTable 1 (ZMod 5) := by decide

/-- **⚑ TOOTH — the gauge scope item bounds a REAL freedom.** `A·S` is a different committed
matrix from `A`… -/
theorem gauge_changes_the_factor : matmulTable eA eS ≠ eA := by decide

/-- …and yet the update is IDENTICAL, so no verifier running this relation can tell the two
factorizations apart. `lowRankUpdate_gauge` is therefore not a statement about an empty
set. -/
theorem gauge_leaves_the_update_fixed :
    lowRankUpdate eW (matmulTable eA eS) (matmulTable eT eB) = eW' :=
  lowRankUpdate_gauge eW eA eB eS eT eS_eT_inverse

/-! ### The inference identity, computed -/

/-- An input vector `v`. -/
def ev : (Fin 2 → Bool) → ZMod 5 := fun b => (![2, 0, 1, 3] : Fin 4 → ZMod 5) (ix2 b)

/-- **TOOTH — the inference identity FIRES on data**: `(W + A·B)v = Wv + A(Bv)` entrywise. -/
theorem inference_identity_fires :
    matVec eW' ev = fun a => matVec eW ev a + matVec eA (matVec eB ev) a := by decide

/-- **TOOTH — the identity is not trivially true because the delta does nothing.** The
adapter genuinely moves the output: `(W + A·B)v ≠ Wv`. -/
theorem the_adapter_moves_the_output : matVec eW' ev ≠ matVec eW ev := by decide

/-- **TOOTH — the cheap order is the one the identity licenses, and forming `A·B` first
agrees with it.** Both sides of `(A·B)v = A(Bv)` are computed and equal — the association
that costs `d²r` and the one that costs `2rd` give the same vector. -/
theorem the_two_evaluation_orders_agree :
    matVec (matmulTable eA eB) ev = matVec eA (matVec eB ev) := by decide

/-! ### The chain, computed — the accumulator state IS the model -/

/-- A second delta, so the chain has length 2. -/
def eA2 : (Fin 2 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun a p => (![![0, 1], ![2, 2], ![1, 0], ![3, 4]] : Fin 4 → Fin 2 → ZMod 5) (ix2 a) (ix1 p)

def eB2 : (Fin 1 → Bool) → (Fin 2 → Bool) → ZMod 5 :=
  fun p b => (![![1, 0, 4, 1], ![3, 3, 2, 0]] : Fin 2 → Fin 4 → ZMod 5) (ix1 p) (ix2 b)

/-- **TOOTH — applying two deltas in sequence equals adding both to the base.** The general
statement is `chainUpdate_eq_base_plus_deltas`; this is it computed, and it is the fact that
lets the prover never recommit an intermediate `W_t`. -/
theorem chain_of_two_computed :
    chainUpdate eW [(eA, eB), (eA2, eB2)]
      = fun a b => eW a b + (matmulTable eA eB a b + matmulTable eA2 eB2 a b) := by decide

/-- **TOOTH — the ORDER of the chain does not change the state but the STATE is still
pinned**: two different chains that reach different matrices are separated. Swapping the
second delta's factors gives a different model. -/
theorem chains_to_different_states_differ :
    chainUpdate eW [(eA, eB), (eA2, eB2)] ≠ chainUpdate eW [(eA, eB), (eA, eB2)] := by decide

end LowRankExample

/-! ### Counting teeth — the whole challenge space, at `μ = ν = 1`, `κ = 0`

A 2×2 weight matrix with a RANK-1 update (`r = 1 < d = 2`), where `Fin 5 × Fin 5` is 25
challenges and `decide` covers all of them. These are the teeth that show the soundness
bound constrains a NONEMPTY event and is not loose slack. -/

namespace LowRankCount

/-- The base, `[[1,2],[3,4]]` over F₅. -/
def cW : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 5 :=
  fun a b => if a 0 then (if b 0 then 4 else 3) else (if b 0 then 2 else 1)

/-- A rank-1 left factor (`κ = 0`: the rank index is a single point). -/
def cA : (Fin 1 → Bool) → (Fin 0 → Bool) → ZMod 5 := fun a _ => if a 0 then 2 else 1

/-- A rank-1 right factor. -/
def cB : (Fin 0 → Bool) → (Fin 1 → Bool) → ZMod 5 := fun _ b => if b 0 then 4 else 3

/-- A DIFFERENT rank-1 left factor. -/
def cA' : (Fin 1 → Bool) → (Fin 0 → Bool) → ZMod 5 := fun a _ => if a 0 then 3 else 1

/-- **TOOTH — completeness on the WHOLE challenge space**: all 25 points accept. -/
theorem count_complete_fires :
    ∀ x : Fin 1 → ZMod 5, ∀ y : Fin 1 → ZMod 5,
      LowRankAccepts cW (lowRankUpdate cW cA cB) cA cB x y := by decide

/-- **TOOTH — the false-accept event is NONEMPTY.** A different rank-1 update IS accepted at
`(0, 3)`, so `lowRank_sound`'s bound constrains a real event rather than a vacuum. -/
theorem count_false_accept_witness :
    LowRankAccepts cW (lowRankUpdate cW cA' cB) cA cB
      (![0] : Fin 1 → ZMod 5) (![3] : Fin 1 → ZMod 5) := by decide

/-- **TOOTH — and it is refused elsewhere**, so the check is not "always accept". -/
theorem count_false_accept_refused :
    ¬ LowRankAccepts cW (lowRankUpdate cW cA' cB) cA cB
        (![2] : Fin 1 → ZMod 5) (![3] : Fin 1 → ZMod 5) := by decide

/-- **⚑ TOOTH — the bound is nearly ATTAINED, not loose slack.** Exactly 9 of the 25
challenges accept the wrong rank-1 update, against `lowRank_sound`'s `(μ+ν)/|F| = 2/5 =
10/25`. -/
theorem count_false_accepts :
    (Finset.univ.filter fun w : (Fin 1 → ZMod 5) × (Fin 1 → ZMod 5) =>
        LowRankAccepts cW (lowRankUpdate cW cA' cB) cA cB w.1 w.2).card = 9 := by decide

/-- **TOOTH — refusal is the common case**: 16 of 25. -/
theorem count_refusals :
    (Finset.univ.filter fun w : (Fin 1 → ZMod 5) × (Fin 1 → ZMod 5) =>
        ¬ LowRankAccepts cW (lowRankUpdate cW cA' cB) cA cB w.1 w.2).card = 16 := by decide

/-- **TOOTH — a tampered base is caught at EVERY challenge.** Adding `1` to every entry of
`W'` makes the defect the constant table `1`, whose block extension never vanishes: 0 of 25
accept. -/
theorem count_tampered_base_never_accepted :
    ∀ x : Fin 1 → ZMod 5, ∀ y : Fin 1 → ZMod 5,
      ¬ LowRankAccepts cW (fun a b => lowRankUpdate cW cA cB a b + 1) cA cB x y := by decide

/-- The soundness theorem FIRES on the wrong update: at most `2/5`, and the computed count
above is `9/25 < 10/25`. -/
theorem count_sound_fires :
    uniformProb ((Fin 1 → ZMod 5) × (Fin 1 → ZMod 5))
        (fun w => LowRankAccepts cW (lowRankUpdate cW cA' cB) cA cB w.1 w.2)
      ≤ 2 / 5 := by
  have hne : lowRankUpdate cW cA' cB ≠ lowRankUpdate cW cA cB := by decide
  have h := lowRank_sound (F := ZMod 5) (μ := 1) (κ := 0) (ν := 1) hne
  rw [ZMod.card] at h
  norm_num at h
  exact h

end LowRankCount

/-! ## §7. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.mle₂_lowRankUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_lowRankUpdate
/-- info: 'Minidregg.Assurance.lowRank_delta_is_the_matmul_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRank_delta_is_the_matmul_output
/-- info: 'Minidregg.Assurance.lowRank_summand_is_rankK_summand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRank_summand_is_rankK_summand
/-- info: 'Minidregg.Assurance.matmulTable_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmulTable_rank_one
/-- info: 'Minidregg.Assurance.lowRank_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRank_sound
/-- info: 'Minidregg.Assurance.lowRank_sumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRank_sumcheck_soundness
/-- info: 'Minidregg.Assurance.chainUpdate_eq_base_plus_deltas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms chainUpdate_eq_base_plus_deltas
/-- info: 'Minidregg.Assurance.mle₂_chainUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_chainUpdate
/-- info: 'Minidregg.Assurance.matVec_matmulTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matVec_matmulTable
/-- info: 'Minidregg.Assurance.matVec_lowRankUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matVec_lowRankUpdate
/-- info: 'Minidregg.Assurance.matVec_chainUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matVec_chainUpdate
/-- info: 'Minidregg.Assurance.mle_matVec_lowRankUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_matVec_lowRankUpdate
/-- info: 'Minidregg.Assurance.lowRankUpdate_gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRankUpdate_gauge
/-- info: 'Minidregg.Assurance.lowRankUpdate_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowRankUpdate_rescale
/-- info: 'Minidregg.Assurance.LowRankExample.lowRank_refuses_another_low_rank_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankExample.lowRank_refuses_another_low_rank_update
/-- info: 'Minidregg.Assurance.LowRankExample.lowRank_refuses_the_transposed_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankExample.lowRank_refuses_the_transposed_update
/-- info: 'Minidregg.Assurance.LowRankExample.gauge_leaves_the_update_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankExample.gauge_leaves_the_update_fixed
/-- info: 'Minidregg.Assurance.LowRankExample.inference_identity_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankExample.inference_identity_fires
/-- info: 'Minidregg.Assurance.LowRankExample.chain_of_two_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankExample.chain_of_two_computed
/-- info: 'Minidregg.Assurance.LowRankCount.count_false_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankCount.count_false_accepts
/-- info: 'Minidregg.Assurance.LowRankCount.count_sound_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LowRankCount.count_sound_fires

end Minidregg.Assurance
