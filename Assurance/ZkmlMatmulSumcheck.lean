/-
# `Assurance/ZkmlMatmulSumcheck.lean` — the CONTRACTION face, and what the cubic rung serves

**Substrate, said out loud: this is Lean-authored.** The claim, the honest prover, the
error bound and the composition are theorems about the objects `Selvage/`'s adaptive
sumcheck consumes. The Rust (`prover/src/sumcheck.rs`) re-computes these shapes and is
bound to them by a conformance vector — never by a refinement claim.

## ⚠ The correction this file exists to make

`Assurance/AirSumcheckCubic.lean` landed a theorem named `cubicForm_matmul`, for
`eq(z,x)·(Â(x)·B̂(x) − Ĉ(x))`, and the surrounding prose called it "the zkML matmul claim".
**It is not a matmul.** `Â·B̂` is a *pointwise* (Hadamard) product of two tables on the same
cube; a matmul sums over an inner index that appears in neither output coordinate.
`matmul_is_not_hadamard` below computes both on one 2×2 example over F₇ and they differ, so
this is a fact rather than a quibble. That theorem is now named `cubicForm_hadamard`, which
is what it is — the elementwise-product gate's zerocheck face, a real consumer, just not
this one.

## What the contraction face actually is (Thaler)

Bind the OUTER indices to random field points FIRST, then sumcheck the inner index only:

  `Ĉ(x, y) = Σ_{p ∈ {0,1}^κ} Â(x, p) · B̂(p, y)`

`mle₂_contraction` proves this as an **identity at every `(x,y)`** — no probability, no
appeal to multilinear uniqueness, just a triple sum reordered. Three consequences the prose
version of this plan got wrong:

* **No `eq` factor.** The head of the `cubicForm` instance is the CONSTANT `1`
  (`cubicForm_contraction`), because there is nothing left to zero-test: the outer indices
  are already bound. The `eq`-headed instance is the zerocheck face, a different protocol.
* **The summand is degree 2, and the degree-3 rung covers it strictly** — `Â·B̂` is a single
  product pair, so the instance is `E ≡ 1, C ≡ 0, D ≡ 1`. The rung is not tight here, and
  it is still the same engine (`cubicForm_subsumes_prodDiff` already made the degree-2 face
  one object with it), so this file adds no second implementation.
* **The error has TWO terms and they are not the same term.** The sumcheck contributes
  `κ·3/|F|`; binding the outer indices contributes `(μ+ν)/|F|` — a multilinear
  Schwartz–Zippel event that exists *because* the verifier tests the claimed output table
  at one random point. `matmul_sumcheck_soundness` adds them under a union bound. A writeup
  quoting only the sumcheck term would be quoting the flattering half of a pair.

## What is proved (no `sorry`)

* `mle₂` — the two-block multilinear extension, with `mle₂_row`/`mle₂_col` (it IS a
  composition of one-block MLEs, so no multilinearity is re-proved), `mle₂_agrees`,
  `mle₂_sub`.
* `mle₂_contraction` — **the honest-prover identity**, at every `(x,y)`.
* `cubicForm_contraction` / `matmul_claim_total` / `matmulHonest_complete` — the instance,
  its cube total as `Ĉ(x,y)` of the TRUE output table, and completeness on every challenge.
* `mle₂_zero_uniform_bound` — two-block multilinear Schwartz–Zippel, `≤ (μ+ν)/|F|`, from
  `Selvage/MultilinearZeroTest.lean`'s one-block bound composed over the two blocks. No new
  probability toolkit.
* `matmul_sumcheck_soundness` — **the composition**: a prover whose claimed output table is
  wrong AS A TABLE is accepted with probability `≤ (μ+ν)/|F| + κ·3/|F|`, honest side BUILT,
  only adversary-side hypotheses assumed.

## Residuals, named not stubbed

* **`[MATMUL-pcs]`** — a succinct verifier needs THREE multilinear-evaluation claims:
  `Ĉ(x,y)` for the claimed output, `Â(x,r)` for the left operand, and `B̂(r,y)` for the
  right operand. `Selvage/MultilinearCommitment.lean` gives them the correct hash-based
  shape (`MleEvalClaim = (root, point, value)`) over
  the EXISTING positional `OpeningScheme`: a Merkle commitment remains a vector commitment,
  while BaseFold proves the evaluation by an interactive reduction compiled through
  RBR/Fiat--Shamir/BCS. `MleEvalClaim.value_unique` proves that a binding root fixes the
  value inside the BaseFold degree window, and
  `Assurance/ZkmlMatmulCommitment.lean` binds all three exact claims. Here the mathematical
  verifier is still *given* the tables: the remaining gap is the braided BaseFold
  `Reduction`/`RbrKnowledgeSoundness` instance and its BCS query realization, not a new
  `openAt` abstraction.
* **`[MATMUL-fs]`** — the outer point `(x,y)` and the round challenges are drawn uniformly.
  Fiat–Shamir binding is `[PROVER-fs]`, open.
* **`[MATMUL-pad]`** — the tables live on cubes; a real layer's `784` becomes `1024` by
  `Theory/ZkmlMatmulSum.lean`'s `padded_contraction`, which is proved — but that the
  COMMITTED table really is zero outside the true extent is a commitment-layer obligation
  and is not checked here.
* The `ε` propagates. Unlike `eltAddSystem_denotes`, this is not an unconditional iff; a
  design mixing the scalar rung with this one must ADD the two, and only this one has an
  `ε` to add.
-/
import Assurance.AirSumcheckCubic
import Selvage.MultilinearZeroTest
import Theory.ZkmlMatmulSum

namespace Minidregg.Assurance

open Minidregg.Selvage

/-! ## §1. The two-block multilinear extension

A matmul's operands are indexed by TWO cubes (`Â : {0,1}^μ × {0,1}^κ → F`). Rather than
flatten into `Fin (μ+κ) → Bool` and fight `Fin.append`, the block extension is defined
directly and immediately shown to be a COMPOSITION of the landed one-block `mle` — so every
one-block theorem applies and nothing about multilinearity is restated. -/

section Blocks

variable {F : Type} [Field F] {μ ν : ℕ}

/-- **The two-block MLE.** `f̂(x,y) = Σ_a Σ_b f(a,b)·χ_a(x)·χ_b(y)`: multilinear in the `μ`
variables of `x` and in the `ν` variables of `y`, and equal to `f` on the product of the
two cubes. -/
def mle₂ (f : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) : F :=
  ∑ a, ∑ b, f a b * chiEval a x * chiEval b y

/-- The **row-partial** table: the first block bound to a field point, leaving a table on
the second cube. For a matmul's left operand this is `Â(x, ·)` — one of the two objects a
deployed verifier must open. -/
def rowPartial (f : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) :
    (Fin ν → Bool) → F := fun b => mle (fun a => f a b) x

/-- The **column-partial** table: the second block bound, leaving a table on the first
cube. For a matmul's right operand this is `B̂(·, y)`. -/
def colPartial (f : (Fin μ → Bool) → (Fin ν → Bool) → F) (y : Fin ν → F) :
    (Fin μ → Bool) → F := fun a => mle (fun b => f a b) y

/-- The block extension is the one-block extension of the row-partial table. This is the
fact that makes every landed `mle` theorem — multilinearity, Schwartz–Zippel, the sumcheck
realizer — apply to the block object with no new proof. -/
theorem mle₂_row (f : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ f x y = mle (rowPartial f x) y := by
  simp only [mle₂, rowPartial, mle, Finset.sum_mul]
  exact Finset.sum_comm

/-- ...and symmetrically, of the column-partial table. -/
theorem mle₂_col (f : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ f x y = mle (colPartial f y) x := by
  simp only [mle₂, colPartial, mle, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **Agreement**: on the product of the two cubes the extension IS the table. -/
theorem mle₂_agrees (f : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (a : Fin μ → Bool) (b : Fin ν → Bool) :
    mle₂ f (cubePt a) (cubePt b) = f a b := by
  rw [mle₂_row, mle_agrees]
  exact mle_agrees (fun a => f a b) a

/-- Linear in the table, on the subtraction side — how a defect table enters. -/
theorem mle₂_sub (f g : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (fun a b => f a b - g a b) x y = mle₂ f x y - mle₂ g x y := by
  simp only [mle₂, sub_mul, Finset.sum_sub_distrib]

end Blocks

/-! ## §2. The contraction identity — Thaler's matmul sumcheck, stated -/

section Contraction

variable {F : Type} [Field F] {μ κ ν : ℕ}

/-- The output table of a matmul on the cubes: `C(a,b) = Σ_p A(a,p)·B(p,b)`. This is
`Theory/ZkmlMatmulSum.lean`'s `contract` with `Fin k` replaced by the inner cube `{0,1}^κ`
— which is exactly what `padded_contraction` licenses for a non-dyadic `k`. -/
def matmulTable (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) : (Fin μ → Bool) → (Fin ν → Bool) → F :=
  fun a b => ∑ p, A a p * B p b

/-- **THE CONTRACTION IDENTITY.** `Ĉ(x,y) = Σ_p Â(x,p)·B̂(p,y)` at EVERY `(x,y)`, not just
at cube corners — an identity of the extensions, proved by reordering a triple sum. This is
the entire honest-prover side of the matmul argument: it says the sumcheck's claim is true
when the prover is honest, and it says so with no probability and no `eq` factor. -/
theorem mle₂_contraction (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    mle₂ (matmulTable A B) x y = ∑ p, rowPartial A x p * colPartial B y p := by
  have hL : mle₂ (matmulTable A B) x y
      = ∑ a, ∑ b, ∑ p, A a p * B p b * chiEval a x * chiEval b y := by
    simp only [mle₂, matmulTable, Finset.sum_mul]
  have hR : (∑ p, rowPartial A x p * colPartial B y p)
      = ∑ p, ∑ a, ∑ b, A a p * B p b * chiEval a x * chiEval b y := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rowPartial, colPartial, mle, mle, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR]
  calc ∑ a, ∑ b, ∑ p, A a p * B p b * chiEval a x * chiEval b y
      = ∑ a, ∑ p, ∑ b, A a p * B p b * chiEval a x * chiEval b y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p, ∑ a, ∑ b, A a p * B p b * chiEval a x * chiEval b y := Finset.sum_comm

/-- **The correction, as a theorem rather than prose.** The contraction and the pointwise
(Hadamard) product are different functions, so `cubicForm`'s `Â·B̂` face cannot be the
matmul claim. One 2×2 example over F₇ decides it: at `(0,1)` the contraction is
`1·6 + 2·1 = 1` and the Hadamard product is `2·6 = 5`. -/
theorem matmul_is_not_hadamard :
    ∃ (A B : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7),
      matmulTable A B ≠ fun a b => A a b * B a b := by
  refine ⟨fun a b => if a 0 then (if b 0 then 4 else 3) else (if b 0 then 2 else 1),
          fun a b => if a 0 then (if b 0 then 1 else 0) else (if b 0 then 6 else 5), ?_⟩
  intro h
  have := congrFun (congrFun h (fun _ => false)) (fun _ => true)
  revert this
  decide

end Contraction

/-! ## §3. The `cubicForm` instance — head ≡ 1, one product pair -/

section Instance

variable {F : Type} [Field F] {μ κ ν : ℕ}

/-- **The contraction's `cubicForm` instance.** Head `E ≡ 1` (no `eq` — the outer indices
are already bound), one product pair `(g,h)`, the second pair killed by `C ≡ 0`. So the
summand is exactly `ĝ(x)·ĥ(x)` and the landed cubic engine drives it unchanged. -/
theorem cubicForm_contraction (g h : (Fin κ → Bool) → F) :
    cubicForm (fun _ => (1 : F)) g h (fun _ => 0) (fun _ => 1)
      = fun x => mle g x * mle h x := by
  funext x
  simp only [cubicForm, mle_const]
  ring

/-- The cube total of that instance is the plain inner product of the two tables. -/
theorem cubicTotal_contraction (g h : (Fin κ → Bool) → F) :
    (∑ p, ((1 : F) * (g p * h p + 0 * 1))) = ∑ p, g p * h p :=
  Finset.sum_congr rfl fun _ _ => by ring

/-- **The claim the sumcheck proves IS the claimed output entry.** The cube total of the
contraction instance equals `Ĉ(x,y)` of the TRUE output table — `mle₂_contraction`,
packaged in the exact syntactic shape `cubic_sumcheck_soundness` consumes. -/
theorem matmul_claim_total (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    (∑ p, ((1 : F) * (rowPartial A x p * colPartial B y p + 0 * 1)))
      = mle₂ (matmulTable A B) x y := by
  rw [cubicTotal_contraction, mle₂_contraction]

/-- The honest prover family for the contraction sumcheck: the landed `cubicHonest` at the
contraction instance. Nothing new is realized — the four honest-side hypotheses of the
adaptive protocol are already discharged for `cubicHonest`. -/
noncomputable def matmulHonest (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) :
    (ℕ → F) → ℕ → Polynomial F :=
  cubicHonest (fun _ => (1 : F)) (rowPartial A x) (colPartial B y) (fun _ => 0) (fun _ => 1)

/-- The total the honest prover is anchored at, in the shape the protocol layer takes. -/
def matmulTrue (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) : F :=
  ∑ p, ((1 : F) * (rowPartial A x p * colPartial B y p + 0 * 1))

/-- **Completeness**: the honest prover, run on the true output table's entry at `(x,y)`,
is accepted on EVERY challenge vector — `cubicHonest_complete` with the claim rewritten
through the contraction identity. -/
theorem matmulHonest_complete (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F)
    (r : Fin κ → F) :
    SumcheckAccepts (v := κ) (matmulHonest A B x y (chalOf r))
      (matmulHonest A B x y (chalOf r))
      (mle₂ (matmulTable A B) x y) (mle₂ (matmulTable A B) x y) r := by
  rw [← matmul_claim_total A B x y]
  exact cubicHonest_complete (fun _ => (1 : F)) (rowPartial A x) (colPartial B y)
    (fun _ => 0) (fun _ => 1) r

end Instance

/-! ## §4. Two-block Schwartz–Zippel — the cost of binding the outer indices -/

section TwoBlockSZ

variable {F : Type} [Field F] [Fintype F] {μ ν : ℕ}

/-- An event that reads only the FIRST coordinate of a product draw keeps its bound. The
`Equiv.prodComm` flip is done once, here, at OPAQUE types: inlining it at the concrete
product types costs the elaborator an isDefEq blow-up, and the event is passed as an
explicit `q` with a pointwise `Iff` rather than as `fun w => ?p w.1`, because the latter is
not a Miller pattern and sends unification off a cliff. -/
private theorem uniformProb_fst_le {A B : Type} [Fintype A] [Fintype B] (q : A × B → Prop)
    (p : A → Prop) (hq : ∀ w, q w ↔ p w.1) {ε : ℝ} (hε : 0 ≤ ε) (h : uniformProb A p ≤ ε) :
    uniformProb (A × B) q ≤ ε := by
  rw [uniformProb_congr hq, ← uniformProb_equiv (Equiv.prodComm B A) (fun w : A × B => p w.1)]
  exact uniformProb_prod_le hε fun _ => h

/-- **Two-block multilinear Schwartz–Zippel.** A nonzero block table's extension vanishes
at a uniformly random `(x,y)` with probability at most `(μ+ν)/|F|`.

Composed from the landed one-block bound over the two blocks: `mle₂_row` turns the block
extension into the one-block extension of `rowPartial f x`, and the two cases are "that
table is identically zero" — which already kills a nonzero COLUMN of `f` with the `x` draw
— and "it is not", where the `y` draw kills a nonzero one-block extension. No new
probability toolkit. -/
theorem mle₂_zero_uniform_bound {f : (Fin μ → Bool) → (Fin ν → Bool) → F} (hf : f ≠ 0) :
    uniformProb ((Fin μ → F) × (Fin ν → F)) (fun w => mle₂ f w.1 w.2 = 0)
      ≤ ((μ : ℝ) + ν) / Fintype.card F := by
  -- A column of `f` that is not the zero table.
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hf
  obtain ⟨b₀, hb₀⟩ := Function.ne_iff.mp ha₀
  have hcol : (fun a => f a b₀) ≠ 0 := fun h => hb₀ (congrFun h a₀)
  have hstep : ∀ w : (Fin μ → F) × (Fin ν → F), mle₂ f w.1 w.2 = 0 →
      (rowPartial f w.1 = 0
        ∨ (rowPartial f w.1 ≠ 0 ∧ mle (rowPartial f w.1) w.2 = 0)) := by
    intro w hw
    rw [mle₂_row] at hw
    by_cases h : rowPartial f w.1 = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, hw⟩
  refine le_trans (uniformProb_mono hstep) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  have hfirst : uniformProb ((Fin μ → F) × (Fin ν → F)) (fun w => rowPartial f w.1 = 0)
      ≤ (μ : ℝ) / Fintype.card F := by
    refine uniformProb_fst_le _ (fun x => rowPartial f x = 0) (fun _ => Iff.rfl)
      (by positivity) ?_
    refine le_trans (uniformProb_mono (q := fun x => mle (fun a => f a b₀) x = 0) ?_)
      (mle_zero_uniform_bound hcol)
    intro x hx
    exact congrFun hx b₀
  have hsecond : uniformProb ((Fin μ → F) × (Fin ν → F))
      (fun w => rowPartial f w.1 ≠ 0 ∧ mle (rowPartial f w.1) w.2 = 0)
      ≤ (ν : ℝ) / Fintype.card F := by
    refine uniformProb_prod_le (by positivity) fun x => ?_
    -- Beta-reduce the fibre predicate BEFORE any `le_trans`: leaving it as a redex applied
    -- to a pair makes the `uniformProb_mono` unification non-first-order and it diverges.
    show uniformProb (Fin ν → F)
      (fun y => rowPartial f x ≠ 0 ∧ mle (rowPartial f x) y = 0) ≤ _
    by_cases hx : rowPartial f x = 0
    · rw [uniformProb_false fun _ h => h.1 hx]
      positivity
    · exact le_trans
        (uniformProb_mono (p := fun y => rowPartial f x ≠ 0 ∧ mle (rowPartial f x) y = 0)
          (q := fun y => mle (rowPartial f x) y = 0) fun _ h => h.2)
        (mle_zero_uniform_bound hx)
  rw [add_div]
  exact add_le_add hfirst hsecond

end TwoBlockSZ

/-! ## §5. The composition — a WRONG OUTPUT TABLE is caught, with both terms -/

section Soundness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {μ κ ν : ℕ}

/-- One draw of the whole protocol: the outer point `(x,y)`, then the `κ` sumcheck
challenges. The verifier computes its target from the CLAIMED output table `C` and runs the
cubic sumcheck against the honest contraction family. -/
def MatmulAccepts (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (C : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (w : ((Fin μ → F) × (Fin ν → F)) × (Fin κ → F)) : Prop :=
  SumcheckAccepts (v := κ) (prover (chalOf w.2))
    (matmulHonest A B w.1.1 w.1.2 (chalOf w.2))
    (mle₂ C w.1.1 w.1.2) (matmulTrue A B w.1.1 w.1.2) w.2

/-- **THE MATMUL SOUNDNESS THEOREM.** A prover whose claimed output table is wrong AS A
TABLE — one entry, anywhere — is accepted with probability at most

  `(μ+ν)/|F|` — the outer point failed to separate the claimed table from the true one,
  `+ κ·3/|F|` — the sumcheck on the inner index was laundered,

with the honest side BUILT (`matmulHonest`) and only adversary-side hypotheses
(prefix-measurability, the degree bound) assumed. The two terms are different events with
different causes; adding them is the content of the composition. -/
theorem matmul_sumcheck_soundness
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F} {B : (Fin κ → Bool) → (Fin ν → Bool) → F}
    {C : (Fin μ → Bool) → (Fin ν → Bool) → F} (hC : C ≠ matmulTable A B)
    {prover : (ℕ → F) → ℕ → Polynomial F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < κ →
      (prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (((Fin μ → F) × (Fin ν → F)) × (Fin κ → F)) (MatmulAccepts A B C prover)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) := by
  have hD : (fun a b => C a b - matmulTable A B a b) ≠ 0 := by
    intro h
    refine hC (funext fun a => funext fun b => ?_)
    have hab : C a b - matmulTable A B a b = 0 := by
      simpa using congrFun (congrFun h a) b
    exact sub_eq_zero.mp hab
  have hgap : ∀ (x : Fin μ → F) (y : Fin ν → F),
      mle₂ C x y - matmulTrue A B x y
        = mle₂ (fun a b => C a b - matmulTable A B a b) x y := by
    intro x y
    rw [mle₂_sub, matmulTrue, matmul_claim_total]
  have hstep : ∀ w : ((Fin μ → F) × (Fin ν → F)) × (Fin κ → F),
      MatmulAccepts A B C prover w →
        (mle₂ (fun a b => C a b - matmulTable A B a b) w.1.1 w.1.2 = 0
          ∨ AdaptiveAcceptsFalse prover (matmulHonest A B w.1.1 w.1.2)
              (mle₂ C w.1.1 w.1.2) (matmulTrue A B w.1.1 w.1.2) w.2) := by
    intro w hw
    by_cases hEq : mle₂ C w.1.1 w.1.2 = matmulTrue A B w.1.1 w.1.2
    · exact Or.inl (by rw [← hgap, hEq, sub_self])
    · exact Or.inr (acceptsFalse_iff_accepts.mpr ⟨hw, hEq⟩)
  refine le_trans (uniformProb_mono hstep) ?_
  refine le_trans (uniformProb_or_le _ _) (add_le_add ?_ ?_)
  · -- The outer point failed to separate: two-block Schwartz–Zippel.
    exact uniformProb_fst_le _
      (fun o : (Fin μ → F) × (Fin ν → F) =>
        mle₂ (fun a b => C a b - matmulTable A B a b) o.1 o.2 = 0)
      (fun _ => Iff.rfl) (by positivity) (mle₂_zero_uniform_bound hD)
  · -- The sumcheck was laundered: the cubic bound, at every fixed outer point.
    refine uniformProb_prod_le (by positivity) fun o => ?_
    show uniformProb (Fin κ → F)
      (fun r => AdaptiveAcceptsFalse prover (matmulHonest A B o.1 o.2)
        (mle₂ C o.1 o.2) (matmulTrue A B o.1 o.2) r) ≤ _
    exact cubic_sumcheck_soundness (E := fun _ => (1 : F)) (A := rowPartial A o.1)
      (B := colPartial B o.2) (C := fun _ => 0) (D := fun _ => 1) hpm hdeg

end Soundness

/-! ## §6. Teeth over F₇ — the identity FIRES off-cube, and the bad event is NONEMPTY

Three things could be wrong here and would survive a build: the contraction identity could
hold only on the cube (where it is trivial), the forgery event bounded above could be EMPTY
(a true bound about nothing), and the outer test could be doing no work at all. -/

namespace MatmulExample

/-- `A = [[1,2],[3,4]]` over F₇, as a table on `{0,1} × {0,1}` (`a 0` is the row bit). -/
def eA : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun a b => if a 0 then (if b 0 then 4 else 3) else (if b 0 then 2 else 1)

/-- `B = [[5,6],[0,1]]`. -/
def eB : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun a b => if a 0 then (if b 0 then 1 else 0) else (if b 0 then 6 else 5)

/-- The true product `A·B = [[5,8],[15,22]] = [[5,1],[1,1]]` over F₇, computed from the
definition of `matmulTable` rather than asserted. -/
theorem eC_computes :
    matmulTable eA eB (fun _ => false) (fun _ => false) = 5 ∧
    matmulTable eA eB (fun _ => false) (fun _ => true) = 1 ∧
    matmulTable eA eB (fun _ => true) (fun _ => false) = 1 ∧
    matmulTable eA eB (fun _ => true) (fun _ => true) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The identity fires OFF the cube.** At `x = 3, y = 5` — neither a corner nor a table
entry — both sides are `5`. `mle₂_contraction` is the general theorem; this witnesses that
its content is not cube agreement. -/
theorem contraction_offcube :
    mle₂ (matmulTable eA eB) ![3] ![5] = 5 ∧
    (∑ p, rowPartial eA ![3] p * colPartial eB ![5] p) = 5 := by
  refine ⟨by decide, by decide⟩

/-- A forged output table: the true product with the `(false,false)` entry bumped by one,
so the defect's extension is `(1−x)(1−y)`. -/
def eForged : (Fin 1 → Bool) → (Fin 1 → Bool) → ZMod 7 :=
  fun a b => matmulTable eA eB a b + (if a 0 || b 0 then 0 else 1)

/-- The forgery is a real change — built constructively and checked, so no tooth below can
decay into a statement about the true table. -/
theorem eForged_ne : eForged ≠ matmulTable eA eB := by
  intro h
  have := congrFun (congrFun h (fun _ => false)) (fun _ => false)
  revert this
  decide

/-- **The outer test DOES work**: at `x = 0, y = 0` the forged claim reads `6` and the truth
reads `5`, so a random outer point separates this forgery with high probability. -/
theorem eForged_caught : mle₂ eForged ![0] ![0] ≠ mle₂ (matmulTable eA eB) ![0] ![0] := by
  decide

/-- **THE BOUND CONSTRAINS A NONEMPTY EVENT.** The defect's extension is `(1−x)(1−y)`, so at
`x = 1` the forged table's extension AGREES with the truth: the verifier's outer draw can
land where a wrong output table is indistinguishable, and the sumcheck then proves a TRUE
claim about a FALSE table. That is exactly the `(μ+ν)/|F|` term, exhibited rather than
argued. -/
theorem eForged_survives : mle₂ eForged ![1] ![3] = mle₂ (matmulTable eA eB) ![1] ![3] := by
  decide

/-- ...and the same forgery at a different outer point IS separated (`4` against `2`), so
the survival above is a property of the POINT, not of the forgery. -/
theorem eForged_separated_elsewhere :
    mle₂ eForged ![2] ![3] ≠ mle₂ (matmulTable eA eB) ![2] ![3] := by
  decide

end MatmulExample

/-! ## §7. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.mle₂_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_row
/-- info: 'Minidregg.Assurance.mle₂_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_agrees
/-- info: 'Minidregg.Assurance.mle₂_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_contraction
/-- info: 'Minidregg.Assurance.matmul_is_not_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_is_not_hadamard
/-- info: 'Minidregg.Assurance.cubicForm_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicForm_contraction
/-- info: 'Minidregg.Assurance.matmul_claim_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_claim_total
/-- info: 'Minidregg.Assurance.matmulHonest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmulHonest_complete
/-- info: 'Minidregg.Assurance.mle₂_zero_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle₂_zero_uniform_bound
/-- info: 'Minidregg.Assurance.matmul_sumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmul_sumcheck_soundness
/-- info: 'Minidregg.Assurance.MatmulExample.eForged_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MatmulExample.eForged_survives
/-- info: 'Minidregg.Assurance.MatmulExample.eForged_caught' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MatmulExample.eForged_caught

end Minidregg.Assurance
