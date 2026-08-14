/-
# `Assurance/AirSumcheckQuadratic.lean` — [AIR-sumcheck-quadratic]: the MUL-gate face, CLOSED

**Substrate, said out loud:** this is the Lean-authored quadratic face of the arithmetization
soundness link. `Assurance/AirSumcheck` retired the LINEAR face (add gates + root pin) through
Selvage's proven sumcheck and routed mul-gate violations out loud as the `[AIR-sumcheck-quadratic]`
residual — witnessed REAL by `exMulCheat`, which satisfies the whole linear system while
cheating the mul gate. This file builds the missing channel: the degree-2 (R1CS-shaped) claim
`Σ_b (Â·B̂ − Ĉ)(b)` over MLEs, its honest QUADRATIC round-polynomial engine, and the retirement
of a violated mul gate by the SAME proven adaptive sumcheck at degree parameter `d = 2` —
bound `m·2/|F|`, quoted from `adaptive_sumcheck_soundness`, never re-derived. Composed with
`air_violation_dichotomy`, BOTH horns of the gate system are now retired: `airGateSystem_sound`.

## The encoding

The mul gates of a flattened term are indexed into a hypercube `{0,1}^m` (an embedding
`enc : Fin t ↪ (Fin m → Bool)`; padding to a power of two is the deployment bookkeeping).
Three TABLES read the gates' wires: `gateTableA/B/C` carry gate `k`'s `a`-read, `b`-read and
claimed output `auxv out` at corner `enc k` (zero elsewhere) — each read IS a wire-word pairing
(`gateTables_pairing`, via the linear face's `wireVec_read`). The DEFECT word
`D(j) = A(j)·B(j) − C(j)` vanishes at `enc k` iff gate `k` holds (`defectWord_read`). Each gate
is then ONE `Selvage.LinearConstraint` on `D` — indicator weight at its corner, target `0`
(`mulConstraint`, faithful by `mulConstraint_iff`) — so the WHOLE landed constraint machinery
applies to the mul system verbatim: per-constraint claims, γ-batching (`batch_survives_prob_le`
CITED for the γ round), the lot. The sumcheck that retires a violated claim walks the summand
`wt(b)·D(b) = (wt·A)(b)·B(b) − (wt·C)(b)` — STILL a product of two multilinear extensions minus
a third (`prodDiff`), because the mask folds into ONE factor. That is the degree-2 claim.

## The quadratic round engine (the new content — everything else is cited)

For multi-affine `Â, B̂` the product `Â·B̂` is degree ≤ 2 per coordinate: on every axis-`i` line

  `p(x[i↦t]) = (1−t)·p(x[i↦0]) + t·p(x[i↦1]) + t(t−1)·ΔÂ·ΔB̂`,   `Δf̂ = f̂(x[i↦1]) − f̂(x[i↦0])`

(`prodDiff_line`, from `mle_multilinear` + `ring`). Summing over the suffix cube renders round
`i`'s partial sum as an ACTUAL degree-≤2 polynomial `quadRoundPoly` (leading coefficient: the
summed cross term), evaluating to `roundSum` everywhere (`quadRoundPoly_eval`). `quadHonest`
packages the family in the adaptive protocol shape: prefix-measurable
(`quadHonest_prefixMeasurable`), degree `d = 2` (`quadHonest_degree`), boolean-sum consistent
along the truth chain (`quadHonest_boolean_sum`, via the landed `roundSum_zero`/`roundSum_succ`
— pure sum-splitting, no re-derivation), final check FACTORED as
`Â(r)·B̂(r) − Ĉ(r)` (`scChain_quadHonest_final`) — exactly the factored terminal comparison
`Selvage/MultilinearExtension` names as the quadratic face's missing piece. `quadHonest_complete`:
the honest run is accepted on every challenge.

**What is proved (no sorry):**

* `quad_sumcheck_soundness` — the engine consumed: any prefix-measurable degree-≤2 prover
  claiming a false total for `Σ_b (A·B − C)(b)` against the BUILT honest family is accepted
  with probability `≤ m·2/|F|` (`adaptive_sumcheck_soundness` at `d = 2`, cited).
* `quad_retires_constraint` — **the quadratic retirement keystone**: ANY linear constraint on a
  product-form word `D = A·B − C` that the word violates is retired by the sumcheck with the
  honest side BUILT (`quadHonest` on the mask-folded tables), bound `m·2/|F|`. Applies verbatim
  to each gate's claim AND to the γ-batched claim (`mulBatch_retired`) — the batched weight
  folds into the `A` factor just the same.
* `mulConstraint_iff` / `defectWord_read` / `gateTables_pairing` — the encoding is FAITHFUL:
  claim satisfaction IS `Gate.holds`, and the tables read the WIRE WORD (pairings against
  `wireVec` selectors, the linear face's own vocabulary).
* `airMulSumcheck_sound` — **[AIR-sumcheck-quadratic], closed.** A rejected assignment whose
  aux valuation satisfies the whole LINEAR system (the `exMulCheat` scenario — the violation
  hiding in the quadratic channel) violates SOME mul gate's claim, and the quadratic sumcheck
  retires it at the proven bound. The dichotomy's OTHER horn, caught.
* `airGateSystem_sound` — **the full arithmetization is sound.** A rejected assignment is
  caught, under EVERY aux valuation, by the linear-face sumcheck (`v·d/|F|`) or the
  quadratic-face sumcheck (`m·2/|F|`) — no unretired channel remains.
  `airGateSystem_sound_mle` is the same split with BOTH honest sides BUILT (linear face:
  `mleHonest` via `mle_retires_constraint`; quadratic face: `quadHonest`), given hypercube
  encodings of the wire domain and the mul-gate index.
* `airMulSumcheck_gamma_round` / `mulBatch_retired` / `airMulSumcheck_batch_complete` — the
  batched rendering, at parity with the linear face's §4: the γ round keeps a violating word
  alive for `≤ (t−1)/|F|` of γ (`batch_survives_prob_le`, cited), each surviving γ is caught by
  ONE quadratic sumcheck, and the honest wires render the whole mul system as one true batched
  sum-claim (`list_as_single_sumcheck`, cited).
* `airMulSumcheck_honest_never_caught` — the honest side: the forced extension satisfies every
  mul-gate claim (no acceptance hypothesis needed — mul gates never involve the root pin), so
  no run can falsely convict it (`satisfies_not_acceptsFalse`, cited).

**Keystones (ZMod 7, `AirFlatten`'s `(x+2)·x`, the `exMulCheat` witness — BUILT, computed):**
the honest forced wires satisfy every mul-gate claim and the batched claim; `exMulCheat` — the
valuation that fools the ENTIRE linear system — violates its gate's quadratic claim (claimed
`0`, true defect `5·3 − 0 = 1`), and the retirement bound FIRES concretely (`2/7`, one round,
cheating quadratic `X² + 4X + 1` passing the round check) on a NONEMPTY accept event
(challenge `r = 5` launders the lie into the honest fold value `f̂(5) = 4`). The keystone of
`AirSumcheck` closes: the violation `exMulCheat` smuggled past the linear face is caught here.

**Scope and residual — `[AIR-quadratic-selectors]` (prose, per the `[CRS-batch-sound]`
precedent: no placeholder Prop).** The gate-face soundness link is CLOSED: every violated gate
(linear or mul) yields a false sum-claim retired by the proven sumcheck at the proven bound,
with faithful encodings throughout — `[AIR-sumcheck-quadratic]` names no unretired channel
anymore. What remains is the ORACLE-side plumbing of a deployed prover, none of it a soundness
gap of this file's statements: (i) the verifier's final check evaluates
`mle (wt·A) r · mle B r − mle (wt·C) r`, whose factors are MLEs of the GATE tables; in
deployment the one committed oracle is the wire word's own MLE `ŵ`, and each factor's
evaluation `mle A (r) = Σ_y (Σ_k χ_{enc k}(r)·selᴬ(k,y))·w(y) + (const part)` is itself a
LinearConstraint on `w` — retirable by the LANDED linear face (`mle_retires_constraint`); the
missing lemma is exactly this table-evaluation-to-wire-word linearization (Spartan's second
phase). ⚑ **UPDATE 2026-08-14: the R1CS instance of exactly this move is now BUILT** —
`Assurance/SpartanR1CS.lean`'s `innerClaim`/`innerClaim_satisfied_iff` render a row-evaluation
claim as a `LinearConstraint` on the WITNESS word and retire it at `t·2/|F|`
(`spartan_inner_sound`), with the γ-batch of three at `2/|F|`. What is still open HERE is the
gate-table analogue's selector bookkeeping, not the technique. (ii) The alternative single-shot
randomization `Σ_b eq(z,b)·D(b) = mle D z` (better parameters than the γ round: `m/|F|` vs
`(t−1)/|F|`) needs the multilinear zero-test `Pr_{z ← F^m}[mle D z = 0] ≤ m/|F|` for `D ≠ 0` —
multivariate Schwartz–Zippel for multi-affine functions. ⚑ **CLOSED, and this sentence was stale
from the day `Selvage/MultilinearZeroTest.lean` landed**: `Selvage.mle_zero_uniform_bound` proves
exactly that bound and `Selvage.eqMle_zero_test` composes it with `Selvage.eqMle_fold` into the
test, with teeth for nonemptiness, tightness at `m = 1`, and necessity of `D ≠ 0`. A sibling
research lane quoted this paragraph as a live gap on 2026-08-14; that is the cost of a residual
that outlives its repair. (iii) `enc`/`eW` hypercube paddings (`t ≤ 2^m`) are constructed
per deployment, as hypotheses here (the `hyperIdx` precedent).
-/
import Assurance.AirSumcheck
import Selvage.QuadraticSumcheck

namespace Minidregg.Assurance

open Minidregg.Compiler Minidregg.Selvage Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. The quadratic round engine is owned by Selvage

The reusable degree-2 product sumcheck now lives in
`Selvage/QuadraticSumcheck.lean`. This AIR layer consumes it for multiplication
gates; BaseFold consumes the same engine for its table-times-equality braid. -/

section QuadEngine

/-- The quadratic retirement bundle: EVERY admissible (prefix-measurable, degree-≤2) prover
run against the BUILT honest family `quadHonest` on the constraint's claim — claimed total
`c.target`, truth chain anchored at the actual pairing, mask folded into the `A` factor — is
accepted with probability at most `m·2/|F|`. (A `Prop`-bundle so the AIR statements below can
carry the full retirement without restating five hypotheses each time.) -/
def QuadRetired {m : ℕ} (A B C : (Fin m → Bool) → F)
    (c : LinearConstraint (Fin m → Bool) F) : Prop :=
  ∀ prover : (ℕ → F) → ℕ → Polynomial F,
    PrefixMeasurable prover →
    (∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) →
    uniformProb (Fin m → F)
      (fun r => SumcheckAccepts (prover (chalOf r))
        (quadHonest (fun b => c.wt b * A b) B (fun b => c.wt b * C b) (chalOf r))
        c.target (trueSum c (fun b => A b * B b - C b)) r)
      ≤ (m : ℝ) * (2 / Fintype.card F)

/-- **The quadratic retirement keystone.** Any `LinearConstraint` on a PRODUCT-FORM word
`D = A·B − C` that the word violates is retired by the proven sumcheck with the honest side
BUILT: the weight folds into the `A` factor (`wt·D = (wt·A)·B − (wt·C)`, pointwise `ring`),
so the summand keeps the two-MLE product shape and `quadHonest` realizes the rounds at
`d = 2`. `adaptive_sumcheck_retires_constraint`, cited — no probability re-derived. Applies
verbatim to a single gate's indicator claim AND to the γ-batched claim of the whole mul
system. -/
theorem quad_retires_constraint {m : ℕ} {A B C : (Fin m → Bool) → F}
    {c : LinearConstraint (Fin m → Bool) F}
    (hviol : ¬ Satisfies (fun b => A b * B b - C b) c) :
    QuadRetired A B C c := by
  intro prover hpm hProverDeg
  have hsum : trueSum c (fun b => A b * B b - C b)
      = ∑ b, (c.wt b * A b * B b - c.wt b * C b) := by
    simp only [trueSum, constraintSummand]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h := adaptive_sumcheck_retires_constraint (v := m) (d := 2)
    (prover := prover)
    (honest := quadHonest (fun b => c.wt b * A b) B (fun b => c.wt b * C b))
    hviol hpm (quadHonest_prefixMeasurable _ _ _) hProverDeg
    (fun χ i hi => quadHonest_degree _ _ _ χ i hi)
    (fun r i hi => by
      rw [hsum]
      exact quadHonest_boolean_sum _ _ _ r i hi)
  simpa using h

end QuadEngine

/-! ## §2. The mul-gate system — product-form constraints over the gate-index hypercube.

Each mul gate `a·b = out` becomes ONE `Selvage.LinearConstraint` on the DEFECT word
`D(j) = A(j)·B(j) − C(j)`: indicator weight at the gate's corner, target `0`. The tables read
the gates' wires (hence, by `wireVec_read`, the WIRE WORD); the defect vanishes at a corner
iff that gate holds. The whole landed constraint machinery (γ-batching included) then applies
to the mul system verbatim, and §1 retires any violated claim because the summand keeps the
product shape. -/

variable {Idx : Type} [Fintype Idx] [DecidableEq Idx]

/-- The mul gates of a gate list (the complement of `AirSumcheck.addGates`). -/
def mulGates (gs : List (Gate F Idx)) : List (Gate F Idx) :=
  gs.filter fun g => decide (g.op = GateOp.mul)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem mem_mulGates {gs : List (Gate F Idx)} {g : Gate F Idx} :
    g ∈ mulGates gs ↔ g ∈ gs ∧ g.op = GateOp.mul := by
  simp [mulGates]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem mulGates_all_mul (gs : List (Gate F Idx)) :
    ∀ g ∈ mulGates gs, g.op = GateOp.mul :=
  fun _ hg => (mem_mulGates.mp hg).2

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- Indicator-masked sums collapse at the mask (the embedding is injective). -/
theorem sum_ite_enc {m t : ℕ} (enc : Fin t ↪ (Fin m → Bool)) (val : Fin t → F)
    (k : Fin t) :
    (∑ k' : Fin t, if enc k' = enc k then val k' else 0) = val k := by
  rw [Fintype.sum_eq_single k fun k' hk' => if_neg fun h => hk' (enc.injective h)]
  exact if_pos rfl

/-- The `A` table: gate `k`'s LEFT-input read sits at corner `enc k`; zero elsewhere. -/
def gateTableA {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool))
    (asg : Idx → F) (auxv : ℕ → F) : (Fin m → Bool) → F :=
  fun j => ∑ k, if enc k = j then (gs.get k).a.read asg auxv else 0

/-- The `B` table: gate `k`'s RIGHT-input read at corner `enc k`; zero elsewhere. -/
def gateTableB {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool))
    (asg : Idx → F) (auxv : ℕ → F) : (Fin m → Bool) → F :=
  fun j => ∑ k, if enc k = j then (gs.get k).b.read asg auxv else 0

/-- The `C` table: gate `k`'s CLAIMED output wire value at corner `enc k`; zero elsewhere.
(The var-assignment parameter is unused — outputs are always aux wires — but kept so the
three tables share one calling shape.) -/
def gateTableC {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool))
    (_asg : Idx → F) (auxv : ℕ → F) : (Fin m → Bool) → F :=
  fun j => ∑ k, if enc k = j then auxv (gs.get k).out else 0

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem gateTableA_read {m : ℕ} (gs : List (Gate F Idx))
    (enc : Fin gs.length ↪ (Fin m → Bool)) (asg : Idx → F) (auxv : ℕ → F)
    (k : Fin gs.length) :
    gateTableA gs enc asg auxv (enc k) = (gs.get k).a.read asg auxv :=
  sum_ite_enc enc _ k

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem gateTableB_read {m : ℕ} (gs : List (Gate F Idx))
    (enc : Fin gs.length ↪ (Fin m → Bool)) (asg : Idx → F) (auxv : ℕ → F)
    (k : Fin gs.length) :
    gateTableB gs enc asg auxv (enc k) = (gs.get k).b.read asg auxv :=
  sum_ite_enc enc _ k

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem gateTableC_read {m : ℕ} (gs : List (Gate F Idx))
    (enc : Fin gs.length ↪ (Fin m → Bool)) (asg : Idx → F) (auxv : ℕ → F)
    (k : Fin gs.length) :
    gateTableC gs enc asg auxv (enc k) = auxv (gs.get k).out :=
  sum_ite_enc enc _ k

/-- **The defect word**: `D(j) = A(j)·B(j) − C(j)` over the gate-index hypercube — zero at a
gate's corner iff that gate's multiplication is honest, zero at padding corners outright. -/
def defectWord {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool))
    (asg : Idx → F) (auxv : ℕ → F) : (Fin m → Bool) → F :=
  fun j => gateTableA gs enc asg auxv j * gateTableB gs enc asg auxv j
    - gateTableC gs enc asg auxv j

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- The defect at gate `k`'s corner is the gate's actual defect `a·b − out`. -/
theorem defectWord_read {m : ℕ} (gs : List (Gate F Idx))
    (enc : Fin gs.length ↪ (Fin m → Bool)) (asg : Idx → F) (auxv : ℕ → F)
    (k : Fin gs.length) :
    defectWord gs enc asg auxv (enc k)
      = (gs.get k).a.read asg auxv * (gs.get k).b.read asg auxv
        - auxv (gs.get k).out := by
  show gateTableA gs enc asg auxv (enc k) * gateTableB gs enc asg auxv (enc k)
      - gateTableC gs enc asg auxv (enc k) = _
  rw [gateTableA_read, gateTableB_read, gateTableC_read]

/-- Gate `k`'s claim as a `Selvage.LinearConstraint` on the defect word: indicator weight at the
gate's corner, target `0` — "the defect vanishes THERE". -/
def mulConstraint {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool))
    (k : Fin gs.length) : LinearConstraint (Fin m → Bool) F where
  wt := fun j => if j = enc k then 1 else 0
  target := 0

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- **The mul-gate encoding is FAITHFUL**: satisfaction of gate `k`'s constraint by the
defect word IS `Gate.holds` — indicator pairing (`dotWt_indicator`, the linear face's own
lemma) + the corner read. -/
theorem mulConstraint_iff {m : ℕ} (gs : List (Gate F Idx))
    (enc : Fin gs.length ↪ (Fin m → Bool)) (asg : Idx → F) (auxv : ℕ → F)
    (k : Fin gs.length) (hop : (gs.get k).op = GateOp.mul) :
    Satisfies (defectWord gs enc asg auxv) (mulConstraint gs enc k)
      ↔ (gs.get k).holds asg auxv := by
  show dotWt (fun j => if j = enc k then 1 else 0) (defectWord gs enc asg auxv) = 0 ↔ _
  rw [dotWt_indicator, defectWord_read]
  unfold Gate.holds
  rw [hop]
  exact sub_eq_zero

/-- **The mul system**: one indicator constraint per mul gate — a plain
`List (LinearConstraint _ F)`, so the landed γ-batching machinery applies verbatim. -/
def mulSystem {m : ℕ} (gs : List (Gate F Idx)) (enc : Fin gs.length ↪ (Fin m → Bool)) :
    List (LinearConstraint (Fin m → Bool) F) :=
  (List.finRange gs.length).map (mulConstraint gs enc)

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem mem_mulSystem {m : ℕ} {gs : List (Gate F Idx)}
    {enc : Fin gs.length ↪ (Fin m → Bool)} {c : LinearConstraint (Fin m → Bool) F} :
    c ∈ mulSystem gs enc ↔ ∃ k, c = mulConstraint gs enc k := by
  simp [mulSystem, eq_comm]

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- Completeness at the system level: an aux valuation satisfying every (mul) gate satisfies
every constraint of the mul system. -/
theorem mulSystem_satisfied {m : ℕ} {gs : List (Gate F Idx)}
    (enc : Fin gs.length ↪ (Fin m → Bool)) {asg : Idx → F} {auxv : ℕ → F}
    (hmul : ∀ g ∈ gs, g.op = GateOp.mul) (hhold : ∀ g ∈ gs, g.holds asg auxv) :
    ∀ c ∈ mulSystem gs enc, Satisfies (defectWord gs enc asg auxv) c := by
  intro c hc
  obtain ⟨k, rfl⟩ := mem_mulSystem.mp hc
  exact (mulConstraint_iff gs enc asg auxv k (hmul _ (List.get_mem gs k))).mpr
    (hhold _ (List.get_mem gs k))

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- Soundness at the system level: a violated (mul) gate yields a violated constraint. -/
theorem mulSystem_violated {m : ℕ} {gs : List (Gate F Idx)}
    (enc : Fin gs.length ↪ (Fin m → Bool)) {asg : Idx → F} {auxv : ℕ → F}
    (hmul : ∀ g ∈ gs, g.op = GateOp.mul) (h : ∃ g ∈ gs, ¬ g.holds asg auxv) :
    ∃ k, ¬ Satisfies (defectWord gs enc asg auxv) (mulConstraint gs enc k) := by
  obtain ⟨k, hk⟩ := List.exists_mem_iff_get.mp h
  exact ⟨k, fun hs =>
    hk ((mulConstraint_iff gs enc asg auxv k (hmul _ (List.get_mem gs k))).mp hs)⟩

omit [Fintype Idx] [DecidableEq Idx] in
/-- **The γ-batched mul claim is retired too**: the batched weight folds into the `A` factor
exactly like an indicator does, so §1 applies verbatim — for any γ where the batch stays
violated, ONE quadratic sumcheck catches the word except with probability `m·2/|F|`. -/
theorem mulBatch_retired {m : ℕ} {gs : List (Gate F Idx)}
    {enc : Fin gs.length ↪ (Fin m → Bool)} {asg : Idx → F} {auxv : ℕ → F} {γ : F}
    (hγ : ¬ Satisfies (defectWord gs enc asg auxv)
      (batchConstraint γ (mulSystem gs enc))) :
    QuadRetired (gateTableA gs enc asg auxv) (gateTableB gs enc asg auxv)
      (gateTableC gs enc asg auxv) (batchConstraint γ (mulSystem gs enc)) :=
  quad_retires_constraint hγ

/-! ## §3. The AIR statements — the dichotomy's mul horn retired, the gate system closed.

Everything below composes `air_violation_dichotomy` (the linear face's soundness split) with
§1's quadratic retirement and the LANDED linear/batch theorems. The mul gates of the
flattening are `mulGates (flatten t 0).gates`; their hypercube indexing `enc` is a hypothesis
(the `hyperIdx` precedent — padding `t ≤ 2^m` is deployment bookkeeping). -/

omit [Fintype F] [DecidableEq F] in
/-- The tables of the flattening's mul-gate system read the WIRE WORD: at every gate corner,
each table value is the pairing of the gate's `wireVec` selector against
`wireWord asg auxv`, plus the selector's constant part — the linear face's own read
decomposition (`wireVec_read`), applied through `flatten_scoped`. The quadratic claim
constrains the SAME object the linear claims constrain. -/
theorem gateTables_pairing {m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (auxv : ℕ → F)
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool))
    (k : Fin (mulGates (flatten t 0).gates).length) :
    gateTableA (mulGates (flatten t 0).gates) enc asg auxv (enc k)
        = dotWt (wireVec (flatten t 0).next ((mulGates (flatten t 0).gates).get k).a)
            (wireWord (N := (flatten t 0).next) asg auxv)
          + wireConst ((mulGates (flatten t 0).gates).get k).a
      ∧ gateTableB (mulGates (flatten t 0).gates) enc asg auxv (enc k)
          = dotWt (wireVec (flatten t 0).next ((mulGates (flatten t 0).gates).get k).b)
              (wireWord (N := (flatten t 0).next) asg auxv)
            + wireConst ((mulGates (flatten t 0).gates).get k).b
      ∧ gateTableC (mulGates (flatten t 0).gates) enc asg auxv (enc k)
          = dotWt (wireVec (flatten t 0).next
                (WireRef.aux ((mulGates (flatten t 0).gates).get k).out))
              (wireWord (N := (flatten t 0).next) asg auxv) := by
  have hg : (mulGates (flatten t 0).gates).get k ∈ (flatten t 0).gates :=
    (mem_mulGates.mp (List.get_mem _ k)).1
  obtain ⟨-, -, hscoped⟩ := flatten_scoped t 0
  obtain ⟨ha, hb, -, houtlt⟩ := hscoped _ hg
  refine ⟨?_, ?_, ?_⟩
  · rw [gateTableA_read,
      ← wireVec_read asg auxv (WireRef.auxIn_mono le_rfl houtlt.le ha)]
  · rw [gateTableB_read,
      ← wireVec_read asg auxv (WireRef.auxIn_mono le_rfl houtlt.le hb)]
  · have hr := wireVec_read (N := (flatten t 0).next) asg auxv
      (w := WireRef.aux ((mulGates (flatten t 0).gates).get k).out)
      ⟨Nat.zero_le _, houtlt⟩
    rw [WireRef.read_aux,
      show wireConst (WireRef.aux ((mulGates (flatten t 0).gates).get k).out
          : WireRef F Idx) = (0 : F) from rfl,
      add_zero] at hr
    rw [gateTableC_read, hr]

omit [Fintype Idx] [DecidableEq Idx] in
/-- The mul horn, packaged: a violated mul gate of the flattening yields a violated
indicator claim on the defect word AND its full quadratic retirement. Shared spine of
`airMulSumcheck_sound` and both apex statements. -/
theorem air_mul_horn {m : ℕ} {asg : Idx → F} {t : Term (AirSig F Idx)} {auxv : ℕ → F}
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool))
    (h : ∃ g ∈ (flatten t 0).gates, g.op = GateOp.mul ∧ ¬ g.holds asg auxv) :
    ∃ k, ¬ Satisfies (defectWord (mulGates (flatten t 0).gates) enc asg auxv)
        (mulConstraint (mulGates (flatten t 0).gates) enc k) ∧
      QuadRetired (gateTableA (mulGates (flatten t 0).gates) enc asg auxv)
        (gateTableB (mulGates (flatten t 0).gates) enc asg auxv)
        (gateTableC (mulGates (flatten t 0).gates) enc asg auxv)
        (mulConstraint (mulGates (flatten t 0).gates) enc k) := by
  obtain ⟨g, hg, hop, hviol⟩ := h
  obtain ⟨k, hk⟩ := mulSystem_violated enc (mulGates_all_mul _)
    ⟨g, mem_mulGates.mpr ⟨hg, hop⟩, hviol⟩
  exact ⟨k, hk, quad_retires_constraint hk⟩

/-- **`airMulSumcheck_sound` — [AIR-sumcheck-quadratic], closed.** A wire assignment the
circuit REJECTS, whose aux valuation satisfies the WHOLE linear system (the `exMulCheat`
scenario: the violation is hiding in the quadratic channel), violates SOME mul gate's
indicator claim on the defect word — and the proven adaptive sumcheck, run on that claim with
the honest quadratic family BUILT, accepts any admissible prover with probability at most
`m·2/|F|`. The bound is `adaptive_sumcheck_retires_constraint` at `d = 2` through
`quad_retires_constraint`; the AIR content is `air_violation_dichotomy` + the faithful
encoding (`mulConstraint_iff`). The dichotomy's OTHER horn, retired. -/
theorem airMulSumcheck_sound {m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (hlin : ∀ c ∈ flatLinearSystem t,
      Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c)
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    ∃ k, ¬ Satisfies (defectWord (mulGates (flatten t 0).gates) enc asg auxv)
        (mulConstraint (mulGates (flatten t 0).gates) enc k) ∧
      QuadRetired (gateTableA (mulGates (flatten t 0).gates) enc asg auxv)
        (gateTableB (mulGates (flatten t 0).gates) enc asg auxv)
        (gateTableC (mulGates (flatten t 0).gates) enc asg auxv)
        (mulConstraint (mulGates (flatten t 0).gates) enc k) := by
  rcases air_violation_dichotomy asg t hrej auxv with hmul | ⟨c, hc, hviol⟩
  · exact air_mul_horn enc hmul
  · exact absurd (hlin c hc) hviol

/-- **`airGateSystem_sound` — the FULL arithmetization is sound.** A rejected assignment is
caught under EVERY aux valuation: either some LINEAR constraint of the encoded system is
violated and the proven sumcheck retires it at `v·d/|F|` (the linear face,
`adaptive_sumcheck_retires_constraint` — any admissible honest chain), or some MUL gate's
quadratic claim is violated and the proven sumcheck retires it at `m·2/|F|` with the honest
side BUILT (`quadHonest`). No unretired channel remains: this closes the derived-
arithmetization → proven-soundness link at the gate level. -/
theorem airGateSystem_sound {v d m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    (∃ c ∈ flatLinearSystem t,
      ¬ Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c ∧
      ∀ (prover honest : (ℕ → F) → ℕ → Polynomial F),
        PrefixMeasurable prover → PrefixMeasurable honest →
        (∀ (χ : ℕ → F) (i : ℕ), i < v →
          (prover χ i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ (χ : ℕ → F) (i : ℕ), i < v →
          (honest χ i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ r : Fin v → F, ∀ i, i < v →
          (honest (chalOf r) i).eval 0 + (honest (chalOf r) i).eval 1
            = scChain (trueSum c (wireWord (N := (flatten t 0).next) asg auxv))
                (honest (chalOf r)) (chalOf r) i) →
        uniformProb (Fin v → F)
          (fun r => SumcheckAccepts (prover (chalOf r)) (honest (chalOf r)) c.target
            (trueSum c (wireWord (N := (flatten t 0).next) asg auxv)) r)
          ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F))
    ∨ (∃ k, ¬ Satisfies (defectWord (mulGates (flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (flatten t 0).gates) enc k) ∧
        QuadRetired (gateTableA (mulGates (flatten t 0).gates) enc asg auxv)
          (gateTableB (mulGates (flatten t 0).gates) enc asg auxv)
          (gateTableC (mulGates (flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (flatten t 0).gates) enc k)) := by
  rcases air_violation_dichotomy asg t hrej auxv with hmul | ⟨c, hc, hviol⟩
  · exact Or.inr (air_mul_horn enc hmul)
  · exact Or.inl ⟨c, hc, hviol, fun prover honest hpm hhm hPD hHD hH =>
      adaptive_sumcheck_retires_constraint hviol hpm hhm hPD hHD hH⟩

/-- **The apex with BOTH honest sides BUILT.** Same dichotomy, but given hypercube encodings
of the wire domain (`eW`) and the mul-gate index (`enc`), each horn carries its constructed
realizer: the linear face's `mleHonest` (via the landed `mle_retires_constraint`, `d = 1`,
bound `w·1/|F|`) or the quadratic face's `quadHonest` (`d = 2`, bound `m·2/|F|`). Only
adversary-side hypotheses remain in either horn — the arithmetization inherits the proven
soundness with no hypothesized honest chain anywhere. -/
theorem airGateSystem_sound_mle {w m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (eW : WireIdx Idx (flatten t 0).next ≃ (Fin w → Bool))
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    (∃ c ∈ flatLinearSystem t,
      ¬ Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c ∧
      ∀ prover : (ℕ → F) → ℕ → Polynomial F,
        PrefixMeasurable prover →
        (∀ (χ : ℕ → F) (i : ℕ), i < w →
          (prover χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ)) →
        uniformProb (Fin w → F)
          (fun r => SumcheckAccepts (prover (chalOf r))
            (mleHonest (fun b => constraintSummand c
              (wireWord (N := (flatten t 0).next) asg auxv) (eW.symm b)) (chalOf r))
            c.target (trueSum c (wireWord (N := (flatten t 0).next) asg auxv)) r)
          ≤ (w : ℝ) * (1 / Fintype.card F))
    ∨ (∃ k, ¬ Satisfies (defectWord (mulGates (flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (flatten t 0).gates) enc k) ∧
        QuadRetired (gateTableA (mulGates (flatten t 0).gates) enc asg auxv)
          (gateTableB (mulGates (flatten t 0).gates) enc asg auxv)
          (gateTableC (mulGates (flatten t 0).gates) enc asg auxv)
          (mulConstraint (mulGates (flatten t 0).gates) enc k)) := by
  rcases air_violation_dichotomy asg t hrej auxv with hmul | ⟨c, hc, hviol⟩
  · exact Or.inr (air_mul_horn enc hmul)
  · exact Or.inl ⟨c, hc, hviol, fun prover hpm hPD =>
      mle_retires_constraint eW hviol hpm hPD⟩

/-- **The γ round of the mul system.** A rejected assignment whose aux valuation satisfies
the linear system has a violated mul gate, so the γ-batched mul claim stays TRUE for at most
`(t−1)/|F|` of uniform γ — `batch_survives_prob_le`, cited. Together with `mulBatch_retired`
this is the batched pipeline at full parity with the linear face's §4: additive RBR entries
`(t−1)/|F| + m·2/|F|` for the whole mul system through ONE quadratic sumcheck. -/
theorem airMulSumcheck_gamma_round {m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (hlin : ∀ c ∈ flatLinearSystem t,
      Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c)
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    uniformProb F (fun γ =>
        Satisfies (defectWord (mulGates (flatten t 0).gates) enc asg auxv)
          (batchConstraint γ (mulSystem (mulGates (flatten t 0).gates) enc)))
      ≤ (((mulSystem (mulGates (flatten t 0).gates) enc).length - 1 : ℕ) : ℝ)
          / Fintype.card F := by
  rcases air_violation_dichotomy asg t hrej auxv with ⟨g, hg, hop, hviol⟩ | ⟨c, hc, hviol⟩
  · obtain ⟨k, hk⟩ := mulSystem_violated enc (mulGates_all_mul _)
      ⟨g, mem_mulGates.mpr ⟨hg, hop⟩, hviol⟩
    exact batch_survives_prob_le
      ⟨mulConstraint (mulGates (flatten t 0).gates) enc k,
        mem_mulSystem.mpr ⟨k, rfl⟩, hk⟩
  · exact absurd (hlin c hc) hviol

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- **The honest side**: the FORCED aux extension satisfies every gate of the flattening
(`flatten_sound` — no acceptance hypothesis needed: mul gates never involve the root pin), so
every mul-gate claim is satisfied and no sumcheck run on any of them can be an `AcceptsFalse`
event (`satisfies_not_acceptsFalse`, cited) — the honest prover is never falsely convicted on
the quadratic face. -/
theorem airMulSumcheck_honest_never_caught {m v : ℕ} (asg : Idx → F)
    (t : Term (AirSig F Idx))
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    ∃ auxv : ℕ → F, ∀ k (prover honest : ℕ → Polynomial F) (r : Fin v → F),
      ¬ AcceptsFalse prover honest
        (mulConstraint (mulGates (flatten t 0).gates) enc k).target
        (trueSum (mulConstraint (mulGates (flatten t 0).gates) enc k)
          (defectWord (mulGates (flatten t 0).gates) enc asg auxv)) r := by
  obtain ⟨auxv, hgates, -⟩ := flatten_sound asg t 0
  refine ⟨auxv, fun k prover honest r => satisfies_not_acceptsFalse ?_ r⟩
  exact mulSystem_satisfied enc (mulGates_all_mul _)
    (fun g hg => hgates g (mem_mulGates.mp hg).1) _ (mem_mulSystem.mpr ⟨k, rfl⟩)

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
/-- **Batched completeness**: the forced extension renders the WHOLE mul system as ONE true
γ-batched sum-claim, for every γ (`list_as_single_sumcheck`, cited) — the claim object the
decider's single quadratic sumcheck walks. -/
theorem airMulSumcheck_batch_complete {m : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (enc : Fin (mulGates (flatten t 0).gates).length ↪ (Fin m → Bool)) :
    ∃ auxv : ℕ → F, ∀ γ : F,
      ∑ j, constraintSummand
          (batchConstraint γ (mulSystem (mulGates (flatten t 0).gates) enc))
          (defectWord (mulGates (flatten t 0).gates) enc asg auxv) j
        = (batchConstraint γ (mulSystem (mulGates (flatten t 0).gates) enc)).target := by
  obtain ⟨auxv, hgates, -⟩ := flatten_sound asg t 0
  exact ⟨auxv, fun γ => list_as_single_sumcheck γ
    (mulSystem_satisfied enc (mulGates_all_mul _)
      (fun g hg => hgates g (mem_mulGates.mp hg).1))⟩

/-! ## §4. Keystones — BUILT, over `ZMod 7`, on the `exMulCheat` witness.

`AirSumcheck`'s honest-scope witness `exMulCheat` satisfies EVERY linear constraint of
`exFlat`'s system while cheating the mul gate `aux₀ · x = aux₁` — precisely the assignment
the linear face cannot catch (`exMulCheat_shows_residual_real`). Here it IS caught: its
quadratic claim is violated (claimed `0`, true defect `5·3 − 0 = 1`), the retirement bound
fires concretely (`2/7`, honest side BUILT), and the caught event is NONEMPTY. Everything
computes on the actual flattening. -/

namespace ASQExample

open ASExample

/-- The mul-gate list of `exFlat`'s flattening: the single gate `aux₀ · x = aux₁`. -/
def exMulGs : List (Gate (ZMod 7) Unit) := [⟨.mul, .aux 0, .var (), 1⟩]

/-- *Computes, on the nose*: the filter extracts exactly that gate — definitionally. -/
example : mulGates (flatten exFlat 0).gates = exMulGs := rfl

/-- The one-gate hypercube indexing: the gate sits at corner `(true)` of `{0,1}¹`. -/
def exEnc : Fin exMulGs.length ↪ (Fin 1 → Bool) :=
  ⟨fun _ _ => true, fun x y _ => by
    have hx : x.val < 1 := x.isLt
    have hy : y.val < 1 := y.isLt
    exact Fin.ext (by omega)⟩

/-- The one gate's index. -/
def exK : Fin exMulGs.length := ⟨0, by decide⟩

/-- **SATISFIABLE, BUILT**: the honest forced wires (`aux₀ = 5`, `aux₁ = 1`) satisfy every
constraint of the mul system — the defect at the gate corner is `5·3 − 1 = 0`, computed. -/
example : ∀ c ∈ mulSystem exMulGs exEnc,
    Satisfies (defectWord exMulGs exEnc exAsg exForced) c := by decide

/-- The faithfulness iff FIRES on data: claim satisfaction IS the gate's `holds`. -/
example : Satisfies (defectWord exMulGs exEnc exAsg exForced)
      (mulConstraint exMulGs exEnc exK)
    ↔ (exMulGs.get exK).holds exAsg exForced :=
  mulConstraint_iff exMulGs exEnc exAsg exForced exK rfl

/-- Completeness fires on data: the honest quadratic prover of the forced wires' tables is
accepted on every challenge (`quadHonest_complete`). -/
example (r : Fin 1 → ZMod 7) := quadHonest_complete
  (gateTableA exMulGs exEnc exAsg exForced) (gateTableB exMulGs exEnc exAsg exForced)
  (gateTableC exMulGs exEnc exAsg exForced) r

/-! ### Teeth: the claim the linear face could not see, violated and retired. -/

/-- The violated claim's mask-folded `A` table (the indicator weight folds in). -/
def exA : (Fin 1 → Bool) → ZMod 7 :=
  fun j => (mulConstraint exMulGs exEnc exK).wt j
    * gateTableA exMulGs exEnc exAsg exMulCheat j

/-- The (shared, unmasked) `B` table. -/
def exB : (Fin 1 → Bool) → ZMod 7 := gateTableB exMulGs exEnc exAsg exMulCheat

/-- The mask-folded `C` table — `exMulCheat`'s cheat (`aux₁ = 0`) lives here. -/
def exC : (Fin 1 → Bool) → ZMod 7 :=
  fun j => (mulConstraint exMulGs exEnc exK).wt j
    * gateTableC exMulGs exEnc exAsg exMulCheat j

/-- The tables at the gate corner, computed: `A = 5` (the `aux₀` read), `B = 3` (the `x`
read), `C = 0` (the cheated output wire). -/
example : exA (fun _ => true) = 5 ∧ exB (fun _ => true) = 3
    ∧ exC (fun _ => true) = 0 := by decide

/-- **TEETH — the quadratic channel catches what the linear face missed.** `exMulCheat`
satisfies every linear constraint (`exMulCheat_shows_residual_real`), yet VIOLATES its
gate's quadratic claim on the defect word. -/
theorem exMulCheat_violates :
    ¬ Satisfies (defectWord exMulGs exEnc exAsg exMulCheat)
      (mulConstraint exMulGs exEnc exK) := by decide

/-- The violated claim's TRUE total, computed: the defect `5·3 − 0 = 1` (claimed: `0`). -/
theorem exMulCheat_trueSum :
    trueSum (mulConstraint exMulGs exEnc exK)
      (defectWord exMulGs exEnc exAsg exMulCheat) = 1 := by decide

/-- **The degree-2 claim is genuinely quadratic, computed**: the product extension of the
violated claim is `x²` over `ZMod 7` — the round data are `g(0) = 0`, `g(1) = 1`, cross term
`ΔÂ·ΔB̂ = 5·3 = 1` (the leading coefficient is NONZERO: degree 2 is attained, not just
bounded), and the off-cube oracle value is `f̂(5) = 25 = 4`. -/
example : roundSum (prodDiff exA exB exC) (fun _ => 5) ⟨0, by decide⟩ 0 = 0
    ∧ roundSum (prodDiff exA exB exC) (fun _ => 5) ⟨0, by decide⟩ 1 = 1
    ∧ quadCross exA exB (fun _ => 5) ⟨0, by decide⟩ = 1
    ∧ prodDiff exA exB exC (fun _ => 5) = 4 := by decide

/-- The cheating prover: the quadratic `X² + 4X + 1` — it passes the round check on the
false claimed total `0` (`g̃(0) + g̃(1) = 1 + 6 = 0` over `ZMod 7`) while differing from the
honest round polynomial `X²`. -/
noncomputable def exCheat : (ℕ → ZMod 7) → ℕ → Polynomial (ZMod 7) :=
  fun _ _ => Polynomial.C 1 * X ^ 2 + Polynomial.C 4 * X + Polynomial.C 1

/-- **TEETH — the retirement bound FIRES.** One-round quadratic sumcheck on `exMulCheat`'s
violated claim, honest side BUILT (`quadHonest` on the mask-folded tables), cheating prover
`X² + 4X + 1`: `quad_retires_constraint` delivers `Pr[accept] ≤ 2/7` with every hypothesis
discharged concretely. -/
theorem exMulCheat_caught :
    uniformProb (Fin 1 → ZMod 7)
      (fun r => SumcheckAccepts (exCheat (chalOf r))
        (quadHonest exA exB exC (chalOf r))
        (mulConstraint exMulGs exEnc exK).target
        (trueSum (mulConstraint exMulGs exEnc exK)
          (defectWord exMulGs exEnc exAsg exMulCheat)) r)
      ≤ 2 / 7 := by
  have h := quad_retires_constraint (m := 1)
    (A := gateTableA exMulGs exEnc exAsg exMulCheat)
    (B := gateTableB exMulGs exEnc exAsg exMulCheat)
    (C := gateTableC exMulGs exEnc exAsg exMulCheat)
    (c := mulConstraint exMulGs exEnc exK)
    exMulCheat_violates exCheat
    (fun _ _ _ _ => rfl)
    (fun χ i _ => lt_of_le_of_lt Polynomial.degree_quadratic_le (by decide))
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- The laundering challenge: `r = 5`. -/
def exR : Fin 1 → ZMod 7 := fun _ => 5

/-- **The caught-event is NONEMPTY**: at challenge `r = 5` the cheat IS accepted — the round
check passes on the claimed `0`, and the fold `g̃(5) = 25 + 20 + 1 = 4` equals the honest
chain's factored oracle value `f̂(5) = 4` — the lie is laundered. The `2/7` bound constrains
a real event, not a vacuum. -/
theorem exMulCheat_accept_witness :
    SumcheckAccepts (v := 1) (exCheat (chalOf exR))
      (quadHonest exA exB exC (chalOf exR))
      (mulConstraint exMulGs exEnc exK).target
      (trueSum (mulConstraint exMulGs exEnc exK)
        (defectWord exMulGs exEnc exAsg exMulCheat))
      exR := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    show (exCheat (chalOf exR) 0).eval 0 + (exCheat (chalOf exR) 0).eval 1
      = (mulConstraint exMulGs exEnc exK).target
    simp only [exCheat, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    decide
  · show (exCheat (chalOf exR) 0).eval (chalOf exR 0)
      = (quadHonest exA exB exC (chalOf exR) 0).eval (chalOf exR 0)
    rw [quadHonest, dif_pos (by decide : (0 : ℕ) < 1), quadRoundPoly_eval,
      roundSum_last rfl]
    simp only [exCheat, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    decide

/-- Batch-teeth premise inhabited: the batched mul claim is violated at `γ = 3` (indeed at
every γ — the system is a singleton), so `mulBatch_retired`'s hypothesis holds on data. -/
example : ¬ Satisfies (defectWord exMulGs exEnc exAsg exMulCheat)
    (batchConstraint 3 (mulSystem exMulGs exEnc)) := by decide

/-- **The keystone FIRES on real data** — every premise of `airMulSumcheck_sound`
discharged concretely: `x = 3` is rejected, `exMulCheat` satisfies the WHOLE linear system
(the very witness that forced the residual), so the violation is caught in the quadratic
channel at the proven bound. -/
example := airMulSumcheck_sound (m := 1) exAsg exFlat exFlat_rejects exMulCheat
  exMulCheat_shows_residual_real.1 exEnc

/-- The apex fires on the same data: the full gate-system soundness disjunction,
instantiated end-to-end. -/
example := airGateSystem_sound (v := 1) (d := 1) (m := 1) exAsg exFlat exFlat_rejects
  exMulCheat exEnc

end ASQExample

end Minidregg.Assurance
