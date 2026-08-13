/-
# `Assurance/AirSumcheck.lean` — [AIR-sumcheck]: the DERIVED gate system retired by the PROVEN sumcheck

**Substrate, said out loud:** this is the Lean-authored soundness link. The gate system comes
out of `Compiler/AirFlatten`'s fold (`flatten`), the sumcheck bound out of `Selvage/Sumcheck`'s
proved round-by-round soundness; this file only ENCODES the former as the latter's claim
object and composes the landed theorems. No constraint is hand-authored here, and no
soundness is re-derived.

## The argument

`gatesHold asg auxv gates` says every gate `a ⋄ b = out` holds. Over the finite WIRE WORD
`wireWord asg auxv : (Idx ⊕ Fin N) → F` (original variables ⊕ the `N` allocated aux wires):

* an ADD gate `a + b = out` is the LINEAR equation `⟨vec(a) + vec(b) − vec(out), w⟩ = −(consts)`
  — a `Selvage.LinearConstraint`, i.e. (by `constraint_as_sumcheck`, definitional) a sumcheck
  sum-claim. `addGateLin_iff` proves the encoding faithful: satisfaction of the constraint IS
  `Gate.holds`, given the scoping `flatten_scoped` provides for every emitted gate.
* the ROOT PIN `root = 0` is likewise linear (`rootZero`, `rootZero_iff`).
* a MUL gate `a · b = out` is DEGREE-2 in the wire word — NOT a linear functional, hence not a
  `LinearConstraint`. Its sumcheck retirement needs the multilinear-extension encoding
  (R1CS-style: `Σ_b eq(z,b)·(Â(b)·B̂(b) − Ĉ(b)) = 0`), the same MLE vocabulary Selvage already
  names as `[SC-reshape]`. That is the honest residual `[AIR-sumcheck-quadratic]` below.

**What is proved (no sorry):**

* `wireVec_read` / `addGateLin_iff` / `rootZero_iff` — the encoding is FAITHFUL: each linear
  constraint holds iff the corresponding gate holds / the root wire reads zero.
* `linearSystem_complete` — completeness: an ACCEPTED assignment (`accepts asg t`) has an aux
  extension (the forced one, `flatten_sound`) satisfying EVERY constraint of the linear system;
  `airSumcheck_batch_complete` renders it as the single γ-batched sum-claim, every γ
  (`list_as_single_sumcheck`).
* `air_violation_dichotomy` — soundness split: a REJECTED assignment (`¬ accepts asg t`)
  makes every aux valuation violate a MUL gate (the `[AIR-sumcheck-quadratic]` channel) or
  violate some LINEAR constraint of the encoded system. Composition of `flatten_constraint_iff`
  with the encoding iffs — this is where "the arithmetization's constraint is false" becomes
  "some sumcheck claim is false".
* `airSumcheck_sound` — **the keystone**: rejected assignment + mul gates undisturbed ⟹ some
  encoded constraint is violated AND Selvage's sumcheck on that claim accepts with probability
  `≤ v·d/|F|` — `sumcheck_retires_constraint` (hence `sumcheck_soundness`) CITED, not re-proved.
  `airSumcheck_sound_adaptive` is the same statement in the prefix-dependent protocol shape a
  real multi-round MLE prover inhabits (`adaptive_sumcheck_retires_constraint`, cited).
* `airSumcheck_retires_batch` — the whole linear system as ONE sumcheck: the γ round keeps a
  violating word alive for `≤ (t−1)/|F|` of γ (`batch_survives_prob_le`), and each surviving γ
  is caught by the single batched sumcheck except with `v·d/|F|` (`sumcheck_retires_batch`).
* `airSumcheck_honest_never_caught` — the honest side: the forced extension of an accepted
  assignment can never be falsely convicted (`satisfies_not_acceptsFalse`).

**Keystones (ZMod 7, `AirFlatten`'s `(x+2)·x` example — BUILT, computed):** the honest forced
wires satisfy every encoded constraint and the batched sum-claim; a wrong aux value violates
the add gate's constraint, and the retirement bound FIRES concretely (one round, cheating
prover `g̃ = X + 2` passing the round check, bound `1/7`) on a NONEMPTY accept event; the
rejecting assignment `x = 3` violates the root-pin constraint under the forced wires; and
`exMulCheat` shows an assignment satisfying EVERY linear constraint while cheating the mul
gate — the quadratic residual is REAL, not decorative.

**Residual — `[AIR-sumcheck-quadratic]` (prose, per the `[CRS-batch-sound]` precedent: no
placeholder Prop).** The MUL-gate channel: encoding `a·b = out` as a sum-claim needs the
multilinear extension of the wire word and the standard R1CS-to-sumcheck reshaping
(`Σ_b eq(z,b)·(Â(b)·B̂(b) − Ĉ(b)) = 0`, degree ≤ 3 per round variable) — exactly the MLE
realizer Selvage names `[SC-reshape]`. Until it lands, mul-gate violations are routed out
loud (the left disjunct of `air_violation_dichotomy`), never silently absorbed: the PROVED
scope is "linear subsystem (add gates + root pin) retired with the proven bound", and
`exMulCheat` witnesses that this scope is strictly smaller than full gate soundness.
-/
import Compiler.AirFlatten
import Selvage.SumcheckReduction

namespace Minidregg.Assurance

open Minidregg.Compiler Minidregg.Selvage Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Idx : Type} [Fintype Idx] [DecidableEq Idx]

/-! ## §1. The wire word — the gate system's variables as ONE finite domain.

`AirFlatten`'s gates read original variables (`Idx`) and aux wires (`ℕ`, allocated in
`[0, next)` by `flatten_scoped` when flattening starts at counter `0`). The sumcheck's claim
object lives over a FINITE domain, so the wire vector is indexed by `Idx ⊕ Fin N`. -/

/-- The finite wire domain: original variables ⊕ the first `N` aux wires. -/
abbrev WireIdx (Idx : Type) (N : ℕ) : Type := Idx ⊕ Fin N

/-- The wire word of an assignment pair: the one vector the sumcheck constrains. -/
def wireWord {N : ℕ} (asg : Idx → F) (auxv : ℕ → F) : WireIdx Idx N → F :=
  Sum.elim asg fun k => auxv k.val

/-- The coordinate (indicator) weight vector of a wire reference: constants contribute no
coordinate (they go to the constraint's target via `wireConst`); out-of-range aux wires give
`0` (never produced by `flatten` — `flatten_scoped`). -/
def wireVec (N : ℕ) : WireRef F Idx → (WireIdx Idx N → F)
  | .cnst _ => 0
  | .var i => fun j => if j = Sum.inl i then 1 else 0
  | .aux n => if h : n < N then (fun j => if j = Sum.inr ⟨n, h⟩ then 1 else 0) else 0

/-- The constant (affine) part of a wire reference's read. -/
def wireConst : WireRef F Idx → F
  | .cnst c => c
  | .var _ => 0
  | .aux _ => 0

omit [Fintype F] [DecidableEq F] in
/-- `⟨indicator pt, f⟩ = f pt` — reuse of `satisfies_evalConstraint_iff` (the `Z·eq` weight),
no sum re-computed. -/
theorem dotWt_indicator {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι) (f : ι → F) :
    dotWt (fun j => if j = pt then 1 else 0) f = f pt :=
  satisfies_evalConstraint_iff.mpr rfl

omit [Fintype F] [DecidableEq F] in
/-- Pairing linearity for differences, derived from the landed `dotWt_add_left` /
`dotWt_smul_left`. -/
theorem dotWt_sub_left {ι : Type} [Fintype ι] (a b f : ι → F) :
    dotWt (a - b) f = dotWt a f - dotWt b f := by
  rw [sub_eq_add_neg, ← neg_one_smul F b, dotWt_add_left, dotWt_smul_left]
  ring

omit [Fintype F] [DecidableEq F] in
/-- **The read decomposition**: for any in-scope wire reference, the pairing of its weight
vector against the wire word plus its constant part is exactly its `read` — the linear
encoding reads wires faithfully. -/
theorem wireVec_read {N : ℕ} (asg : Idx → F) (auxv : ℕ → F) {w : WireRef F Idx}
    (hw : w.auxIn 0 N) :
    dotWt (wireVec N w) (wireWord (N := N) asg auxv) + wireConst w = w.read asg auxv := by
  cases w with
  | cnst c =>
      show dotWt (0 : WireIdx Idx N → F) _ + c = c
      rw [dotWt_zero_left, zero_add]
  | var i =>
      show dotWt (fun j => if j = Sum.inl i then 1 else 0) (wireWord asg auxv) + 0 = asg i
      rw [dotWt_indicator, add_zero]
      rfl
  | aux n =>
      show dotWt (wireVec N (.aux n)) (wireWord asg auxv) + 0 = auxv n
      rw [add_zero]
      show dotWt (if h : n < N then (fun j => if j = Sum.inr ⟨n, h⟩ then 1 else 0) else 0)
        (wireWord asg auxv) = auxv n
      rw [dif_pos hw.2, dotWt_indicator]
      rfl

/-! ## §2. The gate constraints — ADD gates and the root pin are LINEAR claims.

An add gate `a + b = out` over the wire word `w` is `⟨vec(a)+vec(b)−vec(out), w⟩ = −(κa+κb)`
(κ the constant parts): one `Selvage.LinearConstraint`, hence — by the landed, definitional
`constraint_as_sumcheck` — one sumcheck sum-claim. The root pin `root = 0` is
`⟨vec(root), w⟩ = −κ`. MUL gates are degree-2 in `w`: NOT in this vocabulary; they are the
`[AIR-sumcheck-quadratic]` residual, routed explicitly by `air_violation_dichotomy`. -/

/-- The linear constraint of an ADD gate `a + b = out`: weight `vec(a)+vec(b)−vec(out)`,
target `−(κa+κb)`. (Meaningful only for `g.op = .add` — `addGateLin_iff` carries that
hypothesis; `linearSystem` only ever applies it to add gates.) -/
def addGateLin (N : ℕ) (g : Gate F Idx) : LinearConstraint (WireIdx Idx N) F where
  wt := wireVec N g.a + wireVec N g.b - wireVec N (.aux g.out)
  target := -(wireConst g.a + wireConst g.b)

/-- The root-pin constraint `w = 0` for a wire reference: weight `vec(w)`, target `−κ(w)`. -/
def rootZero (N : ℕ) (w : WireRef F Idx) : LinearConstraint (WireIdx Idx N) F where
  wt := wireVec N w
  target := -(wireConst w)

omit [Fintype F] [DecidableEq F] in
/-- **The add-gate encoding is FAITHFUL**: for an in-scope add gate, satisfaction of its
linear constraint by the wire word IS `Gate.holds`. -/
theorem addGateLin_iff {N : ℕ} {g : Gate F Idx} (hop : g.op = GateOp.add)
    (ha : g.a.auxIn 0 N) (hb : g.b.auxIn 0 N) (hout : g.out < N)
    (asg : Idx → F) (auxv : ℕ → F) :
    Satisfies (wireWord (N := N) asg auxv) (addGateLin N g) ↔ g.holds asg auxv := by
  have hra := wireVec_read (N := N) asg auxv ha
  have hrb := wireVec_read (N := N) asg auxv hb
  have hro := wireVec_read (N := N) asg auxv
    (w := .aux g.out) ⟨Nat.zero_le _, hout⟩
  rw [WireRef.read_aux,
    show wireConst (WireRef.aux g.out : WireRef F Idx) = (0 : F) from rfl, add_zero] at hro
  have hgoal : Satisfies (wireWord (N := N) asg auxv) (addGateLin N g)
      ↔ g.a.read asg auxv + g.b.read asg auxv = auxv g.out := by
    show dotWt (wireVec N g.a + wireVec N g.b - wireVec N (.aux g.out))
        (wireWord asg auxv) = -(wireConst g.a + wireConst g.b) ↔ _
    rw [dotWt_sub_left, dotWt_add_left]
    constructor
    · intro h
      linear_combination h - hra - hrb + hro
    · intro h
      linear_combination h + hra + hrb - hro
  rw [hgoal]
  unfold Gate.holds
  rw [hop]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- **The root-pin encoding is FAITHFUL**: satisfaction of `rootZero` IS "the wire reads 0". -/
theorem rootZero_iff {N : ℕ} {w : WireRef F Idx} (hw : w.auxIn 0 N)
    (asg : Idx → F) (auxv : ℕ → F) :
    Satisfies (wireWord (N := N) asg auxv) (rootZero N w) ↔ w.read asg auxv = 0 := by
  have hr := wireVec_read (N := N) asg auxv hw
  show dotWt (wireVec N w) (wireWord asg auxv) = -(wireConst w) ↔ _
  constructor
  · intro h
    linear_combination h - hr
  · intro h
    linear_combination h + hr

/-! ## §3. The linear system of a flattened term, and the soundness dichotomy.

`linearSystem N root gs` collects the LINEAR face of the gate system: the root pin plus one
constraint per ADD gate. Completeness (`linearSystem_complete`): an accepted assignment's
forced extension satisfies all of it. Soundness (`air_violation_dichotomy`): a rejected
assignment violates a MUL gate — the `[AIR-sumcheck-quadratic]` channel, named out loud — or
some constraint of this system, under EVERY aux valuation. -/

/-- The add gates of a gate list (mul gates go to the quadratic residual channel). -/
def addGates (gs : List (Gate F Idx)) : List (Gate F Idx) :=
  gs.filter fun g => decide (g.op = GateOp.add)

omit [Field F] [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] in
theorem mem_addGates {gs : List (Gate F Idx)} {g : Gate F Idx} :
    g ∈ addGates gs ↔ g ∈ gs ∧ g.op = GateOp.add := by
  simp [addGates]

/-- **The linear face of the gate system**: the root pin + the add gates' constraints — each
entry a `Selvage.LinearConstraint`, i.e. (by `constraint_as_sumcheck`) a sumcheck sum-claim. -/
def linearSystem (N : ℕ) (root : WireRef F Idx) (gs : List (Gate F Idx)) :
    List (LinearConstraint (WireIdx Idx N) F) :=
  rootZero N root :: (addGates gs).map (addGateLin N)

/-- The linear system of the FLATTENED term, at the scope `flatten` itself allocates. -/
def flatLinearSystem (t : Term (AirSig F Idx)) :
    List (LinearConstraint (WireIdx Idx (flatten t 0).next) F) :=
  linearSystem (flatten t 0).next (flatten t 0).out (flatten t 0).gates

omit [Fintype F] [DecidableEq F] in
/-- **Completeness**: an ACCEPTED assignment (`accepts asg t`, i.e. `eval asg t = 0`) has an
aux extension — the forced one, via `flatten_constraint_iff` / `flatten_sound` — whose wire
word satisfies EVERY constraint of the linear system. -/
theorem linearSystem_complete (asg : Idx → F) (t : Term (AirSig F Idx))
    (hacc : accepts asg t) :
    ∃ auxv : ℕ → F, ∀ c ∈ flatLinearSystem t,
      Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c := by
  obtain ⟨auxv, hgates, hroot⟩ := (flatten_constraint_iff asg t 0).mpr hacc
  obtain ⟨-, hout, hscoped⟩ := flatten_scoped t 0
  refine ⟨auxv, fun c hc => ?_⟩
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact (rootZero_iff hout asg auxv).mpr hroot
  · obtain ⟨g, hgmem, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨hg, hop⟩ := mem_addGates.mp hgmem
    obtain ⟨ha, hb, -, houtlt⟩ := hscoped g hg
    exact (addGateLin_iff hop
      (WireRef.auxIn_mono le_rfl houtlt.le ha)
      (WireRef.auxIn_mono le_rfl houtlt.le hb) houtlt asg auxv).mpr (hgates g hg)

omit [Fintype F] [DecidableEq F] in
/-- **The soundness dichotomy — where a false arithmetization claim goes.** If the circuit
REJECTS the assignment (`¬ accepts asg t` — equivalently, by `accepts_iff_semHolds`, the
executor relation fails), then EVERY aux valuation either violates a MUL gate (the
`[AIR-sumcheck-quadratic]` residual channel, named, never silently absorbed) or violates some
LINEAR constraint of the encoded system — a false sumcheck sum-claim, which §4 retires with
Selvage's proven bound. Composition of `flatten_constraint_iff` with the §2 encoding iffs. -/
theorem air_violation_dichotomy (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F) :
    (∃ g ∈ (flatten t 0).gates, g.op = GateOp.mul ∧ ¬ g.holds asg auxv)
    ∨ (∃ c ∈ flatLinearSystem t,
        ¬ Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hmul, hlin⟩ := hcon
  apply hrej
  rw [← flatten_constraint_iff asg t 0]
  obtain ⟨-, hout, hscoped⟩ := flatten_scoped t 0
  refine ⟨auxv, fun g hg => ?_, ?_⟩
  · cases hop : g.op with
    | mul => exact hmul g hg hop
    | add =>
      obtain ⟨ha, hb, -, houtlt⟩ := hscoped g hg
      refine (addGateLin_iff hop
        (WireRef.auxIn_mono le_rfl houtlt.le ha)
        (WireRef.auxIn_mono le_rfl houtlt.le hb) houtlt asg auxv).mp ?_
      exact hlin _ (List.mem_cons_of_mem _
        (List.mem_map_of_mem (mem_addGates.mpr ⟨hg, hop⟩)))
  · exact (rootZero_iff hout asg auxv).mp (hlin _ (List.mem_cons_self ..))

/-! ## §4. The retirement — Selvage's PROVEN sumcheck catches the violation.

Everything below CITES `Selvage/SumcheckReduction` (`sumcheck_retires_constraint`,
`batch_survives_prob_le`, `sumcheck_retires_batch`, `satisfies_not_acceptsFalse`,
`list_as_single_sumcheck`) — which in turn cites `Selvage/Sumcheck`'s proved
`sumcheck_soundness`. No probability, no root counting, no union bound is re-derived here;
the bound `v·d/|F|` is Selvage's, quoted verbatim, and covers the LINEAR face of the gate
system (add gates + root pin) — mul gates are `[AIR-sumcheck-quadratic]`. -/

/-- **`airSumcheck_sound` — [AIR-sumcheck], the linear face, closed.** A wire assignment the
circuit REJECTS, whose aux valuation leaves every MUL gate intact (otherwise the violation
lives in the named `[AIR-sumcheck-quadratic]` channel), violates SOME constraint of the
encoded linear system — and Selvage's sumcheck run on that constraint's sum-claim (claimed total
`c.target`, truth chain anchored at the actual pairing) accepts with probability at most
`v·d/|F|`, for every prover and every degree-`≤ d` honest chain. The bound is
`sumcheck_retires_constraint` = `sumcheck_soundness`, cited; the AIR content is the
dichotomy + the faithful encoding. -/
theorem airSumcheck_sound {v d : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (hmul : ∀ g ∈ (flatten t 0).gates, g.op = GateOp.mul → g.holds asg auxv) :
    ∃ c ∈ flatLinearSystem t,
      ¬ Satisfies (wireWord (N := (flatten t 0).next) asg auxv) c ∧
      ∀ (prover honest : ℕ → Polynomial F),
        (∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ)) →
        (∀ (r : Fin v → F), ∀ i, i < v →
          (honest i).eval 0 + (honest i).eval 1
            = scChain (trueSum c (wireWord (N := (flatten t 0).next) asg auxv))
                honest (chalOf r) i) →
        uniformProb (Fin v → F)
          (SumcheckAccepts prover honest c.target
            (trueSum c (wireWord (N := (flatten t 0).next) asg auxv)))
          ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  rcases air_violation_dichotomy asg t hrej auxv with ⟨g, hg, hop, hviol⟩ | ⟨c, hc, hviol⟩
  · exact absurd (hmul g hg hop) hviol
  · exact ⟨c, hc, hviol, fun prover honest hPD hHD hH =>
      sumcheck_retires_constraint hviol hPD hHD hH⟩

/-- **The adaptive form** — the protocol shape a real multi-round honest prover (the MLE
round polynomials of `[SC-reshape]`) inhabits: round polynomials drawn from the challenge
prefix. Same dichotomy, same violated claim; the bound is
`adaptive_sumcheck_retires_constraint` (Selvage's packaging of its own `sumcheck_reduction` +
discharged `adaptiveUnionBound_holds`), cited. -/
theorem airSumcheck_sound_adaptive {v d : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (hmul : ∀ g ∈ (flatten t 0).gates, g.op = GateOp.mul → g.holds asg auxv) :
    ∃ c ∈ flatLinearSystem t,
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
          ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  rcases air_violation_dichotomy asg t hrej auxv with ⟨g, hg, hop, hviol⟩ | ⟨c, hc, hviol⟩
  · exact absurd (hmul g hg hop) hviol
  · exact ⟨c, hc, hviol, fun prover honest hpm hhm hPD hHD hH =>
      adaptive_sumcheck_retires_constraint hviol hpm hhm hPD hHD hH⟩

/-- **The γ round (stage 1 of the batched retirement).** The rejected assignment's violated
linear system survives γ-batching for at most `(t−1)/|F|` of uniform γ —
`batch_survives_prob_le`, fed by the dichotomy. -/
theorem airSumcheck_gamma_round (asg : Idx → F) (t : Term (AirSig F Idx))
    (hrej : ¬ accepts asg t) (auxv : ℕ → F)
    (hmul : ∀ g ∈ (flatten t 0).gates, g.op = GateOp.mul → g.holds asg auxv) :
    uniformProb F (fun γ => Satisfies (wireWord (N := (flatten t 0).next) asg auxv)
        (batchConstraint γ (flatLinearSystem t)))
      ≤ (((flatLinearSystem t).length - 1 : ℕ) : ℝ) / Fintype.card F := by
  rcases air_violation_dichotomy asg t hrej auxv with ⟨g, hg, hop, hviol⟩ | hviol
  · exact absurd (hmul g hg hop) hviol
  · exact batch_survives_prob_le hviol

/-- **Stage 2: ONE sumcheck retires the whole linear face.** At any γ where the batch stays
violated (all but `≤ t−1` of them, stage 1), the single sumcheck on the γ-batched sum-claim
catches the assignment except with probability `v·d/|F|` — `sumcheck_retires_batch`, cited.
Together the two stages are the additive RBR ledger entries `(t−1)/|F| + v·d/|F|` for the
whole encoded gate list. -/
theorem airSumcheck_retires_batch {v d : ℕ} {prover honest : ℕ → Polynomial F}
    (asg : Idx → F) (t : Term (AirSig F Idx)) (auxv : ℕ → F) {γ : F}
    (hγ : ¬ Satisfies (wireWord (N := (flatten t 0).next) asg auxv)
      (batchConstraint γ (flatLinearSystem t)))
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1
        = scChain (trueSum (batchConstraint γ (flatLinearSystem t))
            (wireWord (N := (flatten t 0).next) asg auxv)) honest (chalOf r) i) :
    uniformProb (Fin v → F)
      (SumcheckAccepts prover honest (batchConstraint γ (flatLinearSystem t)).target
        (trueSum (batchConstraint γ (flatLinearSystem t))
          (wireWord (N := (flatten t 0).next) asg auxv)))
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  sumcheck_retires_batch hγ hProverDeg hHonestDeg hHonest

omit [Fintype F] [DecidableEq F] in
/-- **The honest side**: an ACCEPTED assignment's forced wire word satisfies every encoded
claim, so no sumcheck run on any of them can be an `AcceptsFalse` event — the honest prover
is never falsely convicted (`satisfies_not_acceptsFalse`, cited). -/
theorem airSumcheck_honest_never_caught {v : ℕ} (asg : Idx → F) (t : Term (AirSig F Idx))
    (hacc : accepts asg t) :
    ∃ auxv : ℕ → F, ∀ c ∈ flatLinearSystem t,
      ∀ (prover honest : ℕ → Polynomial F) (r : Fin v → F),
        ¬ AcceptsFalse prover honest c.target
          (trueSum c (wireWord (N := (flatten t 0).next) asg auxv)) r := by
  obtain ⟨auxv, hsat⟩ := linearSystem_complete asg t hacc
  exact ⟨auxv, fun c hc prover honest r =>
    satisfies_not_acceptsFalse (hsat c hc) r⟩

omit [Fintype F] [DecidableEq F] in
/-- **Batched completeness**: the accepted assignment's forced wire word renders the WHOLE
linear system as ONE true γ-batched sum-claim, for every γ (`list_as_single_sumcheck`,
cited) — the claim object the decider's single sumcheck walks. -/
theorem airSumcheck_batch_complete (asg : Idx → F) (t : Term (AirSig F Idx))
    (hacc : accepts asg t) :
    ∃ auxv : ℕ → F, ∀ γ : F,
      ∑ i, constraintSummand (batchConstraint γ (flatLinearSystem t))
          (wireWord (N := (flatten t 0).next) asg auxv) i
        = (batchConstraint γ (flatLinearSystem t)).target := by
  obtain ⟨auxv, hsat⟩ := linearSystem_complete asg t hacc
  exact ⟨auxv, fun γ => list_as_single_sumcheck γ hsat⟩

/-! ## §5. Keystones — BUILT, over `ZMod 7`, on `AirFlatten`'s `(x+2)·x` example.

`exFlat` flattens to gates `[x + 2 = aux₀, aux₀ · x = aux₁]`, root `aux₁`, two allocations.
The linear system: the root pin + the add gate's constraint (the mul gate routed to the
`[AIR-sumcheck-quadratic]` channel). Everything computes on the actual data. -/

namespace ASExample

/-- The add gate of `exFlat`'s flattening: `x + 2 = aux₀`. -/
def exAddGate : Gate (ZMod 7) Unit := ⟨.add, .var (), .cnst 2, 0⟩

/-- *Computes*: the linear system is the root pin + ONE add-gate constraint — the mul gate
is NOT silently linearized; it sits in the named residual channel. -/
example : (flatLinearSystem exFlat).length = 2 := by decide

/-- *Computes, on the nose*: the linear system IS the root pin on `aux₁` plus the add gate's
constraint — definitionally. -/
example : flatLinearSystem exFlat
    = [rootZero 2 (.aux 1), addGateLin 2 exAddGate] := rfl

/-- **SATISFIABLE, BUILT**: the honest forced wire word (`x = 3`, `aux₀ = 5`, `aux₁ = 1`)
satisfies the add-gate constraint of the linear system — the encoding accepts the honest
wires. (The root PIN is violated at `x = 3` since the term evals to `1 ≠ 0` — exactly
right: see the teeth below.) -/
example : Satisfies (wireWord (N := 2) exAsg exForced) (addGateLin 2 exAddGate) := by
  decide

/-- **The sum-claim rendering computes**: the add gate, γ-batched with the root pin at
`γ = 3`, rendered AS the single sumcheck sum-claim object — the claimed total is the batched
target, and the TRUE total is the actual pairing (here they differ: `x = 3` is rejected). -/
example : trueSum (batchConstraint 3 (flatLinearSystem exFlat))
    (wireWord (N := 2) exAsg exForced)
    = dotWt (batchConstraint 3 (flatLinearSystem exFlat)).wt
        (wireWord (N := 2) exAsg exForced) := trueSum_eq_dotWt _ _

/-- **ROOT-PIN TEETH**: at the rejecting `x = 3` (the expression evals to `1 ≠ 0`), the
FORCED wires satisfy every gate — but violate the root-pin constraint: the false circuit
claim IS a false linear (sum-)claim. -/
example : ¬ Satisfies (wireWord (N := 2) exAsg exForced)
    (rootZero 2 ((flatten exFlat 0).out)) := by decide

/-- The circuit rejects `x = 3` (evals to `1`). -/
theorem exFlat_rejects : ¬ accepts exAsg exFlat := by
  show ¬ (Compiler.eval exAsg exFlat = 0)
  decide

/-- The mul gate HOLDS under the forced wires (`5 · 3 = 1` over `ZMod 7`) — inhabits the
`hmul` premise of `airSumcheck_sound` (the violation is NOT hiding in the quadratic
channel here). -/
theorem exForced_mul_intact :
    ∀ g ∈ (flatten exFlat 0).gates, g.op = GateOp.mul → g.holds exAsg exForced := by
  intro g hg hop
  cases hg with
  | head => exact absurd hop (by decide)
  | tail _ hg' =>
    cases hg' with
    | head => show (5 * 3 : ZMod 7) = 1; decide
    | tail _ hg'' => exact nomatch hg''

/-- **The keystone FIRES on real data**: rejected assignment + mul gates intact ⟹ some
encoded sum-claim is violated and Selvage's proven bound applies to it — every premise of
`airSumcheck_sound` discharged concretely. -/
example := airSumcheck_sound (v := 1) (d := 1) exAsg exFlat exFlat_rejects
  exForced exForced_mul_intact

/-! ### The retirement bound fires concretely — add-gate teeth, `AirFlatten`'s wrong wire. -/

/-- The WRONG aux valuation (wire 0 ↦ 4; forced value 5) — `AirFlatten`'s teeth data. -/
def exWrong : ℕ → ZMod 7 := fun n => if n = 0 then 4 else 1

/-- The wrong wire VIOLATES the add gate's linear constraint (claimed `−2 = 5`, true pairing
`3 − 4 = 6`): the gate violation IS a false sum-claim. -/
theorem exWrong_violates :
    ¬ Satisfies (wireWord (N := 2) exAsg exWrong) (addGateLin 2 exAddGate) := by decide

/-- The violated claim's TRUE total, computed: `⟨wt, w⟩ = 3 − 4 = 6` (claimed: `5`). -/
theorem exWrong_trueSum :
    trueSum (addGateLin 2 exAddGate) (wireWord (N := 2) exAsg exWrong) = 6 := by decide

/-- **TEETH — the retirement bound FIRES.** One-round sumcheck on the violated add-gate
claim: the cheating prover sends `g̃ = X + 2` (passing the round check
`g̃(0) + g̃(1) = 2 + 3 = 5 =` the claimed target), honest chain `g = 3` (boolean sum
`3 + 3 = 6 =` the true total); `sumcheck_retires_constraint` delivers `Pr[accept] ≤ 1/7`
with every hypothesis discharged concretely. -/
theorem exWrong_caught :
    uniformProb (Fin 1 → ZMod 7)
      (SumcheckAccepts (fun _ => (X + C 2 : Polynomial (ZMod 7))) (fun _ => C 3)
        (addGateLin 2 exAddGate).target
        (trueSum (addGateLin 2 exAddGate) (wireWord (N := 2) exAsg exWrong)))
      ≤ 1 / 7 := by
  have h := sumcheck_retires_constraint (v := 1) (d := 1)
    (prover := fun _ => (X + C 2 : Polynomial (ZMod 7))) (honest := fun _ => C 3)
    (f := wireWord (N := 2) exAsg exWrong) (c := addGateLin 2 exAddGate)
    exWrong_violates
    (fun i _ => by rw [Polynomial.degree_X_add_C]; decide)
    (fun i _ => by
      rw [Polynomial.degree_C (by decide : (3 : ZMod 7) ≠ 0)]; decide)
    (fun r i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [scChain, Polynomial.eval_C]
      decide)
  rw [ZMod.card] at h
  norm_num at h
  exact h

/-- The caught-event is NONEMPTY: at challenge `r = 1` the cheat IS accepted
(`g̃(1) = 3 = g(1)` — the lie is laundered), so the `1/7` bound constrains a real event,
not a vacuum. -/
theorem exWrong_accept_witness :
    SumcheckAccepts (v := 1) (fun _ => (X + C 2 : Polynomial (ZMod 7))) (fun _ => C 3)
      (addGateLin 2 exAddGate).target
      (trueSum (addGateLin 2 exAddGate) (wireWord (N := 2) exAsg exWrong))
      (fun _ => 1) := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [scChain, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    decide
  · simp only [scChain, chalOf]
    norm_num

/-- Batch-teeth premise inhabited: at `γ = 3` the wrong wires violate the γ-batched
system — `airSumcheck_retires_batch`'s hypothesis holds on real data. -/
example : ¬ Satisfies (wireWord (N := 2) exAsg exWrong)
    (batchConstraint 3 (flatLinearSystem exFlat)) := by decide

/-! ### Honest scope, witnessed: the quadratic residual is REAL. -/

/-- A MUL-cheating valuation: `aux₀ = 5` (add gate honest), `aux₁ = 0` (mul gate CHEATED —
`5·3 = 1 ≠ 0` — precisely to fake the root pin). -/
def exMulCheat : ℕ → ZMod 7 := fun n => if n = 0 then 5 else 0

/-- **`[AIR-sumcheck-quadratic]` is REAL, not decorative**: `exMulCheat` satisfies EVERY
constraint of the linear system (root pin included!) while violating the mul gate — the
linear face alone does NOT carry full gate soundness; the degree-2 channel is load-bearing.
This is the honest-scope witness for the residual. -/
theorem exMulCheat_shows_residual_real :
    (∀ c ∈ flatLinearSystem exFlat,
      Satisfies (wireWord (N := 2) exAsg exMulCheat) c)
    ∧ ¬ Gate.holds exAsg exMulCheat ⟨.mul, .aux 0, .var (), 1⟩ := by
  constructor
  · decide
  · show ¬ ((5 * 3 : ZMod 7) = 0)
    decide

end ASExample

end Minidregg.Assurance
