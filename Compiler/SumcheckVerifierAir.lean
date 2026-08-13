/-
# `Compiler/SumcheckVerifierAir.lean` — the sumcheck VERIFIER arithmetized: the first
recursive-verifier gadget

**Substrate, said out loud: this is Lean-AUTHORED AIR.** Every constraint below is a
`Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`), read through the
one fold (`eval = fold evalAlg`), composed as a `ConstraintSystem`; its meaning comes from
rung 1's initiality keystone (`accepts_iff_semHolds`, lifted by
`systemAccepts_iff_systemSemHolds`). NO check is hand-authored outside the DSL — no Rust, no
bespoke `air_accepts`, no parallel executor.

## What is arithmetized

The sumcheck VERIFIER (not the prover): given a transcript laid out on wires —

* `claimW` — the claimed sum `H`;
* `g0 i` / `g1 i` — round `i`'s polynomial as its two evaluations `gᵢ(0)`, `gᵢ(1)`
  (the degree-1 values representation: the wire pair IS the round message, so the degree
  bound `d = 1` is enforced by REPRESENTATION — there is no wire on which a higher-degree
  message could ride; the degree-2 rounds a product sumcheck needs are the standing
  `[AIR-sumcheck-quadratic]` face, three evaluations per round, not coined here);
* `chal i` — the challenge `rᵢ`;
* `finalW` — the final oracle value (in the full recursion: the Merkle-opened `f̂(r)`) —

the AIR asserts exactly the verifier's checks:

1. **round 0**: `g₀(0) + g₀(1) = H`;
2. **round k+1**: `g_{k+1}(0) + g_{k+1}(1) = gₖ(rₖ)`, where `gₖ(rₖ)` is the two-point
   interpolation `(1 − rₖ)·gₖ(0) + rₖ·gₖ(1)` — exact for degree ≤ 1;
3. **final**: `finalW = g_{n−1}(r_{n−1})` — the last fold value equals the oracle wire.

## The Selvage correspondence (prose, boundary-honest)

`Compiler` may not import `Selvage` (`Theory`-boundary law), so the correspondence is stated
here at matching shape, theorem-for-theorem, and the cross-boundary lemma is the named
residual `[RECURSE-sumcheck-bridge]`:

* `chainVal` below IS `Selvage.scChain` in values form: `scChain base poly chal 0 = base` and
  `scChain … (i+1) = (poly i).eval (chal i)`; for a degree-≤1 round polynomial the
  evaluation is the interpolation of its values at 0 and 1 (`Selvage.roundSum_affine` /
  `roundPoly_eval` are exactly this shape; `interp_eq_of_affine` below is the in-boundary
  bridge at that resolution).
* Check (1) is `Selvage.roundSum_zero`'s shape (`g₀(0)+g₀(1) =` the claimed total), check (2)
  is `Selvage.roundSum_succ` (`g_{k+1}(0)+g_{k+1}(1) = gₖ(rₖ)`), check (3) is
  `Selvage.roundSum_last` / `scChain_mleHonest_final` (the last fold IS the full evaluation
  `f̂(r)`, compared against the oracle).
* `SumcheckVerifierAccepts` below is `Selvage.SumcheckAccepts`' check-conjunction on the same
  transcript (the round checks against the claim chain + the final comparison), minus
  nothing: the arithmetized verifier accepts iff the Lean sumcheck verifier would accept
  the same values-form transcript.

`[RECURSE-sumcheck-bridge]` — the machine-checked form of that last bullet
(`systemAccepts asg (sumcheckVerifierGadget …) ↔ Selvage.SumcheckAccepts …` through the
values/`Polynomial` representation change), statable only in a layer importing both
(Assurance). Everything on THIS side of the boundary is proved; the residual is the
cross-boundary restatement, not a gap in the gadget's meaning.

## The recursion point — `[RECURSE-verifier]`

The gadget is a `ConstraintSystem`, so the WHOLE emit path applies to it verbatim:
`flattenSystem`/`emit` produce a first-order `ConstraintDescriptor` whose satisfiability is
`systemAccepts` (`emit_accepts_iff`, instantiated on this gadget in §6). Therefore **"the
sumcheck verifier accepted this transcript" is itself a Selvage-arithmetized statement** — a
proof OF that statement is a proof that a proof verified: the recursion apex. The full
recursive verifier `[RECURSE-verifier]` is the composition, all on this rung: THIS gadget
(its first component) + challenge wires BOUND to Fiat–Shamir transcript hashes (AirHash's
`permGadget`) + `finalW` bound to a Merkle-opened oracle value (AirMembership's gadget) +
the FRI-query gadget = the whole light-client check as ONE emitted `ConstraintSystem`.
Here the challenges and `finalW` are free input wires; the composition binds them.

## Statement-first (ATLAS fields)

* `SumcheckVerifierAccepts` — the verifier's checks as a `Prop`, stated BEFORE the gadget.
  Satisfiable: an honest transcript (real MLE round values) inhabits it (§5, decided).
  Teeth: tampered transcripts are rejected, with per-check attribution (§5, decided).
  Premise-inhabitation: the quantified keystones (`↔ c = 1` forms) show acceptance pins
  wires, not vacuously.
* `sumcheckVerifier_correct` — the keystone iff: the AIR accepts iff the verifier's checks
  hold. Derived from `accepts_iff_semHolds` + the §2 eval lemmas; no bespoke soundness
  argument, no new induction.
-/
import Compiler.Emit

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {n : ℕ}

/-! ## §1. The semantic spec, statement-first — the verifier's checks as a `Prop`. -/

/-- Two-point interpolation: the value at `r` of the degree-≤1 polynomial with values
`a` at 0 and `b` at 1 — `(1 − r)·a + r·b`. This is how the arithmetized verifier computes
`gₖ(rₖ)` from the round message `(gₖ(0), gₖ(1))`; exact for degree ≤ 1
(`interp_eq_of_affine`), and the degree bound is enforced by the values REPRESENTATION. -/
def interp (r a b : F) : F := (1 - r) * a + r * b

/-- **The claim chain, values form** — Selvage's `scChain` with the round-polynomial
evaluation rendered as the interpolation: `claim` at 0, `gₖ(rₖ) = interp rₖ gₖ(0) gₖ(1)`
at `k+1` (junk `claim` past the horizon, never queried in range — `chalOf`'s pattern). -/
def chainVal (claim : F) (g0v g1v chalv : Fin n → F) : ℕ → F
  | 0 => claim
  | k + 1 =>
    if h : k < n then interp (chalv ⟨k, h⟩) (g0v ⟨k, h⟩) (g1v ⟨k, h⟩) else claim

/-- **The sumcheck verifier's acceptance, statement-first.** Every round check
`gᵢ(0) + gᵢ(1) = chainᵢ` holds (round 0 against the claim — `roundSum_zero`'s shape;
round `k+1` against the previous fold `gₖ(rₖ)` — `roundSum_succ`'s shape) AND the final
oracle value equals the last fold (`roundSum_last`'s shape). This is
`Selvage.SumcheckAccepts` on the values-form transcript; the machine-checked identification
is `[RECURSE-sumcheck-bridge]`. -/
def SumcheckVerifierAccepts (claim final : F) (g0v g1v chalv : Fin n → F) : Prop :=
  (∀ i : Fin n, g0v i + g1v i = chainVal claim g0v g1v chalv i.val)
    ∧ final = chainVal claim g0v g1v chalv n

/-- **The degree-1 bridge (in-boundary form).** For any round function `g` that is affine
in Selvage's `AffineInCoord`/`roundSum_affine` shape (`g t = (1−t)·g 0 + t·g 1`), the
gadget's fold value `interp r (g 0) (g 1)` IS `g r` — the arithmetized chain computes the
real `gₖ(rₖ)` exactly on degree-≤1 round polynomials. The `Polynomial F` restatement is
`[RECURSE-sumcheck-bridge]`. -/
theorem interp_eq_of_affine (g : F → F)
    (haff : ∀ t, g t = (1 - t) * g 0 + t * g 1) (r : F) :
    interp r (g 0) (g 1) = g r :=
  (haff r).symm

/-! ## §2. The checks as DSL terms — every constraint out of the compiler surface. -/

/-- The interpolation as a DSL term: `(1 + (−1)·r)·a + r·b`. -/
def interpTerm (r a b : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  add' (mul' (add' (cst 1) (mul' (cst (-1)) r)) a) (mul' r b)

@[simp] theorem eval_interpTerm (asg : Idx → F) (r a b : Term (AirSig F Idx)) :
    eval asg (interpTerm r a b) = interp (eval asg r) (eval asg a) (eval asg b) := by
  simp only [interpTerm, eval_add', eval_mul', eval_cst, interp]
  ring

/-- The claim chain as a DSL term: `vr claimW` at 0, the interpolation of round `k`'s
wires at `k+1` — `chainVal`'s syntax, mirrored constructor-for-constructor. -/
def chainTerm (claimW : Idx) (g0 g1 chal : Fin n → Idx) : ℕ → Term (AirSig F Idx)
  | 0 => vr claimW
  | k + 1 =>
    if h : k < n then
      interpTerm (vr (chal ⟨k, h⟩)) (vr (g0 ⟨k, h⟩)) (vr (g1 ⟨k, h⟩))
    else vr claimW

/-- The circuit reads `chainTerm` as `chainVal` — the chain's two renderings agree. -/
theorem eval_chainTerm (asg : Idx → F) (claimW : Idx) (g0 g1 chal : Fin n → Idx) :
    ∀ k : ℕ, eval asg (chainTerm claimW g0 g1 chal k)
      = chainVal (asg claimW) (fun j => asg (g0 j)) (fun j => asg (g1 j))
          (fun j => asg (chal j)) k
  | 0 => rfl
  | k + 1 => by
    simp only [chainTerm, chainVal]
    by_cases h : k < n
    · rw [dif_pos h, dif_pos h, eval_interpTerm, eval_vr, eval_vr, eval_vr]
    · rw [dif_neg h, dif_neg h, eval_vr]

/-- Round `i`'s check as a DSL assertion: `gᵢ(0) + gᵢ(1) − chainᵢ ≐ 0`. -/
def roundCheckTerm (claimW : Idx) (g0 g1 chal : Fin n → Idx) (i : Fin n) :
    Term (AirSig F Idx) :=
  add' (add' (vr (g0 i)) (vr (g1 i)))
    (mul' (cst (-1)) (chainTerm claimW g0 g1 chal i.val))

/-- The round-check assertion MEANS the round check: it accepts iff
`gᵢ(0) + gᵢ(1) = chainᵢ`. -/
theorem roundCheckTerm_correct (asg : Idx → F) (claimW : Idx)
    (g0 g1 chal : Fin n → Idx) (i : Fin n) :
    accepts asg (roundCheckTerm claimW g0 g1 chal i) ↔
      asg (g0 i) + asg (g1 i)
        = chainVal (asg claimW) (fun j => asg (g0 j)) (fun j => asg (g1 j))
            (fun j => asg (chal j)) i.val := by
  unfold accepts roundCheckTerm
  rw [eval_add', eval_add', eval_mul', eval_cst, eval_vr, eval_vr, eval_chainTerm,
    neg_one_mul, add_neg_eq_zero]

/-- The final oracle check as a DSL assertion: `finalW − chainₙ ≐ 0` — the oracle wire
carries the last fold value `g_{n−1}(r_{n−1})`. -/
def finalCheckTerm (claimW finalW : Idx) (g0 g1 chal : Fin n → Idx) :
    Term (AirSig F Idx) :=
  add' (vr finalW) (mul' (cst (-1)) (chainTerm claimW g0 g1 chal n))

/-- The final assertion MEANS the final check. -/
theorem finalCheckTerm_correct (asg : Idx → F) (claimW finalW : Idx)
    (g0 g1 chal : Fin n → Idx) :
    accepts asg (finalCheckTerm claimW finalW g0 g1 chal) ↔
      asg finalW
        = chainVal (asg claimW) (fun j => asg (g0 j)) (fun j => asg (g1 j))
            (fun j => asg (chal j)) n := by
  unfold accepts finalCheckTerm
  rw [eval_add', eval_mul', eval_cst, eval_vr, eval_chainTerm,
    neg_one_mul, add_neg_eq_zero]

/-! ## §3. The gadget and its keystone iff. -/

/-- **The sumcheck-verifier gadget** — the first recursive-verifier component: `n` round
checks plus the final oracle check, all DSL terms, composed as a system. A
`ConstraintSystem`, so the emit path (`flattenSystem`/`emit`) applies verbatim (§6). -/
def sumcheckVerifierGadget (claimW finalW : Idx) (g0 g1 chal : Fin n → Idx) :
    ConstraintSystem F Idx :=
  ((List.finRange n).map fun i => roundCheckTerm claimW g0 g1 chal i)
    ++ [finalCheckTerm claimW finalW g0 g1 chal]

/-- **The keystone iff — the AIR accepts iff the sumcheck verifier accepts.** The system
accepts `asg` iff every round check and the final oracle check hold on the wire values —
`SumcheckVerifierAccepts`, the statement-first spec. Derived: per-term correctness (§2)
under the list membership split; the semantic transfer is rung 1's initiality. -/
theorem sumcheckVerifier_correct (asg : Idx → F) (claimW finalW : Idx)
    (g0 g1 chal : Fin n → Idx) :
    systemAccepts asg (sumcheckVerifierGadget claimW finalW g0 g1 chal) ↔
      SumcheckVerifierAccepts (asg claimW) (asg finalW)
        (fun i => asg (g0 i)) (fun i => asg (g1 i)) (fun i => asg (chal i)) := by
  unfold systemAccepts sumcheckVerifierGadget SumcheckVerifierAccepts
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · exact (roundCheckTerm_correct asg claimW g0 g1 chal i).mp
        (h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
    · exact (finalCheckTerm_correct asg claimW finalW g0 g1 chal).mp
        (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · rintro ⟨hround, hfinal⟩ t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht'
      exact (roundCheckTerm_correct asg claimW g0 g1 chal i).mpr (hround i)
    · rw [List.mem_singleton.mp ht']
      exact (finalCheckTerm_correct asg claimW finalW g0 g1 chal).mpr hfinal

/-- The EXECUTOR reading of the keystone: the semantic relation of the verifier system is
the same acceptance statement — `accepts_iff_semHolds` (initiality) doing the transfer,
no new trust. -/
theorem sumcheckVerifier_semHolds_correct (asg : Idx → F) (claimW finalW : Idx)
    (g0 g1 chal : Fin n → Idx) :
    systemSemHolds asg (sumcheckVerifierGadget claimW finalW g0 g1 chal) ↔
      SumcheckVerifierAccepts (asg claimW) (asg finalW)
        (fun i => asg (g0 i)) (fun i => asg (g1 i)) (fun i => asg (chal i)) := by
  rw [← systemAccepts_iff_systemSemHolds, sumcheckVerifier_correct]

/-! ## §5. Keystone witnesses — BUILT over `ZMod 7` and `ZMod 13`, all `decide`d against
the REAL fold via §1 of `AirRange`'s `Decidable` instances.

The honest transcript is the REAL MLE sumcheck run for `f = AND` on two bits
(`f̂ = x₀·x₁`, `Selvage/MultilinearExtension`'s worked example): claim `H = Σ_b AND(b) = 1`;
`g₀(t) = Σ_b f̂(t, b) = t` so `(g₀(0), g₀(1)) = (0, 1)`; challenge `r₀ = 3`;
`g₁(t) = f̂(3, t) = 3t` so `(g₁(0), g₁(1)) = (0, 3)`; challenge `r₁ = 5`; final oracle
value `f̂(3, 5) = 15 = 1` in `ZMod 7`. Wire layout on `Fin 8`: claim at 0, final at 1,
`gᵢ(0)` at `2+i`, `gᵢ(1)` at `4+i`, `rᵢ` at `6+i` — so the honest vector is
`![1, 1, 0, 0, 1, 3, 3, 5]`. -/

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

namespace SumcheckVerifierExample

/-- Canonical 2-round wire layout on `Fin 8`: claim at 0, final at 1, `gᵢ(0)` at `2+i`,
`gᵢ(1)` at `4+i`, `rᵢ` at `6+i`. -/
def wClaim : Fin 8 := 0
def wFinal : Fin 8 := 1
def wG0 : Fin 2 → Fin 8 := fun i => ⟨2 + i.val, by omega⟩
def wG1 : Fin 2 → Fin 8 := fun i => ⟨4 + i.val, by omega⟩
def wChal : Fin 2 → Fin 8 := fun i => ⟨6 + i.val, by omega⟩

/-- The 2-round verifier gadget over `ZMod 7` at the canonical layout. -/
def gadget7 : ConstraintSystem (ZMod 7) (Fin 8) :=
  sumcheckVerifierGadget wClaim wFinal wG0 wG1 wChal

/-- *Satisfiable, computed*: the HONEST transcript (the real MLE run for AND, challenges
`(3, 5)`) is ACCEPTED. -/
example : systemAccepts ![1, 1, 0, 0, 1, 3, 3, 5] gadget7 := by decide

/-- *Teeth + premise-inhabitation, quantified*: with the honest round data fixed, the
claim wire is FORCED — acceptance holds iff `claim = 1`, over every field element. A
tampered claim (any of the 6 wrong values) is rejected; the true one accepted. -/
example : ∀ c : ZMod 7, systemAccepts ![c, 1, 0, 0, 1, 3, 3, 5] gadget7 ↔ c = 1 := by
  decide

/-- *Teeth (the final oracle check bites), quantified*: the final wire is FORCED to the
fold value `g₁(r₁) = 1` — the arithmetized verifier genuinely compares the oracle. -/
example : ∀ fv : ZMod 7, systemAccepts ![1, fv, 0, 0, 1, 3, 3, 5] gadget7 ↔ fv = 1 := by
  decide

/-- *Teeth (a tampered round message)*: `g₁(1)` altered `3 → 4` — REJECTED (the round-1
folding check `g₁(0)+g₁(1) = g₀(r₀)` breaks: `0+4 ≠ 3`). -/
example : ¬ systemAccepts ![1, 1, 0, 0, 1, 4, 3, 5] gadget7 := by decide

/-- *Teeth (the interpolation is load-bearing)*: challenge `r₀` altered `3 → 4` —
REJECTED: `g₀(r₀)` is computed BY the constraint as `(1−r₀)·g₀(0) + r₀·g₀(1)`, so moving
the challenge moves the folding target (`4·1 = 4 ≠ 3`). -/
example : ¬ systemAccepts ![1, 1, 0, 0, 1, 3, 4, 5] gadget7 := by decide

/-- *…and the attribution is machine-checked, not asserted*: under the tampered `r₀`, the
round-0 check still accepts (it does not read `r₀`)… -/
example : accepts (![1, 1, 0, 0, 1, 3, 4, 5] : Fin 8 → ZMod 7)
    (roundCheckTerm wClaim wG0 wG1 wChal 0) := by decide

/-- *…the final check still accepts (it reads only `r₁` and round 1's wires)…* -/
example : accepts (![1, 1, 0, 0, 1, 3, 4, 5] : Fin 8 → ZMod 7)
    (finalCheckTerm wClaim wFinal wG0 wG1 wChal) := by decide

/-- *…so the rejection is EXACTLY the round-1 folding check* — the interpolation
`(1−r₀)·g₀(0) + r₀·g₀(1)` reading the tampered challenge. -/
example : ¬ accepts (![1, 1, 0, 0, 1, 3, 4, 5] : Fin 8 → ZMod 7)
    (roundCheckTerm wClaim wG0 wG1 wChal 1) := by decide

/-- The 2-round verifier gadget over `ZMod 13`, same layout — field-genericity computed. -/
def gadget13 : ConstraintSystem (ZMod 13) (Fin 8) :=
  sumcheckVerifierGadget wClaim wFinal wG0 wG1 wChal

/-- *Satisfiable over `ZMod 13`*: the honest AND run at challenges `(7, 2)` —
`g₁(t) = f̂(7, t) = 7t`, final `f̂(7, 2) = 14 = 1` — ACCEPTED. -/
example : systemAccepts ![1, 1, 0, 0, 1, 7, 7, 2] gadget13 := by decide

/-- *Teeth over `ZMod 13`*: the same transcript with a tampered claim — REJECTED. -/
example : ¬ systemAccepts ![2, 1, 0, 0, 1, 7, 7, 2] gadget13 := by decide

/-! ## §6. The recursion point, BUILT — the gadget EMITS.

`[RECURSE-verifier]`, first component landed: because the verifier is a
`ConstraintSystem`, the verified emit path applies to it with zero new work — the emitted
`ConstraintDescriptor`'s satisfiability IS the verifier's acceptance
(`emit_accepts_iff_fin`, instantiated below). So **"the sumcheck verifier accepted this
transcript" is itself a Selvage-arithmetizable statement**: prove THAT statement with Selvage
and a proof verifies a proof. What remains under `[RECURSE-verifier]`: binding the
challenge wires to Fiat–Shamir hashes (AirHash `permGadget`), the `finalW` wire to a
Merkle-opened oracle value (AirMembership), and the FRI-query gadget — composed by list
append into one emitted system, on this same rung. -/

/-- **The verifier gadget emitted**: descriptor satisfiability at the canonical layout ⟺
the arithmetized sumcheck verifier accepts — `emit_accepts_iff_fin` consumed on THIS
gadget, no new proof. The recursion apex, concretely: the right-hand side is (by
`sumcheckVerifier_correct`) the verifier's checks, and the left-hand side is a first-order
emitted statement a Selvage proof can target. -/
example (asg : Fin 8 → ZMod 7) :
    (∃ wv : ℕ → ZMod 7, (∀ i : Fin 8, wv i.val = asg i) ∧
        descriptorHolds (emit Fin.val 8 8 gadget7) wv)
      ↔ systemAccepts asg gadget7 :=
  emit_accepts_iff_fin 8 8 asg gadget7

end SumcheckVerifierExample

end Minidregg.Compiler
