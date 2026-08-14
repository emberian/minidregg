/-
# `Compiler/FriQueryVerifierAir.lean` — the FRI query's fold-consistency check
arithmetized: the last major recursive-verifier component

**Substrate, said out loud: this is Lean-AUTHORED AIR.** Every constraint below is a
`Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`), read through
the one fold (`eval = fold evalAlg`), composed as a `ConstraintSystem`; its meaning comes
from rung 1's initiality keystone (`accepts_iff_semHolds`, lifted by
`systemAccepts_iff_systemSemHolds`). NO check is hand-authored outside the DSL — no Rust,
no bespoke `air_accepts`, no parallel executor.

## What is arithmetized

The FRI VERIFIER's per-query check (not the prover's fold): given one query's transcript
laid out on wires — per fold round `k`, the two opened values `lo k` (= `f_k(x)`) and
`hi k` (= `f_k(−x)`), the next round's opened value `next k` (= `f_{k+1}(x²)`), the fold
challenge `beta k`, the witnessed twiddle inverse `tw k` (= `1/(2x)`) and its mate
`twoX k` (= `2x`); plus the claimed final constant `finalW` — the AIR asserts exactly the
verifier's checks:

1. **twiddle-inverse, per round**: `tw_k · twoX_k = 1` — the division in the fold formula
   is ARITHMETIZED as a witnessed inverse with a mul gate, not assumed;
2. **fold-consistency, per round**: `next_k = (lo_k + hi_k)·half + β_k·(lo_k − hi_k)·tw_k`
   — the deployed fold formula, `half` the field constant with `2·half = 1`;
3. **final low-degree check**: the last round's folded value equals the claimed final
   constant — `finalW = next_{rounds−1}`.

`half` is a gadget PARAMETER (a public constant baked into the circuit at construction,
the way deployed folds precompute their half/twiddle tables), and the keystone iff
(`friQueryVerifier_correct`) holds for EVERY `half` — the side condition `2·half = 1`
enters only when reading the constraint as the DIVIDED fold (`friQueryVerifier_correct_div`).
That hypothesis is the deployment label, AirRange's `2^k ≤ p` pattern: over characteristic 2
no `half` satisfies it and the divided fold does not exist — pick the field so it does
(BabyBear does).

## The Selvage correspondence (prose, boundary-honest)

`Compiler` may not import `Selvage` (`Theory`-boundary law), so the correspondence is stated
here at matching shape and the cross-boundary lemma is the named residual
`[RECURSE-fri-bridge]`:

* `Selvage/Proximity.fold D f α = foldEven + α·foldOdd` where
  `foldEven f k = (f(x) + f(−x))/2` and `foldOdd f k = (f(x) − f(−x))/(2x)` at
  `x = D.sec k` — the object `fold_preserves_code` is proved about.
* `friFoldVal half β lo hi tw` below IS that formula with the two divisions rendered as
  the constant `half` and the witnessed wire `tw`: `friFoldVal_eq_div_twoX` proves
  `2·half = 1 → tw·(2x) = 1 → friFoldVal half β lo hi tw = (lo+hi)/2 + β·(lo−hi)/(2x)` —
  the in-boundary bridge, exactly `Selvage.fold` at `f(x) = lo`, `f(−x) = hi`.
* Check (2) is therefore `next_k = Selvage.fold D f_k β_k (sq x)`'s shape per round, and
  check (3) is the final low-degree comparison (`Proximity`'s last-round constant check).

`[RECURSE-fri-bridge]` — the machine-checked identification
(`systemAccepts asg (friQueryVerifierGadget …) ↔` the `Selvage.fold` equations at the real
domain points), statable only in a layer importing both (Assurance). Everything on THIS
side of the boundary is proved; the residual is the cross-boundary restatement, not a gap
in the gadget's meaning.

## Honest scope — which wires are FREE here, and who binds them

* `next k` is a free input wire: it is the round-`(k+1)` MERKLE-OPENED value, and binding
  it to the actual commitment is AirMembership's job in the composition (which of the next
  round's `lo`/`hi` slots the folded value lands on is query-index parity plumbing — a
  wiring choice, not a constraint: the caller passes overlapping indices, demonstrated in
  §5's chained example, where `next 0` IS round 1's `lo` wire and `next 1` IS the final
  wire).
* `twoX k` is a free input wire: the domain-point arithmetic (`x` from the query index,
  the squaring chain `x_{k+1} = x_k²`) is composition/bridge work. What is NOT free is its
  RELATION to `tw k` — constraint (1) forces `tw_k = twoX_k⁻¹` whenever `twoX_k` is
  bound, so the division is inside the proof, not the prover's word.
* `beta k` is a free input wire: Fiat–Shamir binding is AirHash's `permGadget` in the
  composition.
* `rounds = 0` degenerates honestly: no folds, no openings on any wire, and the final
  check reduces to `finalW = finalW` — the gadget checks nothing because a 0-round query
  checks nothing; deployment always has `rounds ≥ 1`.

## The recursion point — `[RECURSE-verifier]`, all three components now on this rung

The gadget is a `ConstraintSystem`, so the WHOLE emit path applies verbatim
(`emit_accepts_iff_fin`, instantiated in §6). With `sumcheckVerifierGadget`
(sumcheck-verify) and AirMembership's `membershipGadget` (Merkle-open) already landed,
this was the last major verifier component: the light-client check as ONE emitted system
is now `sumcheckVerifierGadget … ++ friQueryVerifierGadget … ++ membershipGadget …` —
`systemAccepts` distributes over `++` (`systemAccepts_append`), proved for the
sumcheck + FRI pair as `recursiveVerifierPair_correct` in §4. What remains under
`[RECURSE-verifier]`: the actual wire-sharing composition (challenges to FS hashes,
`lo`/`hi`/`next` to Merkle openings, `twoX` to the index's domain point) and
`[RECURSE-fri-bridge]`/`[RECURSE-sumcheck-bridge]` (the Selvage identifications,
Assurance-side).

## Statement-first (ATLAS fields)

* `FriQueryAccepts` — the verifier's checks as a `Prop`, stated BEFORE the gadget.
  Satisfiable: an honest FRI run (a real degree-1 word, really folded, twiddles really
  inverse) inhabits it (§5, decided). Teeth: tampered opened values and fake twiddles are
  rejected, with per-check attribution (§5, decided). Premise-inhabitation: the
  quantified keystones (`↔ v = _` forms) show acceptance pins wires, not vacuously.
* `friQueryVerifier_correct` — the keystone iff: the AIR accepts iff the FRI query's
  checks hold. Derived from `accepts_iff_semHolds` + the §2 eval lemmas; no bespoke
  soundness argument, no new induction.
-/
import Compiler.SumcheckVerifierAir

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {rounds n : ℕ}

/-! ## §1. The semantic spec, statement-first — the FRI query's checks as a `Prop`. -/

/-- **The deployed fold formula, twiddle form**: `(lo + hi)·half + β·(lo − hi)·tw`. With
`2·half = 1` and `tw·(2x) = 1` this IS `Selvage/Proximity.fold`'s
`(f(x)+f(−x))/2 + β·(f(x)−f(−x))/(2x)` at `f(x) = lo`, `f(−x) = hi`
(`friFoldVal_eq_div_twoX` below). -/
def friFoldVal (half β lo hi tw : F) : F := (lo + hi) * half + β * (lo - hi) * tw

/-- The last fold value: `next (rounds−1)`, or (junk, `rounds = 0` only, never a real
deployment) the final value itself — making the degenerate final check vacuous, honestly. -/
def lastVal (finalv : F) (nextv : Fin rounds → F) : F :=
  if h : 0 < rounds then nextv ⟨rounds - 1, Nat.sub_lt h Nat.one_pos⟩ else finalv

/-- **The FRI query verifier's acceptance, statement-first.** Every twiddle wire is the
genuine inverse of its `2x` mate, every round's opened values fold to the next round's
opened value by the deployed formula, and the last fold equals the claimed final
constant. This is the fold-consistency conjunction `Selvage`'s query check imposes on one
query path; the machine-checked identification is `[RECURSE-fri-bridge]`. -/
def FriQueryAccepts (half finalv : F)
    (lov hiv nextv betav twv twoXv : Fin rounds → F) : Prop :=
  (∀ k, twv k * twoXv k = 1)
    ∧ (∀ k, nextv k = friFoldVal half (betav k) (lov k) (hiv k) (twv k))
    ∧ finalv = lastVal finalv nextv

/-- **The divided-form bridge (in-boundary).** When the half constant and the twiddle wire
really are the inverses their constraints claim (`2·half = 1`, `tw·t2x = 1`), the
arithmetized fold IS the divided fold `(lo+hi)/2 + β·(lo−hi)/t2x` — at `t2x = 2x` this is
verbatim `Selvage.Proximity.fold`'s formula. The `Selvage` restatement is
`[RECURSE-fri-bridge]`. -/
theorem friFoldVal_eq_div_twoX {half tw t2x : F} (hhalf : (2 : F) * half = 1)
    (htw : tw * t2x = 1) (β lo hi : F) :
    friFoldVal half β lo hi tw = (lo + hi) / 2 + β * (lo - hi) / t2x := by
  unfold friFoldVal
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hhalf,
    inv_eq_of_mul_eq_one_left htw]

/-! ### ⚑ The deployment label is a CHARACTERISTIC-TWO WALL, and it is named here

The module header says `2 · half = 1` "is the deployment label … over characteristic 2 no
`half` satisfies it and the divided fold does not exist".  That is correct, and the two
theorems below make it MACHINE-CHECKED rather than prose.  It matters because
`friFoldVal_eq_div_twoX` and `friQueryVerifier_correct_div` are stated over an
unconstrained `[Field F]`: nothing in their types stops a reader from instantiating them
at `Tower256` and reading a VACUOUS statement as a deployment result.

⚑ Note what is and is not walled.  `friQueryVerifier_correct` — the keystone iff — holds
for EVERY `half` and is untouched by this; the gadget itself arithmetizes fine over a
binary field.  Only the DIVIDED reading dies, because that is the multiplicative
even/odd fold.  The characteristic-two protocol folds along an additive coset instead
(`Selvage.AdditiveFriTower.additiveTowerFold`), which never halves; arithmetizing THAT
fold is the honest binary-field task, not relaxing `2 · half = 1`. -/

/-- **No half constant exists at characteristic two.**  `2 = 0`, so `2 * half = 0 ≠ 1`. -/
theorem no_half_of_charTwo [CharP F 2] (half : F) : (2 : F) * half ≠ 1 := by
  rw [CharTwo.two_eq_zero, zero_mul]
  exact zero_ne_one

/-- **The vacuity, named.**  At characteristic two the `2 * half = 1` premise of
`friFoldVal_eq_div_twoX` / `friQueryVerifier_correct_div` proves anything at all.  Cite
this if either theorem is ever quoted at a binary field: it is not a weak result there,
it is no result. -/
theorem dividedFold_vacuous_of_charTwo [CharP F 2] {half : F}
    (hhalf : (2 : F) * half = 1) (P : Prop) : P :=
  absurd hhalf (no_half_of_charTwo half)

/-- info: 'Minidregg.Compiler.no_half_of_charTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_half_of_charTwo
/-- info: 'Minidregg.Compiler.dividedFold_vacuous_of_charTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dividedFold_vacuous_of_charTwo

/-! ## §2. The checks as DSL terms — every constraint out of the compiler surface. -/

/-- The fold formula as a DSL term: `(lo + hi)·half + (β·(lo + (−1)·hi))·tw`. -/
def friFoldTerm (half : F) (β lo hi tw : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  add' (mul' (add' lo hi) (cst half))
    (mul' (mul' β (add' lo (mul' (cst (-1)) hi))) tw)

@[simp] theorem eval_friFoldTerm (asg : Idx → F) (half : F)
    (β lo hi tw : Term (AirSig F Idx)) :
    eval asg (friFoldTerm half β lo hi tw)
      = friFoldVal half (eval asg β) (eval asg lo) (eval asg hi) (eval asg tw) := by
  simp only [friFoldTerm, eval_add', eval_mul', eval_cst, friFoldVal]
  ring

/-- The twiddle-inverse assertion: `tw·twoX + (−1) ≐ 0` — one mul gate; the division of
the deployed fold is WITNESSED and CONSTRAINED, not assumed. -/
def twiddleCheckTerm (tw twoX : Idx) : Term (AirSig F Idx) :=
  add' (mul' (vr tw) (vr twoX)) (cst (-1))

/-- The twiddle assertion MEANS the inverse relation: it accepts iff `tw·twoX = 1`. -/
theorem twiddleCheckTerm_correct (asg : Idx → F) (tw twoX : Idx) :
    accepts asg (twiddleCheckTerm (F := F) tw twoX) ↔ asg tw * asg twoX = 1 := by
  unfold accepts twiddleCheckTerm
  rw [eval_add', eval_mul', eval_vr, eval_vr, eval_cst, add_neg_eq_zero]

/-- Round `k`'s fold-consistency assertion:
`next_k − [(lo_k + hi_k)·half + β_k·(lo_k − hi_k)·tw_k] ≐ 0`. -/
def foldCheckTerm (half : F) (lo hi next beta tw : Fin rounds → Idx) (k : Fin rounds) :
    Term (AirSig F Idx) :=
  add' (vr (next k))
    (mul' (cst (-1)) (friFoldTerm half (vr (beta k)) (vr (lo k)) (vr (hi k)) (vr (tw k))))

/-- The fold assertion MEANS the fold equation: it accepts iff
`next_k = friFoldVal half β_k lo_k hi_k tw_k`. -/
theorem foldCheckTerm_correct (asg : Idx → F) (half : F)
    (lo hi next beta tw : Fin rounds → Idx) (k : Fin rounds) :
    accepts asg (foldCheckTerm half lo hi next beta tw k) ↔
      asg (next k)
        = friFoldVal half (asg (beta k)) (asg (lo k)) (asg (hi k)) (asg (tw k)) := by
  unfold accepts foldCheckTerm
  rw [eval_add', eval_mul', eval_cst, eval_vr, eval_friFoldTerm, eval_vr, eval_vr,
    eval_vr, eval_vr, neg_one_mul, add_neg_eq_zero]

/-- The last fold value as a DSL term — `lastVal`'s syntax, mirrored
constructor-for-constructor (`vr finalW` in the junk `rounds = 0` branch). -/
def lastTerm (finalW : Idx) (next : Fin rounds → Idx) : Term (AirSig F Idx) :=
  if h : 0 < rounds then vr (next ⟨rounds - 1, Nat.sub_lt h Nat.one_pos⟩) else vr finalW

/-- The circuit reads `lastTerm` as `lastVal` — the two renderings agree. -/
theorem eval_lastTerm (asg : Idx → F) (finalW : Idx) (next : Fin rounds → Idx) :
    eval asg (lastTerm finalW next) = lastVal (asg finalW) (fun k => asg (next k)) := by
  unfold lastTerm lastVal
  by_cases h : 0 < rounds
  · rw [dif_pos h, dif_pos h, eval_vr]
  · rw [dif_neg h, dif_neg h, eval_vr]

/-- The final low-degree assertion: `finalW − next_{rounds−1} ≐ 0` — the last folded value
IS the claimed final constant. -/
def finalConstTerm (finalW : Idx) (next : Fin rounds → Idx) : Term (AirSig F Idx) :=
  add' (vr finalW) (mul' (cst (-1)) (lastTerm finalW next))

/-- The final assertion MEANS the final check. -/
theorem finalConstTerm_correct (asg : Idx → F) (finalW : Idx) (next : Fin rounds → Idx) :
    accepts asg (finalConstTerm finalW next) ↔
      asg finalW = lastVal (asg finalW) (fun k => asg (next k)) := by
  unfold accepts finalConstTerm
  rw [eval_add', eval_mul', eval_cst, eval_vr, eval_lastTerm, neg_one_mul,
    add_neg_eq_zero]

/-! ## §3. The gadget and its keystone iff. -/

/-- A mapped-`finRange` block of a system accepts iff every indexed assertion accepts —
the list-membership plumbing spent once (both round blocks below reuse it). -/
theorem systemAccepts_map_finRange {m : ℕ} (asg : Idx → F)
    (f : Fin m → Term (AirSig F Idx)) :
    systemAccepts asg ((List.finRange m).map f) ↔ ∀ k, accepts asg (f k) := by
  unfold systemAccepts
  constructor
  · intro h k
    exact h _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
  · rintro h t ht
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ht
    exact h k

/-- A singleton system accepts iff its one assertion accepts. -/
theorem systemAccepts_singleton (asg : Idx → F) (t : Term (AirSig F Idx)) :
    systemAccepts asg [t] ↔ accepts asg t :=
  List.forall_mem_singleton

/-- **The FRI-query verifier gadget** — the last major recursive-verifier component:
per round a twiddle-inverse assertion and a fold-consistency assertion, plus the final
low-degree assertion — all DSL terms, composed as a system. A `ConstraintSystem`, so the
emit path (`flattenSystem`/`emit`) applies verbatim (§6). -/
def friQueryVerifierGadget (half : F) (finalW : Idx)
    (lo hi next beta tw twoX : Fin rounds → Idx) : ConstraintSystem F Idx :=
  ((List.finRange rounds).map fun k => twiddleCheckTerm (tw k) (twoX k))
    ++ (((List.finRange rounds).map fun k => foldCheckTerm half lo hi next beta tw k)
      ++ [finalConstTerm finalW next])

/-- **The keystone iff — the AIR accepts iff the FRI query verifier accepts.** The system
accepts `asg` iff every twiddle-inverse check, every fold-consistency check, and the final
low-degree check hold on the wire values — `FriQueryAccepts`, the statement-first spec.
Derived: per-term correctness (§2) under the append/membership split; the semantic
transfer is rung 1's initiality. -/
theorem friQueryVerifier_correct (asg : Idx → F) (half : F) (finalW : Idx)
    (lo hi next beta tw twoX : Fin rounds → Idx) :
    systemAccepts asg (friQueryVerifierGadget half finalW lo hi next beta tw twoX) ↔
      FriQueryAccepts half (asg finalW) (fun k => asg (lo k)) (fun k => asg (hi k))
        (fun k => asg (next k)) (fun k => asg (beta k)) (fun k => asg (tw k))
        (fun k => asg (twoX k)) := by
  unfold friQueryVerifierGadget FriQueryAccepts
  rw [systemAccepts_append, systemAccepts_append, systemAccepts_map_finRange,
    systemAccepts_map_finRange, systemAccepts_singleton, finalConstTerm_correct]
  exact and_congr (forall_congr' fun k => twiddleCheckTerm_correct asg (tw k) (twoX k))
    (and_congr
      (forall_congr' fun k => foldCheckTerm_correct asg half lo hi next beta tw k)
      Iff.rfl)

/-- The EXECUTOR reading of the keystone: the semantic relation of the FRI-query system is
the same acceptance statement — `accepts_iff_semHolds` (initiality) doing the transfer,
no new trust. -/
theorem friQueryVerifier_semHolds_correct (asg : Idx → F) (half : F) (finalW : Idx)
    (lo hi next beta tw twoX : Fin rounds → Idx) :
    systemSemHolds asg (friQueryVerifierGadget half finalW lo hi next beta tw twoX) ↔
      FriQueryAccepts half (asg finalW) (fun k => asg (lo k)) (fun k => asg (hi k))
        (fun k => asg (next k)) (fun k => asg (beta k)) (fun k => asg (tw k))
        (fun k => asg (twoX k)) := by
  rw [← systemAccepts_iff_systemSemHolds, friQueryVerifier_correct]

/-- **The DIVIDED reading — the gadget accepts iff Selvage's fold equations hold.** Under the
deployment label `2·half = 1`, acceptance is: the twiddles invert, and every round
satisfies `next_k = (lo_k + hi_k)/2 + β_k·(lo_k − hi_k)/twoX_k` — with `twoX_k` carrying
`2x`, verbatim `Selvage.Proximity.fold`'s formula — plus the final check. The first conjunct
FEEDS the second (the division form only means division because the inverse constraint
holds): the arithmetized division is load-bearing, not decorative. -/
theorem friQueryVerifier_correct_div (asg : Idx → F) {half : F}
    (hhalf : (2 : F) * half = 1) (finalW : Idx)
    (lo hi next beta tw twoX : Fin rounds → Idx) :
    systemAccepts asg (friQueryVerifierGadget half finalW lo hi next beta tw twoX) ↔
      ((∀ k, asg (tw k) * asg (twoX k) = 1)
        ∧ (∀ k, asg (next k) = (asg (lo k) + asg (hi k)) / 2
            + asg (beta k) * (asg (lo k) - asg (hi k)) / asg (twoX k))
        ∧ asg finalW = lastVal (asg finalW) (fun k => asg (next k))) := by
  rw [friQueryVerifier_correct]
  simp only [FriQueryAccepts]
  exact and_congr_right fun htw => and_congr_left fun _ => forall_congr' fun k => by
    rw [friFoldVal_eq_div_twoX hhalf (htw k)]

/-! ## §4. The composition toward the apex — `[RECURSE-verifier]`.

Gadgets compose by list append and `systemAccepts_append` turns the composite into the
conjunction of meanings — so the whole verifier-as-a-circuit is assembled from proved
parts with zero new constraint work. The pair below (sumcheck-verify + FRI-query) is the
proof-system spine; AirMembership's `membershipGadget` appends the same way to bind each
opened wire (`lo k`/`hi k`/`next k`) to a Merkle root, and AirHash's `permGadget` to bind
`beta k`/`chal i` to Fiat–Shamir transcript hashes. The remaining `[RECURSE-verifier]`
mass is exactly that wire-sharing (plus the `[RECURSE-*-bridge]` Selvage identifications,
Assurance-side); the constraint vocabulary is now complete. -/

/-- **Sumcheck-verify + FRI-query as ONE system** — the two proof-system components of the
recursive verifier, appended, accept iff BOTH verifiers accept. One `systemAccepts_append`
plus the two keystones; the same step extends to `++ membershipGadget …` for the Merkle
openings. -/
theorem recursiveVerifierPair_correct (asg : Idx → F)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx) :
    systemAccepts asg
        (sumcheckVerifierGadget claimW scFinalW g0 g1 chal
          ++ friQueryVerifierGadget half friFinalW lo hi next beta tw twoX) ↔
      (SumcheckVerifierAccepts (asg claimW) (asg scFinalW)
          (fun i => asg (g0 i)) (fun i => asg (g1 i)) (fun i => asg (chal i))
        ∧ FriQueryAccepts half (asg friFinalW)
            (fun k => asg (lo k)) (fun k => asg (hi k)) (fun k => asg (next k))
            (fun k => asg (beta k)) (fun k => asg (tw k)) (fun k => asg (twoX k))) := by
  rw [systemAccepts_append, sumcheckVerifier_correct, friQueryVerifier_correct]

/-! ## §5. Keystone witnesses — BUILT over `ZMod 7` and `ZMod 13`, all `decide`d against
the REAL fold via `AirRange`'s `Decidable` instances.

The honest transcript is a REAL FRI run over `ZMod 7`, two fold rounds, on the word of
`p(X) = X + 1` (even part `1`, odd part `1`): query point `x₀ = 3`, so `twoX₀ = 6` and
`tw₀ = 6⁻¹ = 6`; opened `lo₀ = p(3) = 4`, `hi₀ = p(−3) = p(4) = 5`; challenge `β₀ = 2`
folds to the CONSTANT word `1 + β₀ = 3`, opened at `x₁ = x₀² = 2` (so `twoX₁ = 4`,
`tw₁ = 4⁻¹ = 2`, the squaring chain honest too): `next₀ = 3`, `lo₁ = hi₁ = 3`; challenge
`β₁ = 5` folds the constant to itself, `next₁ = 3 = final`. `half = 4` (`2·4 = 1`).
Wire layout on `Fin 13`: final at 0, `lo_k` at `1+k`, `hi_k` at `3+k`, `next_k` at `5+k`,
`β_k` at `7+k`, `tw_k` at `9+k`, `twoX_k` at `11+k` — the honest vector is
`![3, 4, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4]`. -/

namespace FriQueryVerifierExample

/-- Canonical 2-round wire layout on `Fin 13`. -/
def wFinal : Fin 13 := 0
def wLo : Fin 2 → Fin 13 := fun k => ⟨1 + k.val, by omega⟩
def wHi : Fin 2 → Fin 13 := fun k => ⟨3 + k.val, by omega⟩
def wNext : Fin 2 → Fin 13 := fun k => ⟨5 + k.val, by omega⟩
def wBeta : Fin 2 → Fin 13 := fun k => ⟨7 + k.val, by omega⟩
def wTw : Fin 2 → Fin 13 := fun k => ⟨9 + k.val, by omega⟩
def wTwoX : Fin 2 → Fin 13 := fun k => ⟨11 + k.val, by omega⟩

/-- The 2-round FRI-query gadget over `ZMod 7` at the canonical layout, `half = 4`. -/
def gadget7 : ConstraintSystem (ZMod 7) (Fin 13) :=
  friQueryVerifierGadget 4 wFinal wLo wHi wNext wBeta wTw wTwoX

/-- *Satisfiable, computed*: the HONEST transcript (a real 2-round fold of `X + 1`,
challenges `(2, 5)`, genuine twiddle inverses on the genuine squaring chain) is
ACCEPTED. -/
example : systemAccepts ![3, 4, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] gadget7 := by decide

/-- *Teeth + premise-inhabitation, quantified*: with everything else honest, the opened
value `lo₀` is FORCED — acceptance holds iff `lo₀ = 4`, over every field element (the
fold check is linear in `lo₀` with coefficient `half + β₀·tw₀ = 2 ≠ 0`). A tampered
opening (any of the 6 wrong values) is rejected; the true one accepted. -/
example : ∀ v : ZMod 7,
    systemAccepts ![3, v, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] gadget7 ↔ v = 4 := by decide

/-- *Teeth (a tampered opened value), the fold equation violated*: `lo₀` altered `4 → 5`
— REJECTED. -/
example : ¬ systemAccepts ![3, 5, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] gadget7 := by decide

/-- *…and the attribution is machine-checked, not asserted*: under the tampered `lo₀`,
both twiddle-inverse checks still accept (they do not read openings)… -/
example : ∀ k : Fin 2, accepts (![3, 5, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] : Fin 13 → ZMod 7)
    (twiddleCheckTerm (wTw k) (wTwoX k)) := by decide

/-- *…round 1's fold check still accepts (it reads only round 1's wires)…* -/
example : accepts (![3, 5, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] : Fin 13 → ZMod 7)
    (foldCheckTerm 4 wLo wHi wNext wBeta wTw 1) := by decide

/-- *…the final check still accepts…* -/
example : accepts (![3, 5, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] : Fin 13 → ZMod 7)
    (finalConstTerm wFinal wNext) := by decide

/-- *…so the rejection is EXACTLY round 0's fold-consistency check* — the tampered
opening breaks the fold equation it appears in, and nothing else. -/
example : ¬ accepts (![3, 5, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] : Fin 13 → ZMod 7)
    (foldCheckTerm 4 wLo wHi wNext wBeta wTw 0) := by decide

/-- *Teeth (the twiddle-inverse constraint is LOAD-BEARING), computed*: a FAKE twiddle
`tw₀ = 2` with `next₀` adjusted to `4` so the fold ALGEBRA passes with the fake value —
REJECTED anyway. Without the inverse constraint a prover could fold with any "twiddle"
and fabricate consistency; the mul gate `tw·twoX = 1` closes that door. -/
example : ¬ systemAccepts ![3, 4, 3, 5, 3, 4, 3, 2, 5, 2, 2, 6, 4] gadget7 := by decide

/-- *…attribution machine-checked*: on the fake-twiddle vector every fold check
accepts… -/
example : ∀ k : Fin 2, accepts (![3, 4, 3, 5, 3, 4, 3, 2, 5, 2, 2, 6, 4] : Fin 13 → ZMod 7)
    (foldCheckTerm 4 wLo wHi wNext wBeta wTw k) := by decide

/-- *…and the final check accepts…* -/
example : accepts (![3, 4, 3, 5, 3, 4, 3, 2, 5, 2, 2, 6, 4] : Fin 13 → ZMod 7)
    (finalConstTerm wFinal wNext) := by decide

/-- *…so the rejection is EXACTLY the twiddle-inverse check*: `2·6 = 5 ≠ 1`. -/
example : ¬ accepts (![3, 4, 3, 5, 3, 4, 3, 2, 5, 2, 2, 6, 4] : Fin 13 → ZMod 7)
    (twiddleCheckTerm (wTw 0) (wTwoX 0)) := by decide

/-- *Teeth (wrong twiddle, quantified)*: with everything else honest, the twiddle wire is
FORCED — acceptance holds iff `tw₀ = 6 = 6⁻¹` (pinned twice over: by the inverse
constraint against `twoX₀` and by the fold equation), over every field element. -/
example : ∀ t : ZMod 7,
    systemAccepts ![3, 4, 3, 5, 3, 3, 3, 2, 5, t, 2, 6, 4] gadget7 ↔ t = 6 := by decide

/-- *Teeth (the final low-degree check bites), quantified*: the final wire is FORCED to
the last folded value `3` — the arithmetized verifier genuinely compares the claimed
constant. -/
example : ∀ fv : ZMod 7,
    systemAccepts ![fv, 4, 3, 5, 3, 3, 3, 2, 5, 6, 2, 6, 4] gadget7 ↔ fv = 3 := by decide

/-! ### The chained wiring — `next` bound by INDEX-SHARING, the composition mechanism.

Binding round `k`'s fold target to round `k+1`'s opened value is a wiring choice, not a
new constraint: pass `next 0 := wLo 1` and `next 1 := wFinal`. The fold chain then runs
THROUGH the shared wires — round 0 folds onto round 1's opening, round 1 folds onto the
final constant (wires 5, 6 go unused; the final check degenerates to the shared wire's
reflexivity, its content absorbed into round 1's fold check). This is exactly how the
full `[RECURSE-verifier]` composition binds this gadget to AirMembership's opened
leaves. -/

/-- The chained layout: round 0's fold target IS round 1's `lo` wire; round 1's fold
target IS the final-constant wire. -/
def wNextChained : Fin 2 → Fin 13 := ![wLo 1, wFinal]

/-- The chained 2-round gadget over `ZMod 7`. -/
def gadget7Chained : ConstraintSystem (ZMod 7) (Fin 13) :=
  friQueryVerifierGadget 4 wFinal wLo wHi wNextChained wBeta wTw wTwoX

/-- *Satisfiable, chained*: the same honest transcript accepts with the fold chain run
through shared wires (positions 5, 6 junk `0`, never read). -/
example : systemAccepts ![3, 4, 3, 5, 3, 0, 0, 2, 5, 6, 2, 6, 4] gadget7Chained := by
  decide

/-- *Teeth, chained*: tampering the SHARED wire (round 1's opened `lo₁` = round 0's fold
target) `3 → 4` breaks the chain — REJECTED. -/
example : ¬ systemAccepts ![3, 4, 4, 5, 3, 0, 0, 2, 5, 6, 2, 6, 4] gadget7Chained := by
  decide

/-! ### Field-genericity — the same gadget over `ZMod 13`, one round. -/

/-- A 1-round gadget over `ZMod 13` (`half = 7`, `2·7 = 1`), layout: final 0, lo 1, hi 2,
next 3, β 4, tw 5, twoX 6. -/
def gadget13 : ConstraintSystem (ZMod 13) (Fin 7) :=
  friQueryVerifierGadget (rounds := 1) 7 0 (fun _ => 1) (fun _ => 2) (fun _ => 3)
    (fun _ => 4) (fun _ => 5) (fun _ => 6)

/-- *Satisfiable over `ZMod 13`*: the honest fold of `p(X) = 3X + 2` at `x = 2`
(`lo = p(2) = 8`, `hi = p(−2) = 9`, `twoX = 4`, `tw = 4⁻¹ = 10`, `β = 6`, folded
constant `2 + 6·3 = 7 = final`) — ACCEPTED. -/
example : systemAccepts ![7, 8, 9, 7, 6, 10, 4] gadget13 := by decide

/-- *Teeth over `ZMod 13`*: the same transcript with a tampered opening `hi = 10` —
REJECTED. -/
example : ¬ systemAccepts ![7, 8, 10, 7, 6, 10, 4] gadget13 := by decide

/-! ## §6. The recursion point, BUILT — the gadget EMITS.

`[RECURSE-verifier]`, last major component landed: because the FRI-query verifier is a
`ConstraintSystem`, the verified emit path applies with zero new work — the emitted
`ConstraintDescriptor`'s satisfiability IS the query verifier's acceptance
(`emit_accepts_iff_fin`, instantiated below). So **"the FRI query folded consistently" is
itself a Selvage-arithmetizable statement**: prove THAT statement with Selvage and a proof
verifies a proof. Together with `sumcheckVerifierGadget` (§4's append) and
AirMembership's `membershipGadget`, every check of the light client now exists as an
emittable constraint — the apex assembly is wire-sharing, `[RECURSE-verifier]`'s
remaining mass. -/

/-- **The FRI-query gadget emitted**: descriptor satisfiability at the canonical layout ⟺
the arithmetized query verifier accepts — `emit_accepts_iff_fin` consumed on THIS gadget,
no new proof. -/
example (asg : Fin 13 → ZMod 7) :
    (∃ wv : ℕ → ZMod 7, (∀ i : Fin 13, wv i.val = asg i) ∧
        descriptorHolds (emit Fin.val 13 13 gadget7) wv)
      ↔ systemAccepts asg gadget7 :=
  emit_accepts_iff_fin 13 13 asg gadget7

end FriQueryVerifierExample

end Minidregg.Compiler
