/-
# Loom.Sumcheck — sumcheck soundness by univariate root-counting + a union bound.

The load-bearing content of sumcheck soundness is Schwartz–Zippel in one variable:
two distinct polynomials of degree `≤ d` over a field `F` agree on at most `d`
points, so a uniformly random challenge separates them except with probability
`≤ d/|F|`. Minidregg already proved exactly this shape for the Reed–Solomon
minimum distance (`Loom/ReedSolomon.lean`, `card_agreeSet_lt_of_ne`, over an
arbitrary evaluation embedding `ι ↪ F`); here we instantiate it at the identity
embedding `Function.Embedding.refl F` to get the field-wide agreement bound and
build the protocol soundness on top. Nothing is re-derived.

**What is proved here (no `sorry`, no vacuity):**

* `card_agreeFinset_lt` — the field-wide Schwartz–Zippel core, a two-line reuse of
  Reed–Solomon's `card_agreeSet_lt_of_ne` at `Function.Embedding.refl F`.
* `sumcheckRound_sound` — **single-round soundness.** If the verifier's boolean
  check `g̃(0)+g̃(1) = H` passes on a FALSE claim (`H ≠ g(0)+g(1)`, `g` the honest
  round polynomial), then `g̃ ≠ g`, so the fold values agree — `g̃(r) = g(r)`, the
  event that launders the lie into a true sub-claim — on at most `d` challenges.
* `sumcheckRound_prob` — the probability rendering: `≤ d/|F|`.
* `sumcheck_soundness` — **the v-round composition.** For a run whose round
  polynomials are fixed (challenge-independent), a verifier that accepts an
  initially-false claim forces the random challenge vector to launder the lie at
  some round; a union bound over the `v` rounds gives acceptance probability
  `≤ v·d/|F|`. The union bound reuses `uniformProb_exists_le` (Loom/Depth.lean);
  the per-round `≤ d/|F|` reuses the fibrewise `uniformProb_prod_le` + `splitCoord`.

The reduction "accept ∧ false ⟹ some round launders" is `sumcheck_reduction`,
proved by an elementary lie-persistence induction (`lie_persists`): if no round
launders, the claim stays wrong through the final check, which then rejects.

**Honest boundary (`AdaptiveUnionBound`, the remaining obligation).** The proved
composition fixes the round polynomials up front. A fully adaptive prover chooses
round `i`'s message as a function of the challenge prefix `r|_{<i}`; the same
union bound still holds (each round's bad set is prefix-measurable, and
`uniformProb_prod_le` conditions on all coordinates but the fresh one), but that
generalization is stated, not discharged, here — `AdaptiveUnionBound`, a genuine
`Prop` with the fixed case as a firing sub-instance (`sumcheck_soundness` witnesses
its teeth), left as the sumcheck front's obligation.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Loom.ReedSolomon
import Loom.Depth

namespace Minidregg.Loom

open Polynomial

-- `uniformProb`/`splitCoord`/`uniformProb_prod_le` (Loom/Depth.lean) are
-- universe-monomorphic (`Type`), so we work over `F : Type` — every concrete
-- finite field lands here.
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The field-wide Schwartz–Zippel core (reuse of Reed–Solomon root counting) -/

/-- The set of field elements on which two polynomials agree. -/
def agreeFinset (p q : Polynomial F) : Finset F :=
  Finset.univ.filter fun x => p.eval x = q.eval x

@[simp] theorem mem_agreeFinset {p q : Polynomial F} {x : F} :
    x ∈ agreeFinset p q ↔ p.eval x = q.eval x := by
  simp [agreeFinset]

/-- **Field-wide Schwartz–Zippel, degree `< d`.** Distinct polynomials of degree
`< d` agree on strictly fewer than `d` field elements. A direct instantiation of
Reed–Solomon's `card_agreeSet_lt_of_ne` at the identity embedding `Fin.refl F`;
no root counting is repeated. -/
theorem card_agreeFinset_lt {d : ℕ} {p q : Polynomial F}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ)) (hne : p ≠ q) :
    (agreeFinset p q).card < d := by
  have h := card_agreeSet_lt_of_ne (F := F) (Function.Embedding.refl F) hp hq hne
  simpa [agreeFinset, Function.Embedding.refl_apply] using h

/-! ## Uniform-probability of a coordinate landing in a fixed set

Two reused facts: a fixed finite event has probability `card/|F|`
(`uniformProb_mem_finset`), and a single coordinate of a random tuple lands in a
fixed set with the same probability — the fibrewise `uniformProb_prod_le` +
`splitCoord` from `Loom/Depth.lean`, no new counting. -/

omit [Field F] [DecidableEq F] in
/-- `Pr_{x ← F}[x ∈ S] = |S| / |F|`. -/
theorem uniformProb_mem_finset (S : Finset F) :
    uniformProb F (fun x => x ∈ S) = (S.card : ℝ) / Fintype.card F := by
  unfold uniformProb
  have hc : Nat.card {x : F // x ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hc]

omit [DecidableEq F] in
/-- **A single coordinate of a uniform tuple lands in a fixed set with the same
probability `|S|/|F|`.** Slice the `i`-th coordinate out with `splitCoord` and
apply the fibrewise `uniformProb_prod_le`. -/
theorem uniformProb_coord_mem {v : ℕ} (i : Fin v) (S : Finset F) :
    uniformProb (Fin v → F) (fun r => r i ∈ S) ≤ (S.card : ℝ) / Fintype.card F := by
  have hkey : uniformProb (Fin v → F) (fun r => r i ∈ S)
      = uniformProb (({j : Fin v // j ≠ i} → F) × F) (fun x => x.2 ∈ S) :=
    uniformProb_equiv (splitCoord i) (fun x => x.2 ∈ S)
  rw [hkey]
  refine uniformProb_prod_le (by positivity) (fun a => ?_)
  show uniformProb F (fun b => b ∈ S) ≤ (S.card : ℝ) / Fintype.card F
  rw [uniformProb_mem_finset]

/-! ## Single-round sumcheck soundness -/

/-- **Single-round sumcheck soundness (counting form).** `g` is the honest round
polynomial, `gp` the prover's claimed round polynomial, both of degree `< d+1`
(i.e. `≤ d`). If the verifier's boolean check `gp(0)+gp(1) = H` passes on a FALSE
claim `H ≠ g(0)+g(1)`, then `gp ≠ g`, so the fold values `gp(r) = g(r)` — the
event that turns the lie into a *true* sub-claim and lets the prover proceed —
agree on at most `d` challenges. -/
theorem sumcheckRound_sound {d : ℕ} {g gp : Polynomial F} {H : F}
    (hg : g.degree < ((d + 1 : ℕ) : WithBot ℕ)) (hgp : gp.degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hcheck : gp.eval 0 + gp.eval 1 = H) (hfalse : H ≠ g.eval 0 + g.eval 1) :
    (agreeFinset gp g).card ≤ d := by
  have hne : gp ≠ g := by
    rintro rfl
    exact hfalse hcheck.symm
  have h := card_agreeFinset_lt hgp hg hne
  omega

/-- **Single-round sumcheck soundness (probability form): `≤ d/|F|`.** The random
challenge launders the lie with probability at most `d/|F|`. -/
theorem sumcheckRound_prob {d : ℕ} {g gp : Polynomial F} {H : F}
    (hg : g.degree < ((d + 1 : ℕ) : WithBot ℕ)) (hgp : gp.degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hcheck : gp.eval 0 + gp.eval 1 = H) (hfalse : H ≠ g.eval 0 + g.eval 1) :
    uniformProb F (fun r => gp.eval r = g.eval r) ≤ (d : ℝ) / Fintype.card F := by
  have hcard := sumcheckRound_sound hg hgp hcheck hfalse
  have hconv : uniformProb F (fun r => gp.eval r = g.eval r)
      = uniformProb F (fun x => x ∈ agreeFinset gp g) :=
    uniformProb_congr (fun x => mem_agreeFinset.symm)
  rw [hconv, uniformProb_mem_finset]
  gcongr

/-! ## The claim / truth chains and the lie-persistence reduction

A `v`-round run threads two chains of field values: the prover's `claim` chain
(`claim 0 = H`, `claim (i+1) = g̃ᵢ(rᵢ)` — the fold) and the honest `truth` chain
(`tru 0 = S`, `tru (i+1) = gᵢ(rᵢ)`). The fold is memoryless — the next value is
the round polynomial at the challenge, independent of the running value — so the
chains are a plain case split, not a recursion. -/

/-- The fold chain: `base` at round 0, and `polyᵢ(chalᵢ)` at round `i+1`. Models
both the prover's claim chain (`base = H`, `poly = g̃`) and the honest truth chain
(`base = S`, `poly = g`). -/
def scChain (base : F) (poly : ℕ → Polynomial F) (chal : ℕ → F) : ℕ → F
  | 0 => base
  | (i + 1) => (poly i).eval (chal i)

/-- Read the challenge tuple `r : Fin v → F` as a total function `ℕ → F` (junk
`0` past the horizon; never queried in range). -/
def chalOf {v : ℕ} (r : Fin v → F) (i : ℕ) : F :=
  if h : i < v then r ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
@[simp] theorem chalOf_coe {v : ℕ} (r : Fin v → F) (i : Fin v) : chalOf r i.val = r i := by
  rw [chalOf, dif_pos i.isLt]

omit [Fintype F] [DecidableEq F] in
/-- **Lie persistence.** If no round `j < v` launders the lie — i.e. never both
the incoming claim is wrong *and* the fold value matches the truth — then a
false initial claim stays false through every round `i ≤ v`. Elementary
induction on `i`; each step turns "claim wrong at `i`, no laundering at `i`" into
"fold values differ", hence "claim wrong at `i+1`". -/
theorem lie_persists {v : ℕ} {prover honest : ℕ → Polynomial F} {chal : ℕ → F}
    {claimF truF : ℕ → F}
    (hcf : ∀ i, i < v → claimF (i + 1) = (prover i).eval (chal i))
    (htf : ∀ i, i < v → truF (i + 1) = (honest i).eval (chal i))
    (h0 : claimF 0 ≠ truF 0)
    (hno : ∀ j, j < v →
      ¬ (claimF j ≠ truF j ∧ (prover j).eval (chal j) = (honest j).eval (chal j))) :
    ∀ i, i ≤ v → claimF i ≠ truF i := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hle
    have hnv : n < v := hle
    have hclaimn : claimF n ≠ truF n := ih (Nat.le_of_succ_le hle)
    have hnag : (prover n).eval (chal n) ≠ (honest n).eval (chal n) := fun hag =>
      hno n hnv ⟨hclaimn, hag⟩
    rw [hcf n hnv, htf n hnv]
    exact hnag

omit [Fintype F] [DecidableEq F] in
/-- **Soundness reduction (per transcript).** If the verifier accepts (all fold
recurrences hold and the final claim matches the truth) on a false initial
claim, then some round `j < v` laundered the lie: the claim was still wrong there
and the fold value matched the truth. Contrapositive of `lie_persists`. -/
theorem sumcheck_reduction {v : ℕ} {prover honest : ℕ → Polynomial F} {chal : ℕ → F}
    {claimF truF : ℕ → F}
    (hcf : ∀ i, i < v → claimF (i + 1) = (prover i).eval (chal i))
    (htf : ∀ i, i < v → truF (i + 1) = (honest i).eval (chal i))
    (h0 : claimF 0 ≠ truF 0) (hfinal : claimF v = truF v) :
    ∃ j, j < v ∧ claimF j ≠ truF j
        ∧ (prover j).eval (chal j) = (honest j).eval (chal j) := by
  by_contra hc
  have hno : ∀ j, j < v →
      ¬ (claimF j ≠ truF j ∧ (prover j).eval (chal j) = (honest j).eval (chal j)) :=
    fun j hj hcontra => hc ⟨j, hj, hcontra⟩
  exact lie_persists hcf htf h0 hno v (le_refl v) hfinal

/-! ## The v-round protocol and its union-bound soundness -/

/-- Round `i`'s **lie-laundering event**: the round check passes, the incoming
claim is still false, and the fold value matches the truth (`g̃ᵢ(rᵢ) = gᵢ(rᵢ)`) —
the event that turns the lie into a true sub-claim. -/
def LaunderEvent {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F)
    (i : Fin v) (r : Fin v → F) : Prop :=
  (prover i.val).eval 0 + (prover i.val).eval 1 = scChain H prover (chalOf r) i.val
    ∧ scChain H prover (chalOf r) i.val ≠ scChain S honest (chalOf r) i.val
    ∧ (prover i.val).eval (chalOf r i.val) = (honest i.val).eval (chalOf r i.val)

/-- The verifier **accepts a false claim**: every round check passes, the final
folded claim equals the truth, and the initial claimed sum `H` is wrong
(`H ≠ S`, the true sum). -/
def AcceptsFalse {v : ℕ} (prover honest : ℕ → Polynomial F) (H S : F)
    (r : Fin v → F) : Prop :=
  (∀ i, i < v → (prover i).eval 0 + (prover i).eval 1 = scChain H prover (chalOf r) i)
    ∧ scChain H prover (chalOf r) v = scChain S honest (chalOf r) v
    ∧ H ≠ S

/-- **v-round sumcheck soundness (fixed round polynomials).** For a run whose
honest polynomials `gᵢ = honest i` and prover polynomials `g̃ᵢ = prover i` have
degree `≤ d` and satisfy the honest boolean-sum consistency `gᵢ(0)+gᵢ(1) = truthᵢ`
(the true partial sums), the probability over a uniform challenge vector
`r ∈ Fⱽ` that the verifier accepts an initially-false claim is at most `v·d/|F|`.

Proof: `sumcheck_reduction` forces acceptance to launder the lie at some round
(each `LaunderEvent`); a union bound (`uniformProb_exists_le`) over the `v` rounds,
with each round's laundering probability `≤ d/|F|` (root counting for a false
round, impossible for a truthful one), gives the bound. -/
theorem sumcheck_soundness {v d : ℕ} {prover honest : ℕ → Polynomial F} {H S : F}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf r) i) :
    uniformProb (Fin v → F) (AcceptsFalse prover honest H S)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  -- Step 1: acceptance of a false claim launders the lie at some round.
  have hstep1 : ∀ r : Fin v → F,
      AcceptsFalse prover honest H S r →
        ∃ i : Fin v, LaunderEvent prover honest H S i r := by
    rintro r ⟨hchecks, hfinal, hfalse⟩
    obtain ⟨j, hj, hne, hag⟩ :=
      sumcheck_reduction (v := v) (prover := prover) (honest := honest)
        (chal := chalOf r) (claimF := scChain H prover (chalOf r))
        (truF := scChain S honest (chalOf r)) (fun i _ => rfl) (fun i _ => rfl)
        hfalse hfinal
    exact ⟨⟨j, hj⟩, hchecks j hj, hne, hag⟩
  -- Step 3: each round's laundering probability is at most d/|F|.
  have hstep3 : ∀ i : Fin v,
      uniformProb (Fin v → F) (LaunderEvent prover honest H S i)
        ≤ (d : ℝ) / Fintype.card F := by
    intro i
    by_cases hpe : prover i.val = honest i.val
    · -- a truthful round cannot launder a false claim: the event is empty.
      rw [uniformProb_false]
      · positivity
      · rintro r ⟨hchk, hne', _⟩
        exact hne' (by rw [← hchk, hpe, hHonest r i.val i.isLt])
    · -- a false round agrees at ≤ d challenges (root counting).
      have hlt := card_agreeFinset_lt (hProverDeg i.val i.isLt) (hHonestDeg i.val i.isLt) hpe
      have hcard : (agreeFinset (prover i.val) (honest i.val)).card ≤ d := by omega
      calc uniformProb (Fin v → F) (LaunderEvent prover honest H S i)
          ≤ uniformProb (Fin v → F)
              (fun r => r i ∈ agreeFinset (prover i.val) (honest i.val)) := by
            apply uniformProb_mono
            intro r hr
            rw [mem_agreeFinset, ← chalOf_coe r i]
            exact hr.2.2
        _ ≤ ((agreeFinset (prover i.val) (honest i.val)).card : ℝ) / Fintype.card F :=
            uniformProb_coord_mem i _
        _ ≤ (d : ℝ) / Fintype.card F := by gcongr
  -- Combine: reduction ▸ union bound ▸ per-round bound.
  calc uniformProb (Fin v → F) (AcceptsFalse prover honest H S)
      ≤ uniformProb (Fin v → F)
          (fun r => ∃ i : Fin v, LaunderEvent prover honest H S i r) :=
        uniformProb_mono hstep1
    _ ≤ ∑ i : Fin v, uniformProb (Fin v → F) (LaunderEvent prover honest H S i) :=
        uniformProb_exists_le _
    _ ≤ ∑ _i : Fin v, (d : ℝ) / Fintype.card F := Finset.sum_le_sum fun i _ => hstep3 i
    _ = (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## The reusable fixed union-bound engine

The tail of `sumcheck_soundness`, isolated: `v` per-round bad sets of size `≤ d`
give a total laundering probability `≤ v·d/|F|`. Reuses `uniformProb_exists_le`
(the union bound) and `uniformProb_coord_mem` (per-coordinate counting). -/

omit [DecidableEq F] in
/-- **Fixed union bound.** For challenge-independent bad sets `bad i` (each of
size `≤ d`), the probability that a uniform challenge tuple hits some round's bad
set is `≤ v·d/|F|`. -/
theorem unionBound_fixed {v d : ℕ} (bad : Fin v → Finset F)
    (hcard : ∀ i, (bad i).card ≤ d) :
    uniformProb (Fin v → F) (fun r => ∃ i : Fin v, r i ∈ bad i)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
  calc uniformProb (Fin v → F) (fun r => ∃ i : Fin v, r i ∈ bad i)
      ≤ ∑ i : Fin v, uniformProb (Fin v → F) (fun r => r i ∈ bad i) :=
        uniformProb_exists_le _
    _ ≤ ∑ _i : Fin v, (d : ℝ) / Fintype.card F :=
        Finset.sum_le_sum fun i _ =>
          le_trans (uniformProb_coord_mem i (bad i)) (by gcongr; exact_mod_cast hcard i)
    _ = (v : ℝ) * ((d : ℝ) / Fintype.card F) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## Keystone obligation: the fully-adaptive union bound

`sumcheck_soundness` fixes the round polynomials up front. A fully adaptive
prover chooses round `i`'s message from the challenge prefix `r|_{<i}`; the union
bound still holds, but its per-round step must condition on the prefix. That
generalization is stated here as an obligation and NOT discharged — its
challenge-independent case is `unionBound_fixed` (proved), which fires on nonempty
laundering sets, so the obligation is a genuine, non-vacuous statement. -/

/-- **OB-SC (fully-adaptive sumcheck union bound).** Round `i`'s laundering set
`bad r i` may depend on `r`, but only through the prefix `r|_{<i}`
(prefix-measurability). If every such set has `≤ d` elements, some round is
laundered with probability `≤ v·d/|F|`. The prefix-independent case is proved
(`unionBound_fixed`); the general case is the sumcheck front's obligation
(dischargeable by the fibrewise `uniformProb_prod_le` per round). -/
def AdaptiveUnionBound (F : Type) [Field F] [Fintype F] (v d : ℕ) : Prop :=
  ∀ bad : (Fin v → F) → Fin v → Finset F,
    (∀ (i : Fin v) (r r' : Fin v → F),
      (∀ j : Fin v, (j : ℕ) < (i : ℕ) → r j = r' j) → bad r i = bad r' i) →
    (∀ (r : Fin v → F) (i : Fin v), (bad r i).card ≤ d) →
    uniformProb (Fin v → F) (fun r => ∃ i : Fin v, r i ∈ bad r i)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F)

omit [DecidableEq F] in
/-- **Teeth for `AdaptiveUnionBound`.** Its conclusion holds for every
challenge-INDEPENDENT bad function (a genuine sub-class of its quantifier — every
constant `bad` is prefix-measurable), discharged by `unionBound_fixed`. So the
obligation is satisfiable and non-vacuous, with its fixed case proved. -/
theorem adaptiveUnionBound_fixedCase {v d : ℕ} (b : Fin v → Finset F)
    (hb : ∀ i, (b i).card ≤ d) :
    uniformProb (Fin v → F) (fun r => ∃ i : Fin v, r i ∈ (fun _r => b) r i)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
  unionBound_fixed b hb

/-! ## Teeth: the round bound fires on a concrete nonempty laundering set

Over `F₅`, honest `g = 0`, prover `g̃ = X`, claimed sum `H = 1` (the true sum is
`0`, so the claim is false). The check `g̃(0)+g̃(1) = 0+1 = 1 = H` passes, `g̃ ≠ g`,
and the fold agrees exactly at `x = 0`: the round bound `card ≤ d = 1` fires, and
the laundering set is nonempty — the `d/|F| = 1/5` soundness bound is a real,
positive constraint, not vacuous. -/

namespace SumcheckExample

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The round bound fires: `#(agreeFinset X 0) ≤ 1` via `sumcheckRound_sound` with
every hypothesis (degrees, check, false claim) discharged. -/
example : (agreeFinset (X : Polynomial (ZMod 5)) 0).card ≤ 1 :=
  sumcheckRound_sound (d := 1) (H := 1)
    (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [Polynomial.degree_X]; decide)
    (by simp)
    (by simp)

/-- The laundering set is nonempty: `x = 0` launders (`X.eval 0 = 0 = (0).eval 0`),
so the round soundness bound is non-vacuous. -/
example : (0 : ZMod 5) ∈ agreeFinset (X : Polynomial (ZMod 5)) 0 := by
  simp [mem_agreeFinset]

end SumcheckExample

end Minidregg.Loom

