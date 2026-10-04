/-
# `Theory.CertF` — the Cert-F weak-duality certificate: duality gap ⇒ ε-optimality

The verify side of an untrusted clearing solver. For the volume-max circulation LP

    maximize   wᵀf     subject to   A f = 0,   0 ≤ f ≤ c

(`A` the public incidence matrix of the trade graph, `w` volume weights, `c` capacities) a
primal-dual triple `(f, π, s)` satisfying the LINEAR certificate

    A f = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε

certifies that `f` is ε-optimal, independent of how the triple was found. The solver (PDHG/ADMM,
any heuristic) is an untrusted search; this module is the checked output (ATLAS §3 item 1, the
verify/find seam of `Theory.Knowledge`). Generic over any ordered commutative ring.

* `weak_duality` — `wᵀf ≤ cᵀs` for every primal-feasible `f` and dual-feasible `(π, s)`.
* `certifies_epsilon_optimal` — a certificate with gap `≤ ε` bounds every feasible flow by
  `wᵀf + ε`.
* `gap_nonneg` — a certified gap is nonnegative.
* Worked 3-cycle: an ACCEPTING instance (`ringCert_valid`, gap `0` at `ε = 0`) and REFUSING
  instances (`leakF_infeasible`: non-conserving flow; `zeroFlow_gap_refused`: gap `3 > ε = 0`;
  `zeroFlow_refused_at_two` / `zeroFlow_certified_at_three`: the same triple refused at `ε = 2`
  and accepted at `ε = 3`, the boundary pinned in both polarities).

**What this does not do.** It proves the CHECK sound; it says nothing about finding an optimum
(exact all-or-nothing clearing is NP-hard; the certified program is the `[0,1]` partial-fill
relaxation). It does not emit a circuit: Bread's §6 (the `Dregg2.Circuit` emit half, BabyBear AIR
constraints) is dropped, and Mini's admission does not verify proofs.

**The consumer it awaits.** A DrEX settlement plan on the Core4 surface: the clearing turn's
settlement plan must carry `(f, π, s)` and its admission must run this check before the plan's
transfers apply. The old `.bend` DrEX sources are being deleted; until the Core4 DrEX plan exists,
nothing in Mini invokes this module, and it claims no deployment.

**Port provenance (Mini, 2026-10-04).** Sections 1–5 copied from breadstuffs
`metatheory/Market/CertF.lean` (sha256 `f75e10adfc4f41c0239d3b497261b78683fcd45719568eabf46dbdf44df202b4`), renamespaced `Market` → `Minidregg.Theory.CertF`;
statements and proofs unchanged. Dropped: §6 (emit half, imports `Dregg2.Circuit`) and the
`#guard` smoke lines (replaced by the named theorems `ringF_value` and `zeroFlow_gap_value`).
Added: `ringLPAt`, `zeroFlow_refused_at_two`, `zeroFlow_certified_at_three`.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Minidregg.Theory.CertF

open Matrix

/-! ## 1. The volume-max circulation LP (public `A`, private amounts). -/

variable {V E : Type*} [Fintype V] [Fintype E]
variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- **The volume-max circulation LP** `max wᵀf s.t. Af=0, 0≤f≤c` — the canonical dregg program of
`PRIVATE-CONVEX-ENGINE.md §2.3`. `A` is the **public incidence matrix** of the trade graph (vertices `V`
× edges `E`); `w` (volume weights), `c` (capacities), and the certified `f` (edge flows) are the private
amounts. `ε` is the public accuracy target. -/
structure FlowLP (V E R : Type*) where
  /-- The public incidence matrix `A = ∂` of the trade graph. Conservation is `A f = 0`. -/
  A : Matrix V E R
  /-- Per-edge volume weights (the objective `max wᵀf`). -/
  w : E → R
  /-- Per-edge capacities (the box `0 ≤ f ≤ c`). -/
  c : E → R
  /-- The public accuracy target (`gap ≤ ε` ⇒ `ε`-optimal). -/
  ε : R

/-- **Primal feasibility** — `f` is a capacity-respecting circulation: conserves at every node
(`A f = 0`), and lies in the box `0 ≤ f ≤ c`. -/
def PrimalFeasible (lp : FlowLP V E R) (f : E → R) : Prop :=
  lp.A *ᵥ f = 0 ∧ 0 ≤ f ∧ f ≤ lp.c

/-- **Dual feasibility** — node potentials `π` and slacks `s` with `s ≥ 0` and `Aᵀπ + s ≥ w`
(the dual of the box-constrained circulation). `π ᵥ* A` is `Aᵀπ`. -/
def DualFeasible (lp : FlowLP V E R) (π : V → R) (s : E → R) : Prop :=
  0 ≤ s ∧ lp.w ≤ π ᵥ* lp.A + s

/-- **A `Cert-F` certificate** — a primal-dual triple whose duality gap is `≤ ε`. The ENTIRE object the
hidden proof checks; sound ⇒ `f` is `ε`-optimal (`certifies_epsilon_optimal`), independent of how the
triple was found. -/
def Certified (lp : FlowLP V E R) (f : E → R) (π : V → R) (s : E → R) : Prop :=
  PrimalFeasible lp f ∧ DualFeasible lp π s ∧ lp.c ⬝ᵥ s - lp.w ⬝ᵥ f ≤ lp.ε

/-! ## 2. Weak duality — the linear inequality every feasible pair satisfies. -/

/-- **`weak_duality` — `wᵀf ≤ cᵀs` for EVERY feasible primal `f` and dual `(π, s)`.** The load-bearing
lemma: the objective at any feasible flow is bounded by the dual value at any dual-feasible point, using
NOTHING about how either was obtained. The four moves:

  * `wᵀf ≤ (Aᵀπ + s)ᵀf` — dual feasibility `w ≤ Aᵀπ + s` scaled by `f ≥ 0`;
  * `(Aᵀπ + s)ᵀf = πᵀ(Af) + sᵀf` — linearity (`Aᵀπ ⬝ f = π ⬝ Af`);
  * `= sᵀf` — primal conservation `Af = 0`;
  * `sᵀf ≤ sᵀc = cᵀs` — the box `f ≤ c` scaled by `s ≥ 0`.

This is the whole of verify-not-find for convex clearing: a certificate is sound because weak duality
sandwiches the optimum, and weak duality reads only the two feasibilities. -/
theorem weak_duality (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s) :
    lp.w ⬝ᵥ f ≤ lp.c ⬝ᵥ s :=
  calc lp.w ⬝ᵥ f
      ≤ (π ᵥ* lp.A + s) ⬝ᵥ f := dotProduct_le_dotProduct_of_nonneg_right hd.2 hf.2.1
    _ = (π ᵥ* lp.A) ⬝ᵥ f + s ⬝ᵥ f := add_dotProduct _ _ _
    _ = π ⬝ᵥ (lp.A *ᵥ f) + s ⬝ᵥ f := by rw [← dotProduct_mulVec]
    _ = s ⬝ᵥ f := by rw [hf.1, dotProduct_zero, zero_add]
    _ ≤ s ⬝ᵥ lp.c := dotProduct_le_dotProduct_of_nonneg_left hf.2.2 hd.1
    _ = lp.c ⬝ᵥ s := dotProduct_comm _ _

/-! ## 3. THE KEYSTONE — a `Cert-F` certificate ⇒ ε-optimality (verify-not-find). -/

/-- **`certifies_epsilon_optimal` — the certificate CERTIFIES `f` is ε-optimal.** Given a `Certified`
triple `(f, π, s)` (gap `≤ ε`), EVERY primal-feasible `f'` obeys `wᵀf' ≤ wᵀf + ε`: no feasible flow can
out-score the certified one by more than `ε`. The proof reads ONLY the certificate — `weak_duality`
applied to `f'` against the certificate's OWN dual `(π, s)` gives `wᵀf' ≤ cᵀs`, and the gap gives `cᵀs ≤
wᵀf + ε`. **Independent of how `(f, π, s)` was found** — the untrusted solver's search is never
re-examined; the linear certificate stands alone. This is the "checked output" half of the fhEgg
engine. -/
theorem certifies_epsilon_optimal (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hcert : Certified lp f π s) {f' : E → R} (hf' : PrimalFeasible lp f') :
    lp.w ⬝ᵥ f' ≤ lp.w ⬝ᵥ f + lp.ε := by
  obtain ⟨_, hd, hgap⟩ := hcert
  have h1 : lp.w ⬝ᵥ f' ≤ lp.c ⬝ᵥ s := weak_duality lp hf' hd
  have h2 : lp.c ⬝ᵥ s ≤ lp.ε + lp.w ⬝ᵥ f := sub_le_iff_le_add.mp hgap
  calc lp.w ⬝ᵥ f' ≤ lp.c ⬝ᵥ s := h1
    _ ≤ lp.ε + lp.w ⬝ᵥ f := h2
    _ = lp.w ⬝ᵥ f + lp.ε := by rw [add_comm]

/-- **`gap_nonneg` — a certified gap is `≥ 0`.** Weak duality at the certified `f` against its own dual
gives `wᵀf ≤ cᵀs`, i.e. `cᵀs − wᵀf ≥ 0`. So a "certificate" asserting a strictly negative gap is
impossible, and the target `ε` it certifies is forced `≥ 0`. -/
theorem gap_nonneg (lp : FlowLP V E R) {f : E → R} {π : V → R} {s : E → R}
    (hf : PrimalFeasible lp f) (hd : DualFeasible lp π s) :
    0 ≤ lp.c ⬝ᵥ s - lp.w ⬝ᵥ f :=
  sub_nonneg.mpr (weak_duality lp hf hd)

/-! ## 4. NON-VACUITY, positive polarity — the worked 3-cycle circulation (over `ℤ`).

The directed triangle `0→1→2→0`, edges `e0,e1,e2`. The incidence `A` (row = vertex, `+1` in-edge,
`−1` out-edge) makes `A f = 0` the node-conservation "in = out". A uniform flow `f = (1,1,1)` circulates;
capacities `c = (1,1,1)` cap it; weights `w = (1,1,1)` (`wᵀf` = total volume). The optimum is `f =
(1,1,1)`, value `3`. Dual certificate `π = 0`, `s = (1,1,1)` gives `cᵀs = 3 = wᵀf` — a TIGHT (`gap = 0`)
certificate of the exact optimum. -/

/-- The `3×3` incidence matrix of the directed triangle `0→1→2→0` (rows = vertices, cols = edges):
edge `e` leaves vertex `e` (`−1`) and enters vertex `e+1 (mod 3)` (`+1`). So the columns are
`e₀=[-1,1,0]ᵀ`, `e₁=[0,-1,1]ᵀ`, `e₂=[1,0,-1]ᵀ`, and `A f = 0` ⇔ `f` is a circulation (in = out at
every node). -/
def ringA : Matrix (Fin 3) (Fin 3) ℤ := fun i e =>
  if i = e then -1 else if (i : ℕ) = ((e : ℕ) + 1) % 3 then 1 else 0

/-- The worked circulation LP: unit weights, unit capacities, exact target `ε = 0` (certify the true
optimum, not merely ε-close). -/
def ringLP : FlowLP (Fin 3) (Fin 3) ℤ :=
  { A := ringA, w := fun _ => 1, c := fun _ => 1, ε := 0 }

/-- The optimal circulation: one unit of flow all the way around the cycle. -/
def ringF : Fin 3 → ℤ := fun _ => 1
/-- The dual potentials — all zero (the triangle is balanced). -/
def ringπ : Fin 3 → ℤ := fun _ => 0
/-- The dual slacks — one per edge, saturating `Aᵀπ + s ≥ w` at `s = w`. -/
def ringS : Fin 3 → ℤ := fun _ => 1

/-- **THE CERTIFICATE VERIFIES — the worked triple is `Certified` with gap exactly `0`.** `f = (1,1,1)`
is a capacity-respecting circulation, `(π, s) = (0, (1,1,1))` is dual-feasible, and `cᵀs − wᵀf = 3 − 3 =
0 ≤ ε = 0`. A concrete, non-vacuous `Cert-F` certificate of a real optimum. -/
theorem ringCert_valid : Certified ringLP ringF ringπ ringS := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · funext i; fin_cases i <;>
      simp [ringLP, ringA, ringF, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro i; fin_cases i <;> simp [ringF]
  · intro i; fin_cases i <;> simp [ringLP, ringF]
  · intro i; fin_cases i <;> simp [ringS]
  · intro i; fin_cases i <;>
      simp [ringLP, ringA, ringπ, ringS, Matrix.vecMul, dotProduct]
  · simp [ringLP, ringF, ringS, dotProduct]

/-- **THE KEYSTONE, INSTANTIATED — the certificate proves `(1,1,1)` is optimal.** Every primal-feasible
`f'` has `wᵀf' ≤ wᵀ(1,1,1) + 0 = 3`: no circulation in the unit box beats a total volume of `3`.
`certifies_epsilon_optimal` on the worked certificate — the untrusted solver's `(1,1,1)` is proven
optimal by the linear certificate alone. -/
theorem ringF_optimal {f' : Fin 3 → ℤ} (hf' : PrimalFeasible ringLP f') :
    ringLP.w ⬝ᵥ f' ≤ 3 := by
  have h := certifies_epsilon_optimal ringLP ringCert_valid hf'
  simpa [ringLP, ringF, dotProduct, Fin.sum_univ_three] using h

/-! ## 5. NON-VACUITY, negative polarity — the teeth (an unsound triple is REFUSED). -/

/-- A NON-CONSERVING flow: `1` on edge `e0` only. `A f`'s node-0 row reads `−1 ≠ 0` (flow leaves node 0
and never returns) — not a circulation. -/
def leakF : Fin 3 → ℤ := fun e => if e = 0 then 1 else 0

/-- **TOOTH (conservation): a non-circulating `f` is REFUSED.** `leakF` puts flow on one edge with no
return leg, so `A f ≠ 0` — it fails `PrimalFeasible`, hence cannot anchor any certificate. The
conservation half of `Cert-F` has real refusing power: value cannot leak out of the cycle. -/
theorem leakF_infeasible : ¬ PrimalFeasible ringLP leakF := by
  rintro ⟨hAf, -, -⟩
  have h0 := congrFun hAf 0
  simp [ringLP, ringA, leakF, Matrix.mulVec, dotProduct] at h0

/-- **TOOTH (the certificate cannot certify a NON-OPTIMAL `f`).** Suppose the zero flow `f = 0` (feasible,
value `0`) carried a `Cert-F` certificate at `ε = 0`. Then `certifies_epsilon_optimal` would force EVERY
feasible `f'` to score `≤ 0` — but the genuine circulation `(1,1,1)` scores `3 > 0`. So NO dual can
certify the sub-optimal zero flow as optimal: the certificate is sound in the strong sense that it
refuses to certify a flow that is not actually ε-best. (`0` is `PrimalFeasible` — a real feasible point,
not a straw man.) -/
theorem zeroFlow_not_certifiable (π s : Fin 3 → ℤ) :
    ¬ Certified ringLP (fun _ => 0) π s := by
  intro hcert
  have hf' : PrimalFeasible ringLP ringF := ringCert_valid.1
  have h := certifies_epsilon_optimal ringLP hcert hf'
  -- h : 3 ≤ 0 + 0, refuted by simp
  simp [ringLP, ringF, dotProduct] at h

/-- **TOOTH (gap > ε): an off-optimal primal with a valid dual is REFUSED.** Pair the zero flow with the
honest dual `(π, s) = (0, (1,1,1))`: it is primal- and dual-feasible, but `cᵀs − wᵀf = 3 − 0 = 3 > 0 =
ε`, so the gap clause fails — not `Certified`. A large duality gap is exactly the certificate detecting
"this flow is `3` short of optimal." -/
theorem zeroFlow_gap_refused : ¬ Certified ringLP (fun _ => 0) ringπ ringS :=
  zeroFlow_not_certifiable ringπ ringS

/-! ## 6. Named values (the former `#guard` smoke lines) and the boundary in both polarities -/

/-- The objective at the certified optimum is `3`. -/
theorem ringF_value : ringLP.w ⬝ᵥ ringF = 3 := by
  simp [ringLP, ringF, dotProduct, Fin.sum_univ_three]

/-- The zero flow against the honest dual has gap exactly `3`: how far it is from optimal. -/
theorem zeroFlow_gap_value : ringLP.c ⬝ᵥ ringS - ringLP.w ⬝ᵥ (fun _ => (0 : ℤ)) = 3 := by
  simp [ringLP, ringS, dotProduct, Fin.sum_univ_three]

/-- The worked LP at accuracy target `ε`. -/
def ringLPAt (ε : ℤ) : FlowLP (Fin 3) (Fin 3) ℤ := { ringLP with ε := ε }

/-- **Refused at the boundary:** the zero flow with the honest dual is primal- and dual-feasible,
but its gap `3` exceeds `ε = 2`, so the triple is not a certificate. -/
theorem zeroFlow_refused_at_two : ¬ Certified (ringLPAt 2) (fun _ => 0) ringπ ringS := by
  rintro ⟨-, -, hgap⟩
  simp [ringLPAt, ringLP, ringS, dotProduct, Fin.sum_univ_three] at hgap

/-- **Accepted at the boundary:** the same triple certifies the zero flow `3`-optimal at `ε = 3`,
and the keystone then bounds every feasible flow by `3` — which the true optimum attains. -/
theorem zeroFlow_certified_at_three : Certified (ringLPAt 3) (fun _ => 0) ringπ ringS := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · funext i; fin_cases i <;> simp [ringLPAt, ringLP, Matrix.mulVec, dotProduct]
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp [ringLPAt, ringLP]
  · intro i; fin_cases i <;> simp [ringS]
  · intro i; fin_cases i <;>
      simp [ringLPAt, ringLP, ringA, ringπ, ringS, Matrix.vecMul, dotProduct]
  · simp [ringLPAt, ringLP, ringS, dotProduct, Fin.sum_univ_three]

#print axioms weak_duality
#print axioms certifies_epsilon_optimal
#print axioms gap_nonneg
#print axioms ringCert_valid
#print axioms ringF_optimal
#print axioms leakF_infeasible
#print axioms zeroFlow_not_certifiable
#print axioms zeroFlow_gap_refused
#print axioms ringF_value
#print axioms zeroFlow_gap_value
#print axioms zeroFlow_refused_at_two
#print axioms zeroFlow_certified_at_three

end Minidregg.Theory.CertF
