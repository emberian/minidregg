# N2 — the turn is a limit (hyperedge universality)

*Design, 2026-08-07, under the goal. KERNEL-NECESSITY §N2: any N-party atomic-update
object satisfying the cone condition with derivable pairwise consistency IS a cone; the
hyperedge is the universal such object — the LIMIT. This note fixes the category and the
statement BEFORE the Lean, because §N1's warning applies — "getting the category right is
the whole game" — and a rushed universal-property statement is the OB-2 trap (a wrong
statement proved fast). Design-first, then author the Lean statement with keystone fields,
then fan out the proof.*

## 0. What is already built (Kernel/Turn.lean)

- `Hyperedge` — the structure: participant tuple `x`, shared turn `t`, apex `tid`, the
  cone condition `agree : ∀ i, turnId i (step (x i) t) = tid`, and `balanced`.
- `legs_agree` — pairwise agreement is a THEOREM from the one apex (the equalizer content).
- `binding_is_proper` — a configuration can satisfy `agree` yet FAIL `balanced`.

N2 says: among all cones over the turn diagram, the hyperedge is the limit. And
`binding_is_proper` is *already N2's teeth in embryo* — it exhibits a cone (agree holds)
that is not a valid hyperedge (balanced fails), i.e. a cone that does not factor as a
limit cone of the CONSERVING diagram. The two results compose.

## 1. The category and the diagram (the crux to get right)

Two honest candidates for what N2 means; pick the one whose universal property is
non-vacuous and whose limit IS the hyperedge, not merely admits it.

**Candidate A — the apex cone in `Type` (the literal wide pullback).**
Diagram shape `J`: the wide cospan — objects `{leg i | i : ι} ∪ {apex}`, one morphism
`leg i → apex` each. Functor `D : J ⥤ Type`: `D(leg i) = Carrier` (participant states),
`D(apex) = TurnId`, `D(leg i → apex) = (turnId i ∘ step · t)` for a FIXED turn `t`. The
wide pullback `∏_{apex} D(leg i)` is `{ (xᵢ) | ∀ i, turnId i (step xᵢ t) = tid for a common
tid }` — exactly `Hyperedge`'s `(x, agree)` at fixed `t`. IsLimit gives the universal
property: any cone (any tuple with a common apex image) factors uniquely.
*Verdict:* clean and true, but it captures only the CONE half (`agree`); `balanced` is
extra structure the plain limit does not see. So Candidate A proves "the agreement
bookkeeping is a limit" — real, but it is the part `legs_agree` already trivializes.

**Candidate B — the conserving hyperedge as a limit in a category of BALANCED cones.**
Enrich: objects are cones carrying a half-edge assignment; morphisms preserve it; the
limit is the cone whose half-edge sum is `0`. Here the limit genuinely IS the hyperedge
(balanced included), and `binding_is_proper` is the teeth: the `Σ=1` cone is an object of
the ambient category that does NOT map to the limit (no morphism to a `Σ=0` object that
preserves the nonzero sum). *Verdict:* this is the N2 with content — the limit sees
`balanced`, so universality is not just the agreement half. But it needs the enriched
category defined carefully (the half-edge as part of the object, the morphism law that
makes `Σ=0` terminal among cones). This is where §N1's "get the category right" bites.

**Decision:** state BOTH, layered. N2a = Candidate A (the wide-pullback cone in `Type`;
`Hyperedge`-at-fixed-`t` ≅ the limit; proof is the mathlib `Types.isLimit` for the wide
cospan — cheap, true, and it discharges the "pairwise agreement is universal not
pairwise" claim rigorously). N2b = Candidate B (the balanced limit; the hyperedge with
conservation IS the universal conserving cone). N2a is the near-term Lean target
(fan-outable); N2b is the deeper statement whose category is designed here and authored
after N2a lands. Do not conflate them — labeling N2b's content as proved when only N2a is
built would be the reach OB-2 punished.

## 2. The statement to author (N2a, near-term)

```
-- shape: the wide cospan over ι (mathlib: WidePullbackShape ι, or a hand functor)
-- D : WidePullbackShape ι ⥤ Type, legs ↦ Carrier, apex ↦ TurnId, arrow i ↦ (turnId i ∘ step·t)
-- claim: the type { x : ι → Carrier // ∃ tid, ∀ i, turnId i (step (x i) t) = tid }
--        (= Hyperedge's cone data at fixed t) is a limit of D.
def turnDiagram (t : Turn) : WidePullbackShape ι ⥤ Type u := …
theorem hyperedge_is_wide_pullback (t : Turn) :
    IsLimit (hyperedgeCone t)        -- the cone built from Hyperedge.x + Hyperedge.agree
```

**Keystone fields (BUILT, per the audit lesson):**
- *satisfiable:* a concrete `ι = Fin 2`, `Carrier = ℤ`, a `t` and a tuple where the limit
  cone is inhabited — the transfer, exhibited.
- *teeth:* `binding_is_proper` reused — a cone that does not lie in the CONSERVING limit
  (N2b's teeth), plus for N2a a tuple with NO common apex (agree fails for any tid) that
  is therefore not a cone point, showing the limit condition is a real constraint.
- *premise-inhabitation:* the diagram `D` is a genuine functor (identities/composition
  hold — `WidePullbackShape` gives this) over a nonempty `ι`.

## 3. The no-free-completion conjecture (N2, the deep half — record, don't rush)

HYPEREDGE-DESIGN §3's third wall, `sound_bisim_ill_posed`, in categorical dress: the
forgetful functor from lawful turn-models to free spec-models has NO left adjoint (there
is no free completion that adds conservation for free). This is the categorical form of
"no abstract sibling spec" and is a genuine research conjecture — stated here as the
horizon, NOT a near-term target. It is refuted-in-embryo by the `Empty`-carrier witness
[N-TURN-b]. Attempt only after N2a + N2b are green.

## 4. Next action

Author `Kernel/TurnLimit.lean` with N2a statement-first (keystone fields built), fan out
the mathlib `WidePullbackShape`/`Types.isLimit` proof (a bounded, mathlib-only lane — safe
from the large-file stall). Then design N2b's balanced category in this doc's §1 into Lean.
`binding_is_proper` is already the teeth; do not re-derive it.
