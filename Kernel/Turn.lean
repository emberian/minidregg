/-
# `Kernel/Turn.lean` — the turn is a wide pullback (the hyperedge)

Minidregg has ONE turn model: the hyperedge (`docs/HYPEREDGE-DESIGN.md`). A turn is a
wide pullback (N-fold fiber product over a shared apex id) of the participants'
`turnId ∘ step` maps, packaged with the per-asset conservation aggregate. A single-cell
action is the `ι = 1` slice; a transfer is `ι = 2`; an N-party joint turn is `ι = N` —
the *same object*, no special shape.

This is the CLEAN abstract form, not a transcription of breadstuffs'
`Dregg2/Hyperedge.lean` (which drags in the full `TurnCoalg`/`TurnIdOf`/`Bal` tree — the
debt). We parameterize over exactly the four data the wide pullback needs: a `Carrier`
(participant pre-states), a `Turn`, an apex-id type `TurnId`, and a balance monoid `Bal`,
with the two per-incidence projections `step`/`turnId`/`halfEdge`. `Kernel/State.lean`'s
kernel state instantiates `Carrier`; nothing here depends on it, so the two compose
without a merge.

Scope landed (honest): the structure, `legs_agree` (pairwise agreement as a THEOREM, not
C(N,2) data), the binary slice, and `binding_is_proper` — the load-bearing negative that
makes the conservation aggregate genuine data, fully built with its witness. The other two
HYPEREDGE-DESIGN §3 negatives (`sound_needs_binding`, `sound_bisim_ill_posed`) need the
soundness/step-completeness machinery that has not landed yet; they are stated below as
named residuals `[N-TURN-a]`/`[N-TURN-b]` rather than half-ported — the audit discipline
(build the witness you can build solidly; name the rest) applied to this lane's own work.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic

namespace Minidregg.Kernel

universe uCarrier uTurn uTurnId uBal v

/-- **The turn as a wide pullback.** `ι` indexes incidences (a physical cell appearing in
two slots is two incidences — what a hyperedge wants). `step` is the coalgebraic `next`;
`turnId i` reads incidence `i`'s post-step apex id; `halfEdge i` reads its signed balance
contribution. -/
structure Hyperedge
    (ι : Type v) [Fintype ι]
    (Carrier : Type uCarrier) (Turn : Type uTurn)
    (TurnId : Type uTurnId) (Bal : Type uBal)
    [AddCommMonoid Bal] [DecidableEq TurnId]
    (step : Carrier → Turn → Carrier)
    (turnId : ι → Carrier → TurnId)
    (halfEdge : ι → Carrier → Turn → Bal) where
  /-- the participant tuple the hyperedge is incident to. -/
  x : ι → Carrier
  /-- the single shared turn, fired atomically at every incidence. -/
  t : Turn
  /-- the shared apex id (the wide pullback's apex; Mina's `account_updates_hash`). -/
  tid : TurnId
  /-- **the cone condition** — every leg factors through the *one* apex. -/
  agree : ∀ i, turnId i (step (x i) t) = tid
  /-- **the conservation aggregate** — the finite balance sum is `0`. -/
  balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0

variable {ι : Type v} [Fintype ι]
variable {Carrier : Type uCarrier} {Turn : Type uTurn}
variable {TurnId : Type uTurnId} {Bal : Type uBal}
variable [AddCommMonoid Bal] [DecidableEq TurnId]
variable {step : Carrier → Turn → Carrier}
variable {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}

/-- **`legs_agree` — every pair of incidences shares an apex id, as a THEOREM.** The
`O(N²)` pairwise agreements of a family-of-binary-edges framing are recovered for free from
the one apex; none are hypothesized. This is the whole reason the wide pullback is the
right primitive. -/
theorem Hyperedge.legs_agree
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) (i j : ι) :
    turnId i (step (H.x i) H.t) = turnId j (step (H.x j) H.t) :=
  (H.agree i).trans (H.agree j).symm

/-! ### The binary slice — a transfer is the `ι = Fin 2` hyperedge, no extra data.

`balanced` on `Fin 2` is exactly `halfEdge 0 … + halfEdge 1 … = 0` (the `+δ`/`−δ` poles of
a swap), recovered by `Fin.sum_univ_two`. No `JointBinding` structure is needed — the
binary case is a projection of the one primitive. -/
theorem Hyperedge.binary_balanced
    {step : Carrier → Turn → Carrier}
    {turnId : Fin 2 → Carrier → TurnId} {halfEdge : Fin 2 → Carrier → Turn → Bal}
    (H : Hyperedge (Fin 2) Carrier Turn TurnId Bal step turnId halfEdge) :
    halfEdge 0 (H.x 0) H.t + halfEdge 1 (H.x 1) H.t = 0 := by
  have := H.balanced
  rwa [Fin.sum_univ_two] at this

/-! ### `binding_is_proper` — the conservation aggregate is genuine data (the tooth).

A configuration can satisfy the cone condition (`agree`) yet FAIL `balanced`: the binding
is a *proper* subobject, not derivable from the cone. Witnessed at `ι = Unit`, one
incidence whose half-edge is `1 ≠ 0` in `ℤ`, with a trivial apex — the cone holds
vacuously (one leg always agrees with itself) but the balance sum is `1`, so no `Hyperedge`
exists on this data. This is why `balanced` is a field and not a lemma. -/
theorem Hyperedge.binding_is_proper :
    ∃ (x : Unit → ℤ) (t : ℤ) (tid : ℤ)
      (step : ℤ → ℤ → ℤ) (turnId : Unit → ℤ → ℤ) (halfEdge : Unit → ℤ → ℤ → ℤ),
      (∀ i, turnId i (step (x i) t) = tid)
      ∧ (Finset.univ.sum fun i => halfEdge i (x i) t) ≠ 0 := by
  refine ⟨fun _ => 0, 0, 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 1, ?_, ?_⟩
  · intro _; rfl
  · simp

/- ### Named residuals — the two negatives awaiting soundness machinery

HYPEREDGE-DESIGN §3 turns three breadstuffs negatives into typed walls. One
(`binding_is_proper`) is built above. The other two are recorded here as PROSE only — a
`def : Prop := ∀ _, True` would be a vacuous obligation that any prover closes, the exact
anti-pattern the audit discipline forbids (see memory `minidregg-audit-discipline`). They
become real theorems, with refutation witnesses BUILT, when their machinery lands:

  [N-TURN-a]  `sound_needs_binding` — step-completeness alone does not entail joint
     admissibility. Blocked on the kernel's `StepComplete` predicate + an `Admissible`
     notion; port when `Kernel/Exec` lands, refuting concretely that a cone lacking
     `balanced` can be step-complete yet inadmissible.

  [N-TURN-b]  `sound_bisim_ill_posed` — soundness-as-bisimulation-to-a-free-`Spec` is
     false, refuted at `Spec.Carrier = Empty`. Blocked on the abstract-spec bisimulation
     relation; port when a `Spec` coalgebra lands, refuting at the `Empty` carrier.
-/

end Minidregg.Kernel
