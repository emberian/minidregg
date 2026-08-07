/-
# `Kernel/TurnLimit.lean` — N2a: the turn's cone data IS a wide-pullback limit.

`docs/N2-HYPEREDGE-LIMIT.md` fixes the category BEFORE the Lean. This file lands N2a,
Candidate A: at a fixed turn `t`, the hyperedge's cone data
`{ x : ι → Carrier // ∃ tid, ∀ i, turnId i (step (x i) t) = tid }` (the `(x, agree)` half
of `Kernel/Turn.lean`'s `Hyperedge`) carries a genuine `IsLimit` of the wide cospan
`legs ↦ Carrier`, `apex ↦ TurnId`, `arrow i ↦ (fun c => turnId i (step c t))`.

This is the CONE half only (agreement is universal, not pairwise — the rigorous form of
`legs_agree`); `balanced` is the extra structure the plain limit does not see. That deeper
statement is N2b (Candidate B, the balanced-cone category), authored after this lands. Do
NOT read this file as proving conservation is a limit — it proves the AGREEMENT bookkeeping
is one, over nonempty `ι`, which is exactly the near-term target §2 fixes.

Proved (genuine, no `sorry`, no vacuous obligation):
  * `turnDiagram`         — the wide-cospan functor (mathlib `WidePullbackShape.wideCospan`).
  * `hyperedgeCone`       — the cone whose point is the spec's existential cone-data type.
  * `hyperedge_is_wide_pullback` — that cone IS a limit (`Types.isLimit_iff`), over `Nonempty ι`.
Keystones BUILT below: satisfiable (Fin 2 / ℤ, the limit inhabited), teeth (`binding_is_proper`
reused + a tuple with no common apex, hence not a cone point), premise-inhabitation (the
diagram is a genuine functor over nonempty `ι`).
-/
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Data.Fin.VecNotation
import Kernel.Turn

namespace Minidregg.Kernel

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The diagram and the cone (the wide cospan at a fixed turn `t`). -/

section Diagram

variable {ι Carrier Turn TurnId : Type u}
variable (step : Carrier → Turn → Carrier)
variable (turnId : ι → Carrier → TurnId)

/-- **The turn diagram at a fixed turn `t`** — the wide cospan whose legs are all `Carrier`,
whose apex object is `TurnId`, and whose `i`-th arrow is `c ↦ turnId i (step c t)`. A genuine
functor: `WidePullbackShape.wideCospan` discharges the identity/composition laws. -/
def turnDiagram (t : Turn) : WidePullbackShape ι ⥤ Type u :=
  WidePullbackShape.wideCospan TurnId (fun _ => Carrier)
    (fun i => ↾(fun c => turnId i (step c t)))

/-- **The hyperedge's cone data at fixed `t`** — participant tuples admitting a common apex
id. This is exactly `Hyperedge.x` packaged with the existential form of `Hyperedge.agree`
(the shared `tid` witnessed rather than carried). It is the point of `hyperedgeCone`. -/
def HyperedgeConeData (t : Turn) : Type u :=
  { x : ι → Carrier // ∃ tid, ∀ i, turnId i (step (x i) t) = tid }

/-- **The cone over `turnDiagram t` on the hyperedge cone data.** Each leg projects the
tuple; the apex map reads the common id off a representative incidence `Classical.arbitrary ι`
(any leg gives the same value — that is the content of the cone condition). The coherence —
every leg's image equals the apex id — is exactly `Hyperedge.legs_agree` in embryo. -/
noncomputable def hyperedgeCone [Nonempty ι] (t : Turn) : Cone (turnDiagram step turnId t) :=
  WidePullbackShape.mkCone
    (X := HyperedgeConeData step turnId t)
    (↾(fun p => turnId (Classical.arbitrary ι) (step (p.1 (Classical.arbitrary ι)) t)))
    (fun i => ↾(fun p => p.1 i))
    (fun i => by
      ext p
      obtain ⟨tid, htid⟩ := p.2
      exact (htid i).trans (htid (Classical.arbitrary ι)).symm)

/-- **N2a — the hyperedge cone data IS a limit of the turn diagram.** Over a nonempty index
`ι`, `hyperedgeCone t` is a limit cone of `turnDiagram t`: every section of the wide cospan
(every tuple sharing a common apex image) is hit by a unique cone-data point. This is the
rigorous universality behind `Hyperedge.legs_agree` — pairwise agreement is not hypothesized
pairwise, it is forced by the ONE apex the limit provides. It captures the `agree` half only;
`balanced` is invisible to this plain limit (that is N2b, `docs/N2-HYPEREDGE-LIMIT.md` §1). -/
theorem hyperedge_is_wide_pullback [Nonempty ι] (t : Turn) :
    Nonempty (IsLimit (hyperedgeCone step turnId t)) := by
  rw [Types.isLimit_iff]
  intro s hs
  -- The unique cone-data point: the tuple of leg images, with `s none` as its common apex.
  refine ⟨⟨fun i => s (some i), ⟨s none, fun i => hs (WidePullbackShape.Hom.term i)⟩⟩, ?_, ?_⟩
  · -- it maps to `s` at every object of the shape.
    rintro (_ | i)
    · -- apex object: the representative leg's image is `s none` (the section's apex value).
      exact hs (WidePullbackShape.Hom.term (Classical.arbitrary ι))
    · -- a leg: the projection recovers `s (some i)`.
      rfl
  · -- uniqueness: two cone-data points agreeing on every leg are equal (Subtype extensionality).
    intro y hy
    apply Subtype.ext
    funext i
    exact hy (some i)

end Diagram

/-! ### Keystone fields — BUILT witnesses (the audit lesson: exhibit, never assert).

`docs/N2-HYPEREDGE-LIMIT.md` §2 fixes three keystones. Each is a real term below, at the
concrete instance `ι = Fin 2`, `Carrier = Turn = TurnId = ℤ`. -/

section Keystones

/-- The trivial step: the turn does not move the pre-state (enough to exhibit cone data). -/
def stepId : ℤ → ℤ → ℤ := fun c _ => c
/-- A reader that returns the state as its apex id. Distinct legs then read distinct ids. -/
def readId : Fin 2 → ℤ → ℤ := fun _ c => c
/-- The constantly-`0` reader: every leg agrees, so every tuple is a cone point. -/
def zeroRead : Fin 2 → ℤ → ℤ := fun _ _ => 0
/-- A binary tuple whose two legs disagree (`0 ≠ 1`) — no common apex is possible. -/
def splitTuple : Fin 2 → ℤ := ![0, 1]

/-! **satisfiable** — the transfer, exhibited. With the constant reader the cone condition
holds for `tid = 0`, so `HyperedgeConeData` is inhabited AND (Fin 2 nonempty) its cone is a
genuine limit. -/

/-- A concrete inhabitant of the cone data: the zero tuple with common apex `0`. -/
theorem hyperedgeConeData_inhabited :
    Nonempty (HyperedgeConeData stepId zeroRead (0 : ℤ)) :=
  ⟨⟨fun _ => 0, ⟨0, fun _ => rfl⟩⟩⟩

/-- The limit itself, transferred to the concrete instance: `hyperedge_is_wide_pullback` at
`ι = Fin 2` (its `Nonempty (Fin 2)` premise is discharged by the instance). -/
theorem hyperedge_is_wide_pullback_fin2 :
    Nonempty (IsLimit (hyperedgeCone stepId zeroRead (0 : ℤ))) :=
  hyperedge_is_wide_pullback stepId zeroRead 0

/-! **teeth** — the limit condition is a genuine constraint, two-pronged. -/

/-- (a) `Hyperedge.binding_is_proper` (from `Kernel/Turn.lean`) reused verbatim: a cone
(`agree` holds) that is not a valid conserving hyperedge (`balanced` fails). This is N2b's
teeth in embryo — a cone that does not factor through the CONSERVING limit. -/
theorem teeth_binding_is_proper :
    ∃ (x : Unit → ℤ) (t : ℤ) (tid : ℤ)
      (step : ℤ → ℤ → ℤ) (turnId : Unit → ℤ → ℤ) (halfEdge : Unit → ℤ → ℤ → ℤ),
      (∀ i, turnId i (step (x i) t) = tid)
      ∧ (Finset.univ.sum fun i => halfEdge i (x i) t) ≠ 0 :=
  Hyperedge.binding_is_proper

/-- (b) A tuple with NO common apex: `readId` makes the two legs read `0` and `1`, so no
`tid` satisfies the cone condition. Hence `splitTuple` gives no element of
`HyperedgeConeData` — being a cone point is a real constraint, not automatic. -/
theorem no_common_apex :
    ¬ ∃ tid : ℤ, ∀ i : Fin 2, readId i (stepId (splitTuple i) 0) = tid := by
  rintro ⟨tid, h⟩
  have h0 := h 0
  have h1 := h 1
  simp only [readId, stepId, splitTuple, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

/-- The negative packaged against the cone-data type: `splitTuple` is provably not the
underlying tuple of any `HyperedgeConeData` point. -/
theorem splitTuple_not_cone_point :
    ¬ ∃ hd : HyperedgeConeData stepId readId (0 : ℤ), hd.1 = splitTuple := by
  rintro ⟨⟨x, hx⟩, rfl⟩
  exact no_common_apex hx

/-! **premise-inhabitation** — the diagram is a genuine functor over a nonempty index. -/

/-- The index type is nonempty (the `Nonempty ι` the limit needs). -/
theorem index_nonempty : Nonempty (Fin 2) := inferInstance

/-- The shape category is inhabited (its apex object `none`). -/
theorem shape_inhabited : Nonempty (WidePullbackShape (Fin 2)) := ⟨none⟩

/-- The diagram genuinely respects identities — a real functor law, not a stipulation. -/
theorem turnDiagram_map_id (t : ℤ) (X : WidePullbackShape (Fin 2)) :
    (turnDiagram stepId readId t).map (𝟙 X) = 𝟙 _ :=
  (turnDiagram stepId readId t).map_id X

end Keystones

end Minidregg.Kernel
