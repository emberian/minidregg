/-
# Theory.AuthMapCellRoot -- the world map over materialized cell roots

`Theory.AuthMap`'s two-level section takes the cell root as a free parameter
`cellRoot : C → V`.  `Theory.CellState` fixes what a cell root is: the
materializer's root of the logical store, `Materializer.rootOf` (DATAMODEL §6
Q3: the root is a function of the logical store; stage F hashes the canonical
bytes, D1 swaps in an `AuthMap` root under the same function type).

This module instantiates `cellRoot := M.rootOf` with cells = `Store L`, and
states the three facts the world level needs of the cell layer:

* `cellWorld_opening` — a present cell's materialized root opens at the world root;
* `cellWorld_sound` — under the world carrier, a verifying opening of `(c, r)`
  names a present cell store whose materialized root is `r`;
* `validated_write_world` — installing the post of a `ValidatedPatch` at cell
  `c` moves the world root along `c`'s one path (`rootAfter` from the old
  opening), and the post cell's root opens at the new world root.
-/
import Theory.AuthMap
import Theory.CellState

namespace Minidregg.Theory.AuthMapCellRoot

open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.AuthMap

set_option autoImplicit false

variable {L : Layout.{0, 0, 0}} {Root I D : Type} [DecidableEq I] [DecidableEq D]
  (M : Materializer L Root) (W : Scheme I Root D)

/-- The world root of a map of cell stores, each rooted by the materializer. -/
abbrev cellWorldRoot (w : Map I (Store L)) : D := worldRoot W M.rootOf w

/-- Completeness: a present cell's materialized root opens at the world root. -/
theorem cellWorld_opening (w : Map I (Store L)) (c : I) (store : Store L)
    (present : lookup W.ix w c = some store) :
    W.verify (cellWorldRoot M W w) c (some (materialize M store).root)
      (W.opening (worldSlots M.rootOf w) c) = true := by
  have opens := world_opening W M.rootOf w c
  rw [present] at opens
  exact opens

/-- Soundness under the world carrier: a verifying opening of `(c, r)` names a
present cell store whose materialized root is `r`. -/
theorem cellWorld_sound (w : Map I (Store L)) (c : I) (r : Root)
    (π : Scheme.Opening I Root D)
    (hbind : W.PathBinding (worldSlots M.rootOf w) c (some r) π)
    (h : W.verify (cellWorldRoot M W w) c (some r) π = true) :
    ∃ store, lookup W.ix w c = some store ∧ (materialize M store).root = r :=
  world_sound W M.rootOf w c r π hbind h

/-- **The bridge.**  Installing a validated patch's post cell at `c` moves the
world root along `c`'s path from the old opening to the post cell's root, and
the post cell opens at the new world root. -/
theorem validated_write_world {pre : Materialized M} {expectedPreRoot : Root}
    {patch : Patch L} (validated : ValidatedPatch M pre expectedPreRoot patch)
    (w : Map I (Store L)) (c : I) :
    cellWorldRoot M W (write W.ix w c (some validated.apply.logical)) =
        W.rootAfter (W.opening (worldSlots M.rootOf w) c) c (some validated.apply.root) ∧
      W.verify (cellWorldRoot M W (write W.ix w c (some validated.apply.logical))) c
        (some validated.apply.root)
        (W.opening (worldSlots M.rootOf (write W.ix w c (some validated.apply.logical))) c) =
          true :=
  ⟨worldRoot_write W M.rootOf w c _,
    cellWorld_opening M W _ c _ (lookup_write_self W.ix w c _)⟩

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.AuthMapCellRoot.cellWorld_opening' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cellWorld_opening
/-- info: 'Minidregg.Theory.AuthMapCellRoot.cellWorld_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cellWorld_sound
/-- info: 'Minidregg.Theory.AuthMapCellRoot.validated_write_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validated_write_world

end Minidregg.Theory.AuthMapCellRoot
