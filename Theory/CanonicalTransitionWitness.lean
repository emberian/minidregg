/-
# Theory.CanonicalTransitionWitness -- the canonical transition moves the root

`Theory/CanonicalTransition.lean` derives `PreparedTurn` from a
`ValidatedPatch` and proves its pre- and post-roots are derived rather than
supplied.  Those theorems are the point of the module and they are quantified
over a `PreparedTurn` the file never exhibits.

`CellStateWitness` now carries a two-state schema on purpose: its cell holds
`false`, its validated patch writes `true`, and the root is the encoded byte.
So the prepared turn built here does not merely inhabit the type -- it changes
the canonical state, and `preparedTurn_moves` shows the derived post-root
differs from the derived pre-root.

That distinction matters.  A witness over a singleton state space would
inhabit `PreparedTurn` while leaving "the canonical post is derived from the
validated patch" untested, because every post would equal every pre.
-/
import Theory.CanonicalTransition
import Theory.CellStateWitness

namespace Minidregg.Theory.CanonicalTransitionWitness

open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.CellState
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- The validated patch obtained by running the validator. -/
theorem validated : ValidatedPatch materializer cell honestPatch :=
  honestPatch_accepted.choose

/-- **`PreparedTurn` is inhabited**, and its post-state is derived from that
validated patch rather than supplied. -/
noncomputable def preparedTurn : PreparedTurn materializer cell Unit :=
  PreparedTurn.ofValidatedPatch (Nullifier := Unit) validated

theorem preparedTurn_nonempty :
    Nonempty (PreparedTurn materializer cell Unit) := ⟨preparedTurn⟩

/-- The pre-root is the cell's, by computation. -/
theorem preparedTurn_preRoot : preparedTurn.preRoot = ⟨0⟩ := rfl

/-- The post-root is the patched cell's, by computation -- the field moved from
`false` to `true`, so the encoded byte and hence the root moved with it. -/
theorem preparedTurn_postRoot : preparedTurn.postRoot = ⟨1⟩ := by decide

/-- **The transition is not trivial.**  This is what a singleton state space
would have hidden: the derived post-root genuinely differs from the derived
pre-root, so "canonical post derived from the validated patch" is exercised
rather than merely typed. -/
theorem preparedTurn_moves : preparedTurn.preRoot ≠ preparedTurn.postRoot := by
  rw [preparedTurn_preRoot, preparedTurn_postRoot]
  decide

/-- And the eager nullifier defaults to absent: preparing a turn does not mint
one. -/
theorem preparedTurn_no_nullifier : preparedTurn.nullifier = none := rfl

/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_nonempty
/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_preRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_preRoot
/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_postRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_postRoot
/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_moves
/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_no_nullifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_no_nullifier

end Minidregg.Theory.CanonicalTransitionWitness
