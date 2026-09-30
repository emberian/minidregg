/-
# Theory.CanonicalTransitionWitness -- the canonical transition moves the root

`Theory/CanonicalTransition.lean` derives `PreparedTurn` from a
`ValidatedPatch` and proves its pre- and post-roots are derived rather than
supplied.  Those theorems are quantified over a `PreparedTurn` the module never
exhibits.

`CellStateWitness`'s cell holds `false`, its validated patch writes `true`, and
the root is the encoded byte.  So the prepared turn built here does not merely
inhabit the type -- it changes the canonical state, and `preparedTurn_moves`
shows the derived post-root differs from the derived pre-root.  A witness over
a singleton state space would inhabit `PreparedTurn` while testing nothing.
-/
import Theory.CanonicalTransition
import Theory.CellStateWitness

namespace Minidregg.Theory.CanonicalTransitionWitness

open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.CellState
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- The validated patch obtained by running the validator. -/
theorem validated : ValidatedPatch materializer cell ⟨0⟩ honestPatch :=
  honestPatch_accepted.choose

/-- **`PreparedTurn` is inhabited**, and its post-state is derived from that
validated patch rather than supplied. -/
noncomputable def preparedTurn : PreparedTurn materializer cell Unit :=
  PreparedTurn.ofValidatedPatch (Nullifier := Unit) validated

theorem preparedTurn_nonempty :
    Nonempty (PreparedTurn materializer cell Unit) := ⟨preparedTurn⟩

/-- The pre-root is the cell's, by computation. -/
theorem preparedTurn_preRoot : preparedTurn.preRoot = ⟨0⟩ := by decide

/-- The post-root is the patched cell's, by computation -- the value moved from
`false` to `true`, so the encoded byte and hence the root moved with it. -/
theorem preparedTurn_postRoot : preparedTurn.postRoot = ⟨1⟩ := by decide

/-- **The transition is not trivial.** -/
theorem preparedTurn_moves : preparedTurn.preRoot ≠ preparedTurn.postRoot := by
  rw [preparedTurn_preRoot, preparedTurn_postRoot]
  decide

/-- The eager nullifier defaults to absent: preparing a turn does not mint one. -/
theorem preparedTurn_no_nullifier : preparedTurn.nullifier = none := rfl

/-- The delta's footprint is the patch's syntactic write footprint, and the one
address in it did change: the frame law's premise is not vacuous here. -/
theorem preparedTurn_footprint_changes :
    sole ∈ preparedTurn.delta.footprint ∧
      preparedTurn.post.logical sole ≠ cell.logical sole := by
  decide

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
/-- info: 'Minidregg.Theory.CanonicalTransitionWitness.preparedTurn_footprint_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms preparedTurn_footprint_changes

end Minidregg.Theory.CanonicalTransitionWitness
