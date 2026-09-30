/-
# Theory.CanonicalTransition -- one canonical logical transition nucleus

This module is the common semantic target for ordinary and resumed turns.  A
`CellDelta` is indexed by the exact canonical pre/post materializations and
carries one address footprint with its frame law.  A `PreparedTurn` contains
only that canonical post, its delta, and an optional eager nullifier; both
roots are derived projections.

The nucleus depends only on the store and the cell layer.  Adapters from
particular turn models (declared commits, reactive acceptances) live beside
those models and target this module; it never imports them.

`Decision` is total and intent-like: blocked and rejected decisions expose no
post-state, while a prepared decision exposes the logical transition.  Physical
compare-and-swap, nullifier insertion, receipt persistence, and I/O are outside
this module.
-/
import Theory.CellState

namespace Minidregg.Theory.CanonicalTransition

open Minidregg.Theory
open Minidregg.Theory.Store

set_option autoImplicit false

universe u v w y z

/-! ## Canonical typed deltas -/

/-- A proof-relevant transition between two exact canonical cells: an address
footprint and the frame law outside it. -/
structure CellDelta {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root}
    (pre post : CellState.Materialized M) : Type _ where
  footprint : Finset (Address L)
  frame : ∀ address, address ∉ footprint →
    post.logical address = pre.logical address

/-- No address may change outside the delta footprint. -/
theorem CellDelta.changed_only_declared {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (address : Address L)
    (changed : post.logical address ≠ pre.logical address) :
    address ∈ delta.footprint := by
  by_contra outside
  exact changed (delta.frame address outside)

/-- Every validated patch induces the canonical delta it actually applies: its
footprint is the patch's syntactic write footprint and its frame is
`Store.Patch.run_frame`.  There is no separately supplied post-cell,
footprint, or frame proof. -/
def CellDelta.ofValidatedPatch {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {expectedPreRoot : Root} {patch : Patch L}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    CellDelta pre validated.apply where
  footprint := Patch.writeFootprint patch
  frame := Patch.run_frame pre.logical patch

@[simp] theorem CellDelta.ofValidatedPatch_footprint {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {expectedPreRoot : Root} {patch : Patch L}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch) :
    (CellDelta.ofValidatedPatch validated).footprint = Patch.writeFootprint patch :=
  rfl

/-! ## Prepared logical turns and total decisions -/

/-- A commit-ready logical transition.  Roots are deliberately absent as
fields: they are projections of `pre` and `post`. -/
structure PreparedTurn {L : Layout.{u, v, w}} {Root : Type y}
    (M : CellState.Materializer L Root) (pre : CellState.Materialized M)
    (Nullifier : Type z) : Type _ where
  post : CellState.Materialized M
  delta : CellDelta pre post
  nullifier : Option Nullifier

/-- The canonical pre-root; no caller field can disagree with it. -/
def PreparedTurn.preRoot {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (_turn : PreparedTurn M pre Nullifier) : Root :=
  pre.root

/-- The canonical post-root; no caller field can disagree with it. -/
def PreparedTurn.postRoot {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) : Root :=
  turn.post.root

@[simp] theorem PreparedTurn.preRoot_derived {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) :
    turn.preRoot = M.rootOf pre.logical :=
  rfl

@[simp] theorem PreparedTurn.postRoot_derived {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {Nullifier : Type z} (turn : PreparedTurn M pre Nullifier) :
    turn.postRoot = M.rootOf turn.post.logical :=
  rfl

/-- Prepare the exact logical effect of one validated patch. -/
def PreparedTurn.ofValidatedPatch {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {expectedPreRoot : Root} {patch : Patch L} {Nullifier : Type z}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (nullifier : Option Nullifier := none) : PreparedTurn M pre Nullifier where
  post := validated.apply
  delta := CellDelta.ofValidatedPatch validated
  nullifier := nullifier

/-- A prepared turn's pre-root is the root the patch's caller quoted. -/
theorem PreparedTurn.ofValidatedPatch_preRoot {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {expectedPreRoot : Root} {patch : Patch L} {Nullifier : Type z}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (nullifier : Option Nullifier) :
    (PreparedTurn.ofValidatedPatch validated nullifier).preRoot = expectedPreRoot :=
  validated.preRoot_bound.symm

/-- A prepared turn's post-store is the run of the validated patch. -/
@[simp] theorem PreparedTurn.ofValidatedPatch_post_logical {L : Layout.{u, v, w}}
    {Root : Type y} {M : CellState.Materializer L Root} {pre : CellState.Materialized M}
    {expectedPreRoot : Root} {patch : Patch L} {Nullifier : Type z}
    (validated : CellState.ValidatedPatch M pre expectedPreRoot patch)
    (nullifier : Option Nullifier) :
    (PreparedTurn.ofValidatedPatch validated nullifier).post.logical =
      Patch.run pre.logical patch :=
  rfl

/-- Total semantic decision.  Block/reject constructors have no post-state
field; only `prepared` carries a canonical transition. -/
inductive Decision {L : Layout.{u, v, w}} {Root : Type y}
    (M : CellState.Materializer L Root)
    (Blocked Reject Nullifier : Type z) (pre : CellState.Materialized M) : Type _
  | blocked (reason : Blocked)
  | rejected (reason : Reject)
  | prepared (turn : PreparedTurn M pre Nullifier)

/-- Logical state visible after a decision.  This is not a physical durable
commit operation. -/
def Decision.logicalPost {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M} :
    Decision M Blocked Reject Nullifier pre → CellState.Materialized M
  | .blocked _ => pre
  | .rejected _ => pre
  | .prepared turn => turn.post

@[simp] theorem Decision.blocked_atomic {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    (reason : Blocked) :
    (Decision.blocked (M := M) (Reject := Reject) (Nullifier := Nullifier)
      (pre := pre) reason).logicalPost = pre :=
  rfl

@[simp] theorem Decision.rejected_atomic {L : Layout.{u, v, w}} {Root : Type y}
    {M : CellState.Materializer L Root}
    {Blocked Reject Nullifier : Type z} {pre : CellState.Materialized M}
    (reason : Reject) :
    (Decision.rejected (M := M) (Blocked := Blocked) (Nullifier := Nullifier)
      (pre := pre) reason).logicalPost = pre :=
  rfl

/-- info: 'Minidregg.Theory.CanonicalTransition.CellDelta.changed_only_declared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CellDelta.changed_only_declared

end Minidregg.Theory.CanonicalTransition
