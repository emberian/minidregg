/-
# Kernel.TypedCellHyperedgeWitness -- the same-cell joint turn has subjects

`Kernel/TypedCellHyperedge.lean` carries load-bearing negatives: conservation
(`no_commit_of_nonzero_resource`), joint re-validation
(`no_commit_of_invalid_joint_patch`), lost outcomes and failed postconditions.
They are worth their weight only if a `Commit` can exist at all when every
condition DOES hold -- otherwise they say nothing that `¬ Commit` did not
already say everywhere.

This exhibits one, standing on the `Theory` witnesses, and the matching
negatives at built data:

* `commit` -- one incidence over the witness layout, with a law charging
  nothing: shape, joint validation, apex, outcomes, postconditions and
  conservation all hold;
* `no_commit_of_wrong_apex` -- the apex is the root of the APPLIED joint patch,
  not a digest a caller may nominate;
* `repeated_write_refused` -- the same accepted write, taken twice in canonical
  order, admits no commit: each leg is valid at the pre-store on its own, but
  the joint patch re-checks the second write's guard at the store the first
  produced, where it is stale.  (Under the deleted field-footprint validator
  this pair committed as an "agreeing overlap"; the guard is what now refuses
  it.)
-/
import Kernel.TypedCellHyperedge
import Theory.AcceptedCellEffectWitness

namespace Minidregg.Kernel.TypedCellHyperedgeWitness

open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.AcceptedCellEffectWitness
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorizationWitness
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- The authority state is read off the cell, constantly here. -/
def projection : AuthorizationProjection layout where
  project := fun _ => authState

/-- One accepted leg: the closed accepted effect from `Theory`. -/
def leg :
    Leg (L := layout) (M := materializer) permissivePortal
      (projection.project cell.logical) cell where
  Nullifier := Unit
  family := AcceptedCellEffectWitness.family
  kind := .object
  request := request
  declaration := ()
  outcome := ()
  accepted := accepted

/-- The declaration.  Its apex is the root the joint patch actually reaches,
which `apexExact` below forces. -/
def declaration :
    Declaration layout materializer permissivePortal projection Unit where
  pre := cell
  apex := ⟨1⟩
  legs := fun _ => leg
  composition := { mode := .canonical, order := [()] }

/-- A law charging nothing, so conservation holds and the interesting equations
here are the apex and joint-validation ones. -/
def law : ResourceLaw layout materializer permissivePortal Unit Int where
  stateDelta := fun _ _ _ _ => 0

theorem shapeValid : declaration.ShapeValid where
  orderComplete := ⟨by decide, fun incidence => by cases incidence; decide⟩
  modeValid := trivial

theorem jointPatch_eq : declaration.jointPatch = honestPatch := rfl

/-- The joint patch validates at the common pre-root: its one write's guard
holds at the pre-store. -/
theorem jointValidated :
    CellState.ValidatedPatch materializer declaration.pre declaration.pre.root
      declaration.jointPatch := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts materializer declaration.pre
    declaration.pre.root declaration.jointPatch rfl (by decide)
  exact validated

/-- **`Commit` is inhabited.**  Shape, joint validation, the apex equation,
preserved outcomes, joint postconditions and conservation all hold at built
data. -/
theorem commit : Commit law declaration where
  shape := shapeValid
  validated := jointValidated
  apexExact := by decide
  outcomesPreserved := by
    intro incidence address _present
    cases incidence
    rfl
  postconditions := by
    intro incidence
    cases incidence
    intro address _present
    rfl
  jointDeltaExact := by
    funext coordinate
    simp [Declaration.jointDelta, Declaration.aggregateDelta, ResourceLaw.delta, law]
  aggregateBalanced := by
    funext coordinate
    simp [Declaration.aggregateDelta, ResourceLaw.delta, law]

/-- The committed joint post holds the leg's write. -/
theorem commit_post : Patch.run declaration.pre.logical declaration.jointPatch sole =
    some true := by
  decide

/-- **Teeth: the apex is derived, not nominated.**  The same declaration with a
different apex admits no commit, because `apexExact` pins the apex to the root
of the applied joint patch. -/
theorem no_commit_of_wrong_apex :
    ¬ Commit law { declaration with apex := ⟨99⟩ } := by
  intro other
  have exact : other.validated.apply.root = ⟨99⟩ := other.apexExact
  change (CellState.materialize materializer (Patch.run cell.logical honestPatch)).root =
    ⟨99⟩ at exact
  have reached :
      (CellState.materialize materializer (Patch.run cell.logical honestPatch)).root =
        ⟨1⟩ := by decide
  rw [reached] at exact
  exact absurd exact (by decide)

/-! ## Joint validation refuses a stale second guard -/

/-- The same accepted write, as two incidences in canonical order. -/
def repeatedDeclaration :
    Declaration layout materializer permissivePortal projection Bool where
  pre := cell
  apex := ⟨1⟩
  legs := fun _ => leg
  composition := { mode := .canonical, order := [false, true] }

theorem repeatedShape : repeatedDeclaration.ShapeValid where
  orderComplete := by
    constructor
    · decide
    · intro incidence
      cases incidence <;> decide
  modeValid := trivial

/-- Each leg is valid at the pre-store on its own. -/
theorem repeated_legs_valid (incidence : Bool) :
    Patch.ValidFrom cell.logical (repeatedDeclaration.legPatch incidence) :=
  (repeatedDeclaration.legs incidence).patch_valid

/-- The joint patch is not: the second write guards on `false`, and the first
already wrote `true`. -/
theorem repeated_joint_invalid :
    ¬ Patch.ValidFrom repeatedDeclaration.pre.logical repeatedDeclaration.jointPatch := by
  decide

/-- **Teeth: no commit of the repeated write**, although the shape is valid
and the law charges nothing. -/
theorem repeated_write_refused : ¬ Commit law repeatedDeclaration :=
  no_commit_of_invalid_joint_patch law repeatedDeclaration repeated_joint_invalid

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.shapeValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shapeValid
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.commit_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_post
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.no_commit_of_wrong_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_wrong_apex
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.repeated_legs_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_legs_valid
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.repeated_write_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_write_refused

end Minidregg.Kernel.TypedCellHyperedgeWitness
