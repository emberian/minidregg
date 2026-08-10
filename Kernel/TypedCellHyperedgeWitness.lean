/-
# Kernel.TypedCellHyperedgeWitness -- the same-cell joint turn has subjects

`Kernel/TypedCellHyperedge.lean` carries one genuinely load-bearing negative,
`no_commit_of_nonzero_resource`: shape, validation, exact authorizations, and
even apex agreement cannot manufacture conservation.  That theorem is only
worth its weight if a `Commit` can exist at all when conservation DOES hold --
otherwise it says nothing that `IsEmpty` did not already say everywhere.

This exhibits one, standing on the `Theory` witnesses.  It also adds the
matching negative for the apex, so both of the structure's two equations are
shown to be constraints:

* `no_commit_of_nonzero_resource` (already in the source) -- conservation;
* `no_commit_of_wrong_apex` (here) -- the apex is the root of the APPLIED
  joint patch, not a digest a caller may nominate.

Scope: one incidence over the minimal witness schema, with a law charging
nothing.  Multi-leg field composition and resource disjointness are typed but
not exercised at a singleton index.
-/
import Kernel.TypedCellHyperedge
import Theory.AcceptedCellEffectWitness

namespace Minidregg.Kernel.TypedCellHyperedgeWitness

open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.AcceptedCellEffectWitness
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.TypedAuthorizationWitness
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-- The authority state is read off the cell, constantly here. -/
def projection : AuthorizationProjection schema where
  project := fun _ => authState

/-- One accepted leg: the closed accepted effect from `Theory`. -/
noncomputable def leg :
    Leg (S := schema) (M := materializer) permissivePortal
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
noncomputable def declaration :
    Declaration schema materializer permissivePortal projection Unit where
  pre := cell
  apex := ⟨1⟩
  legs := fun _ => leg
  composition := { fieldMode := .canonical, order := [()] }

/-- A law charging nothing, so conservation holds and the interesting equation
here is the apex one. -/
def law : ResourceLaw schema materializer permissivePortal Unit Int where
  delta := fun _ _ => 0

theorem shapeValid : declaration.ShapeValid where
  orderComplete := ⟨by decide, fun incidence => by cases incidence; decide⟩
  resourcesDisjoint := fun _ _ different => absurd (Subsingleton.elim _ _) different
  fieldsValid := trivial

/-- The joint patch validates: its expected pre-root IS the cell's root and its
footprints ARE its named writes, both by the way `jointPatch` is derived. -/
theorem jointPatch_accepted :
    ∃ validated : CellState.ValidatedPatch materializer declaration.pre
        declaration.jointPatch,
      CellState.validate materializer declaration.pre declaration.jointPatch =
        CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show declaration.jointPatch.expectedPreRoot = declaration.pre.root
    from rfl)]
  rw [dif_pos (show declaration.jointPatch.fieldFootprint =
    declaration.jointPatch.namedFields from rfl)]
  rw [dif_pos (show declaration.jointPatch.resourceFootprint =
    declaration.jointPatch.namedResources from rfl)]
  exact ⟨_, rfl⟩

noncomputable def jointValidated :
    CellState.ValidatedPatch materializer declaration.pre declaration.jointPatch :=
  jointPatch_accepted.choose

/-- **`Commit` is inhabited.**  Shape, joint validation, the apex equation, and
conservation all hold at built data. -/
noncomputable def commit : Commit law declaration where
  shape := shapeValid
  validated := jointValidated
  apexExact := by decide
  aggregateBalanced := by
    funext coordinate
    simp [Declaration.aggregateDelta, law]

theorem commit_nonempty : Nonempty (Commit law declaration) := ⟨commit⟩

/-- **Teeth: the apex is derived, not nominated.**  The same declaration with a
different apex admits no commit, because `apexExact` pins the apex to the root
of the applied joint patch. -/
theorem no_commit_of_wrong_apex :
    IsEmpty (Commit law { declaration with apex := ⟨99⟩ }) :=
  ⟨fun other => by
    have exact : other.validated.apply.root = ⟨99⟩ := other.apexExact
    have collapsed : (⟨99⟩ : Digest) = ⟨1⟩ := by rw [← exact]; rfl
    exact absurd collapsed (by decide)⟩

/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.shapeValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shapeValid
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.jointPatch_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jointPatch_accepted
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.commit_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_nonempty
/-- info: 'Minidregg.Kernel.TypedCellHyperedgeWitness.no_commit_of_wrong_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_wrong_apex

end

end Minidregg.Kernel.TypedCellHyperedgeWitness
