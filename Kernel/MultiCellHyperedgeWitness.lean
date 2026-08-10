/-
# Kernel.MultiCellHyperedgeWitness -- the joint turn has subjects

`Kernel/MultiCellHyperedge.lean` is where several heterogeneous cells join
under one apex, and it is the carrier `DurableCommitProtocol.ofMultiCell`,
`HyperdocumentAgentOperation.DurablePlan`, and
`HyperdocumentDurableInstallation` all quantify over.  None of them exhibits a
`Commit`, and neither does the defining module -- so the durable installation
statements landed earlier tonight were conditional on a carrier nobody had
built.

This builds one, at a single incidence, standing on the `Theory` witnesses:
`AcceptedCellEffectWitness.accepted` is the accepted leg, its schema and
materializer come from `CellStateWitness`, and its portal and authority state
from `TypedAuthorizationWitness`.

One incidence is the honest minimum for this file, and it is a real
limitation: `cellIdsDistinct` and the aggregate balance are trivial at a
singleton index, so this witness shows the carrier is inhabited without
exercising heterogeneity.  A two-incidence witness with distinct schemas is
the obvious next improvement, and it is the one that would test what this
module is actually for.
-/
import Kernel.MultiCellHyperedge
import Theory.AcceptedCellEffectWitness

namespace Minidregg.Kernel.MultiCellHyperedgeWitness

open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.AcceptedCellEffectWitness
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.TypedAuthorizationWitness
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-- One incidence, carrying the witness schema, materializer, portal, and a
constant authority projection. -/
def cells : CellFamily.{0, 0, 0, 0, 0} Unit where
  schema := fun _ => schema
  fieldDecidableEq := fun _ => inferInstance
  resourceDecidableEq := fun _ => inferInstance
  materializer := fun _ => materializer
  portal := fun _ => permissivePortal
  projectAuthority := fun _ _ => authState
  cellId := fun _ => ⟨0⟩

/-- The leg data: the built effect family, the authorized request, and its one
declaration and outcome. -/
def legData : LegData.{0, 0, 0, 0, 0, 0} cells () where
  Nullifier := Unit
  family := AcceptedCellEffectWitness.family
  kind := .object
  request := request
  declaration := ()
  outcome := ()

/-- The joint declaration.  Its header domain is the request's domain, which is
what `sharedDomain` demands. -/
def declaration : Declaration.{0, 0, 0, 0, 0, 0} cells where
  header := { domain := ⟨1⟩, turnId := ⟨2⟩, apex := ⟨3⟩ }
  pre := fun _ => cell
  legs := fun _ => legData

/-- The accepted leg family is the closed accepted effect from `Theory`. -/
def acceptedLegs : declaration.AcceptedLegs := fun _ => accepted

/-- A resource law charging nothing, so the aggregate balances. -/
def law : ResourceLaw.{0, 0, 0, 0, 0, 0, 0} declaration Unit Nat where
  delta := fun _ _ _ => 0

/-- A handler boundary whose evidence is trivially available.  This is the
physical/cryptographic seam and it is deliberately not doing any work here. -/
def boundary : HandlerBoundary.{0, 0, 0, 0, 0, 0, 0} declaration where
  Evidence := fun _ _ => Unit

/-- **`Commit` is inhabited.**  The carrier the durable protocol and the
Hyperdocument installation both quantify over is built, not assumed. -/
def commit : Commit law acceptedLegs boundary where
  cellIdsDistinct := fun left right _ => Subsingleton.elim left right
  sharedDomain := fun _ => rfl
  aggregateBalanced := by
    funext coordinate
    simp [aggregateDelta, law]
  jointInput := { jointCommit := ⟨3⟩, receiptRoot := ⟨4⟩ }
  jointCommitExact := rfl
  jointEvidence := ()

theorem commit_nonempty : Nonempty (Commit law acceptedLegs boundary) := ⟨commit⟩

/-- The apex is the header's, by construction rather than by caller choice. -/
theorem commit_jointCommit : commit.jointInput.jointCommit =
    declaration.header.apex := commit.jointCommitExact

/-- **Teeth: the apex equation is a real equation.**  A commit quoting any
other joint commitment is unrepresentable at this declaration, so the apex is
not a field a handler may fill in freely. -/
theorem no_commit_with_wrong_apex
    (other : Commit law acceptedLegs boundary)
    (wrong : other.jointInput.jointCommit = ⟨99⟩) : False := by
  have exact := other.jointCommitExact
  rw [wrong] at exact
  exact absurd exact (by decide)

#print axioms commit_nonempty
#print axioms commit_jointCommit
#print axioms no_commit_with_wrong_apex

end

end Minidregg.Kernel.MultiCellHyperedgeWitness
