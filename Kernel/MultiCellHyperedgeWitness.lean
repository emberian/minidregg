/-
# Kernel.MultiCellHyperedgeWitness -- the joint turn has subjects

`Kernel/MultiCellHyperedge.lean` is where several heterogeneous cells join
under one apex, and it is the carrier `DurableCommitProtocol.ofMultiCell`,
`HyperdocumentAgentOperation.DurablePlan`, and
`HyperdocumentDurableInstallation` all quantify over.  None of them exhibits a
`Commit`, and neither does the defining module -- so the durable installation
statements landed earlier tonight were conditional on a carrier nobody had
built.

This builds one, standing on the `Theory` witnesses:
`AcceptedCellEffectWitness.accepted` and `.acceptedTrue` are the accepted legs,
their schema and materializer come from `CellStateWitness`, and their portal
and authority state from `TypedAuthorizationWitness`.

The turn has TWO incidences, which is what makes the witness worth having:
`cellIdsDistinct` separates two real cell identities, the two legs are distinct
accepted effects over distinct canonical pre-cells with distinct effect digests
(`AcceptedCellEffectWitness.legs_distinct`), and the aggregate resource law
balances by CANCELLATION -- one leg charges `+1`, the other `-1`, and the joint
equation is what forces their sum to zero.

What is still not exercised: both incidences carry the same schema, so
cross-SCHEMA heterogeneity is typed but untested.  A witness with two different
schemas is the remaining improvement.
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

/-- Two incidences, indexed by `Bool`, carrying the witness schema,
materializer, portal, a constant authority projection, and DISTINCT cell
identities. -/
def cells : CellFamily.{0, 0, 0, 0, 0} Bool where
  schema := fun _ => schema
  fieldDecidableEq := fun _ => inferInstance
  resourceDecidableEq := fun _ => inferInstance
  materializer := fun _ => materializer
  portal := fun _ => permissivePortal
  projectAuthority := fun _ _ => authState
  cellId := fun incidence => if incidence then ⟨1⟩ else ⟨0⟩

/-- The leg at the cell holding `false`. -/
def legFalse : LegData.{0, 0, 0, 0, 0, 0} cells false where
  Nullifier := Unit
  family := AcceptedCellEffectWitness.family
  kind := .object
  request := request
  declaration := ()
  outcome := ()

/-- The leg at the cell holding `true`, with its own family and request. -/
def legTrue : LegData.{0, 0, 0, 0, 0, 0} cells true where
  Nullifier := Unit
  family := AcceptedCellEffectWitness.familyTrue
  kind := .object
  request := requestTrue
  declaration := ()
  outcome := ()

/-- The joint declaration.  Its header domain is the shared request domain,
which is what `sharedDomain` demands of both legs. -/
def declaration : Declaration.{0, 0, 0, 0, 0, 0} cells where
  header := { domain := ⟨1⟩, turnId := ⟨2⟩, apex := ⟨3⟩ }
  pre := fun incidence => match incidence with
    | true => cellTrue
    | false => cell
  legs := fun incidence => match incidence with
    | true => legTrue
    | false => legFalse

/-- Both accepted legs are the closed accepted effects from `Theory`. -/
def acceptedLegs : declaration.AcceptedLegs := fun incidence =>
  match incidence with
  | true => acceptedTrue
  | false => accepted

/-- A resource law that charges the two legs oppositely, so the joint balance
is a cancellation rather than a triviality. -/
def law : ResourceLaw.{0, 0, 0, 0, 0, 0, 0} declaration Unit Int where
  delta := fun incidence _ _ => if incidence then 1 else -1

/-- A handler boundary whose evidence is trivially available.  This is the
physical/cryptographic seam and it is deliberately not doing any work here. -/
def boundary : HandlerBoundary.{0, 0, 0, 0, 0, 0, 0} declaration where
  Evidence := fun _ _ => Unit

/-- **`Commit` is inhabited.**  The carrier the durable protocol and the
Hyperdocument installation both quantify over is built, not assumed. -/
def commit : Commit law acceptedLegs boundary where
  cellIdsDistinct := by decide
  sharedDomain := fun incidence => by cases incidence <;> rfl
  aggregateBalanced := by
    funext coordinate
    simp [aggregateDelta, law, Fintype.sum_bool]
  jointInput := { jointCommit := ⟨3⟩, receiptRoot := ⟨4⟩ }
  jointCommitExact := rfl
  jointEvidence := ()

/-- The two cell identities really are distinct, so `cellIdsDistinct` is a
constraint here rather than a consequence of a singleton index. -/
theorem cellIds_distinct : cells.cellId false ≠ cells.cellId true := by decide

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

#print axioms cellIds_distinct
#print axioms commit_nonempty
#print axioms commit_jointCommit
#print axioms no_commit_with_wrong_apex

end

end Minidregg.Kernel.MultiCellHyperedgeWitness
