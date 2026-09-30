/-
# Kernel.TypedCellHyperedge -- layout-polymorphic accepted-effect hyperedges

This is the flat joint-transition nucleus (D-0002).  Every incidence is an
existing `AcceptedCellEffect` over one exact canonical pre-cell (a `Store L`)
and one authorization-state projection of that cell.  The unique joint post is
obtained by validating and running the ordered concatenation of those effects'
guarded patches: joint validation re-checks every guard at the store its
prefix produced, so an incidence whose guard a previous incidence invalidated
is refused, not overwritten.

Conservation is parameterized by an explicit typed `ResourceLaw` over actual
logical pre/post stores and the validated write footprint.  Both the incidence
aggregate and its equality to the actual joint-state delta are checked.  Each
accepted outcome must survive in that joint state, and every source-owned
family postcondition is also required on it; local acceptance cannot hide a
broken cross-address invariant.  Canonical order therefore allows agreeing
overlaps, not unchecked overwrites of independently accepted outcomes.

The legacy integer-field carrier (`Kernel.DeclaredHyperedge`) and its adapter
certificate are deleted; this is the only joint carrier over one cell.
-/
import Kernel.Turn
import Theory.AcceptedCellEffect

namespace Minidregg.Kernel.TypedCellHyperedge

open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w y z b

/-! ## One canonical pre-cell and heterogeneous accepted legs -/

/-- Authorization is projected from the same logical cell consumed by every
effect.  There is no independent ambient authorization state at the joint
transition boundary. -/
structure AuthorizationProjection (L : Layout.{u, v, w}) where
  project : Store L -> AuthState

/-- A heterogeneous accepted semantic effect, packaged as one incidence.
The family, request, declaration, outcome, proof mode, validated patch, and
request-indexed authorization all remain recoverable from `accepted`. -/
structure Leg
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    (portal : Portal) (authState : AuthState)
    (pre : CellState.Materialized M) : Type (max u v w (y + 1) (z + 1)) where
  Nullifier : Type y
  family : SemanticEffectFamily.{u, v, w, y, z} L M Nullifier
  kind : ResourceKind
  request : Request kind
  declaration : family.Declaration
  outcome : family.Outcome declaration
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    family request pre declaration outcome

namespace Leg

variable
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {portal : Portal} {authState : AuthState}
    {pre : CellState.Materialized M}

/-- The exact patch already validated by this incidence's accepted effect. -/
def patch (leg : Leg.{u, v, w, y, z} portal authState pre) : Patch L :=
  leg.family.patch leg.declaration leg.outcome

/-- The incidence-local canonical post.  This is retained even though the
joint transition below has one separately composed post. -/
def post (leg : Leg.{u, v, w, y, z} portal authState pre) :
    CellState.Materialized M :=
  leg.accepted.prepared.post

@[simp] theorem request_preRoot
    (leg : Leg.{u, v, w, y, z} portal authState pre) :
    leg.request.preStateRoot = pre.root :=
  leg.accepted.preRootBound

@[simp] theorem request_effectsDigest
    (leg : Leg.{u, v, w, y, z} portal authState pre) :
    leg.request.effectsDigest =
      leg.family.effectDigest leg.declaration :=
  leg.accepted.effectsDigestBound

/-- Exact request-indexed authority is retained, not summarized by a Boolean. -/
def authorization
    (leg : Leg.{u, v, w, y, z} portal authState pre) :
    Authorized portal authState leg.request :=
  leg.accepted.authorization

@[simp] theorem post_exact
    (leg : Leg.{u, v, w, y, z} portal authState pre) :
    leg.post = leg.accepted.validated.apply :=
  rfl

/-- The leg's own patch is valid at the common pre-store. -/
theorem patch_valid (leg : Leg.{u, v, w, y, z} portal authState pre) :
    Patch.ValidFrom pre.logical leg.patch :=
  leg.accepted.validated.valid

end Leg

/-! ## Flat shape and deterministic patch composition -/

inductive CompositionMode
  | disjoint
  /-- A fixed patch order whose accepted outcomes must all survive.
  `Commit.outcomesPreserved` is mandatory even when structural overlap is allowed. -/
  | canonical
  deriving DecidableEq, Repr

structure CompositionPlan (Incidence : Type z) where
  mode : CompositionMode
  order : List Incidence

/-- A resource law measures the actual logical-store change over the exact
validated write footprint.  The same source-owned primitive is used for each
leg and for the joint post; there is no independently supplied aggregate
meaning. -/
structure ResourceLaw
    (L : Layout.{u, v, w})
    (M : CellState.Materializer L Digest) (portal : Portal)
    (Coordinate : Type y) (Balance : Type b) [AddCommMonoid Balance] :
    Type (max u v w y b) where
  stateDelta : Store L -> Store L -> Finset (Address L) -> Coordinate -> Balance

def ResourceLaw.delta
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L Digest} {portal : Portal}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    {authState : AuthState} {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, y, z} portal authState pre) : Coordinate -> Balance :=
  law.stateDelta pre.logical leg.post.logical (Patch.writeFootprint leg.patch)

/-- One flat family of accepted incidences.  All legs are definitionally
indexed by the same canonical pre-cell and by the authorization projection of
that exact cell. -/
structure Declaration
    (L : Layout.{u, v, w})
    (M : CellState.Materializer L Digest)
    (portal : Portal) (projection : AuthorizationProjection L)
    (Incidence : Type z) where
  pre : CellState.Materialized M
  apex : Digest
  legs : Incidence -> Leg.{u, v, w, y, z} portal
    (projection.project pre.logical) pre
  composition : CompositionPlan Incidence

namespace Declaration

variable
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {portal : Portal} {projection : AuthorizationProjection L}
    {Incidence : Type z} [Fintype Incidence]

def legPatch
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (incidence : Incidence) : Patch L :=
  (declaration.legs incidence).patch

/-- The sole raw joint patch: the ordered concatenation of the legs' patches.
Its footprint is derived from its syntax, so joint validation can contain
neither an undeclared write nor a ghost key. -/
def jointPatch
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) :
    Patch L :=
  declaration.composition.order.flatMap declaration.legPatch

def OrderComplete
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) : Prop :=
  declaration.composition.order.Nodup /\
    forall incidence, incidence ∈ declaration.composition.order

def FootprintsDisjoint
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) : Prop :=
  forall left right, left ≠ right ->
    Disjoint (Patch.writeFootprint (declaration.legPatch left))
      (Patch.writeFootprint (declaration.legPatch right))

structure ShapeValid
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) : Prop where
  orderComplete : declaration.OrderComplete
  modeValid :
    match declaration.composition.mode with
    | .disjoint => declaration.FootprintsDisjoint
    | .canonical => True

/-- Heterogeneous eager nullifiers are retained with their incidence index. -/
def JointNullifier
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) : Type _ :=
  Sigma fun incidence => (declaration.legs incidence).Nullifier

def jointNullifiers
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) :
    List declaration.JointNullifier :=
  declaration.composition.order.filterMap fun incidence =>
    match (declaration.legs incidence).family.nullifier
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome with
    | none => none
    | some nullifier => some ⟨incidence, nullifier⟩

/-- The per-incidence aggregate is read from each exact accepted local post,
against the common canonical pre. -/
def aggregateDelta
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) :
    Coordinate -> Balance :=
  fun coordinate => Finset.univ.sum fun incidence =>
    law.delta (declaration.legs incidence) coordinate

/-- Every incidence's final value at each address it writes must survive the
actual joint installation. Agreeing overlaps satisfy this condition; lost
fees, balance credits, and non-monetary field effects do not. -/
def OutcomesPreserved
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (post : CellState.Materialized M) : Prop :=
  forall incidence address,
    address ∈ Patch.writeFootprint (declaration.legPatch incidence) ->
      post.logical address = (declaration.legs incidence).post.logical address

/-- Every source postcondition is evaluated on the one actual composed post,
including invariants which observe addresses written by other incidences. -/
def JointPostconditions
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (post : CellState.Materialized M) : Prop :=
  forall incidence,
    (declaration.legs incidence).family.Postcondition
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome post.logical

def jointDelta
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (post : CellState.Materialized M) : Coordinate -> Balance :=
  law.stateDelta declaration.pre.logical post.logical
    (Patch.writeFootprint declaration.jointPatch)

omit [Fintype Incidence] in
/-- Every leg's write footprint is inside the joint write footprint, once the
order lists every incidence. -/
theorem legFootprint_subset
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (complete : declaration.OrderComplete) (incidence : Incidence) :
    Patch.writeFootprint (declaration.legPatch incidence) ⊆
      Patch.writeFootprint declaration.jointPatch := by
  intro address present
  obtain ⟨op, member, writes⟩ :=
    (Patch.mem_writeFootprint_iff _ address).mp present
  apply (Patch.mem_writeFootprint_iff _ address).mpr
  exact ⟨op, List.mem_flatMap.mpr ⟨incidence, complete.2 incidence, member⟩, writes⟩

end Declaration

/-! ## Proof-relevant joint admission and one prepared post -/

variable
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L Digest}
    {portal : Portal} {projection : AuthorizationProjection L}
    {Incidence : Type z} [Fintype Incidence]
    {Coordinate : Type y}
    {Balance : Type b} [AddCommMonoid Balance]

/-- A committed hyperedge has one verifier-minted validation of the exact
joint patch at the common pre-root, one exact shared apex, and the aggregate
resource law. -/
structure Commit
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) :
    Prop where
  shape : declaration.ShapeValid
  validated : CellState.ValidatedPatch M declaration.pre declaration.pre.root
    declaration.jointPatch
  apexExact : validated.apply.root = declaration.apex
  outcomesPreserved : declaration.OutcomesPreserved validated.apply
  postconditions : declaration.JointPostconditions validated.apply
  jointDeltaExact : declaration.jointDelta law validated.apply =
    declaration.aggregateDelta law
  aggregateBalanced : declaration.aggregateDelta law = 0

namespace Commit

variable
    {law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence}

/-- The unique canonical transition.  Its post and footprint come only from
the validated concatenated patch. -/
def prepared (commit : Commit law declaration) :
    PreparedTurn M declaration.pre (List declaration.JointNullifier) :=
  PreparedTurn.ofValidatedPatch commit.validated
    (some declaration.jointNullifiers)

@[simp] theorem prepared_post (commit : Commit law declaration) :
    commit.prepared.post = commit.validated.apply :=
  rfl

@[simp] theorem prepared_logical (commit : Commit law declaration) :
    commit.prepared.post.logical =
      Patch.run declaration.pre.logical declaration.jointPatch :=
  rfl

@[simp] theorem prepared_preRoot (commit : Commit law declaration) :
    commit.prepared.preRoot = declaration.pre.root :=
  rfl

@[simp] theorem prepared_postRoot (commit : Commit law declaration) :
    commit.prepared.postRoot = declaration.apex :=
  commit.apexExact

@[simp] theorem prepared_footprint (commit : Commit law declaration) :
    commit.prepared.delta.footprint = Patch.writeFootprint declaration.jointPatch :=
  rfl

/-- Conservation concerns the actual installed joint post, even for a
nonlinear resource law or an allowed agreeing overlap. -/
theorem joint_resources_exact (commit : Commit law declaration) :
    declaration.jointDelta law commit.prepared.post = 0 :=
  commit.jointDeltaExact.trans commit.aggregateBalanced

theorem leg_outcome_preserved (commit : Commit law declaration)
    (incidence : Incidence) (address : Address L)
    (present : address ∈ Patch.writeFootprint (declaration.legPatch incidence)) :
    commit.prepared.post.logical address =
      (declaration.legs incidence).post.logical address :=
  commit.outcomesPreserved incidence address present

/-- The very same source relation which admitted the local candidate holds
at the actual jointly installed post, not only at that tentative candidate. -/
theorem leg_postcondition (commit : Commit law declaration) (incidence : Incidence) :
    (declaration.legs incidence).family.Postcondition
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome commit.prepared.post.logical :=
  commit.postconditions incidence

/-- The one frame: no address outside the joint write footprint changes. -/
theorem frame (commit : Commit law declaration)
    (address : Address L)
    (outside : address ∉ Patch.writeFootprint declaration.jointPatch) :
    commit.prepared.post.logical address = declaration.pre.logical address :=
  commit.prepared.delta.frame address outside

/-- Joint composition cannot omit an address written by any accepted leg. -/
theorem leg_footprint_subset (commit : Commit law declaration)
    (incidence : Incidence) :
    Patch.writeFootprint (declaration.legPatch incidence) ⊆
      Patch.writeFootprint declaration.jointPatch :=
  declaration.legFootprint_subset commit.shape.orderComplete incidence

/-- Every incidence retains authority for its own exact request in the shared
authorization state projected from the common pre-cell. -/
def legAuthorization (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (incidence : Incidence) :
    Authorized portal (projection.project declaration.pre.logical)
      (declaration.legs incidence).request :=
  (declaration.legs incidence).authorization

/-! ## Projection to the abstract wide pullback -/

def step (_state : CellState.Materialized M)
    (post : CellState.Materialized M) : CellState.Materialized M :=
  post

def turnId (_incidence : Incidence) (state : CellState.Materialized M) : Digest :=
  state.root

def halfEdge (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (incidence : Incidence) (_state : CellState.Materialized M)
    (_post : CellState.Materialized M) : Coordinate -> Balance :=
  fun coordinate => law.delta (declaration.legs incidence) coordinate

abbrev SemanticHyperedge
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence) :=
  Hyperedge Incidence (CellState.Materialized M) (CellState.Materialized M)
    Digest (Coordinate -> Balance) step (turnId (M := M)) (halfEdge law declaration)

/-- Every leg starts from the one canonical pre-cell and reaches the one
validated joint post/apex.  Conservation is exactly the declared typed law.
The hyperedge's turn is the joint post itself. -/
def toHyperedge (commit : Commit law declaration) :
    SemanticHyperedge law declaration where
  x := fun _ => declaration.pre
  t := commit.prepared.post
  tid := declaration.apex
  agree := by
    intro incidence
    exact commit.apexExact
  balanced := by
    funext coordinate
    simpa only [halfEdge, Declaration.aggregateDelta, Finset.sum_apply,
      Pi.zero_apply] using congrFun commit.aggregateBalanced coordinate

@[simp] theorem hyperedge_apex (commit : Commit law declaration) :
    commit.toHyperedge.tid = declaration.apex :=
  rfl

@[simp] theorem hyperedge_pre (commit : Commit law declaration)
    (incidence : Incidence) :
    commit.toHyperedge.x incidence = declaration.pre :=
  rfl

end Commit

/-! ## Load-bearing refusals -/

/-- Shape, validation, exact authorizations, and even apex agreement cannot
manufacture conservation for a nonzero typed resource coordinate. -/
theorem no_commit_of_nonzero_resource
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (coordinate : Coordinate)
    (nonzero : declaration.aggregateDelta law coordinate ≠ 0) :
    ¬ Commit law declaration :=
  fun commit => nonzero (congrFun commit.aggregateBalanced coordinate)

/-- Local zero-sum equations cannot admit a different actual joint delta. -/
theorem no_commit_of_nonzero_joint_resource
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (coordinate : Coordinate)
    (nonzero : declaration.jointDelta law
      (CellState.materialize M (Patch.run declaration.pre.logical declaration.jointPatch))
        coordinate ≠ 0) :
    ¬ Commit law declaration :=
  fun commit => nonzero (congrFun commit.joint_resources_exact coordinate)

/-- The joint patch is re-validated: if its guards fail at the composed
prefix (for example, a second incidence guards on a value the first already
moved), no commit exists, however valid each leg was on its own. -/
theorem no_commit_of_invalid_joint_patch
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (invalid : ¬ Patch.ValidFrom declaration.pre.logical declaration.jointPatch) :
    ¬ Commit law declaration :=
  fun commit => invalid commit.validated.valid

/-- Even a resource-neutral overwrite is refused when it drops an accepted
outcome, such as a prior fee in a field-stored resource book. -/
theorem no_commit_of_lost_outcome
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (incidence : Incidence) (address : Address L)
    (present : address ∈ Patch.writeFootprint (declaration.legPatch incidence))
    (lost : Patch.run declaration.pre.logical declaration.jointPatch address ≠
      (declaration.legs incidence).post.logical address) :
    ¬ Commit law declaration :=
  fun commit => lost (commit.outcomesPreserved incidence address present)

/-- Disjoint writes and exact local outcomes cannot admit a joint state that
breaks a retained source predicate. -/
theorem no_commit_of_failed_postcondition
    (law : ResourceLaw.{u, v, w, y, b} L M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (incidence : Incidence)
    (failed : ¬ (declaration.legs incidence).family.Postcondition
        (declaration.legs incidence).declaration
        (declaration.legs incidence).outcome
        (Patch.run declaration.pre.logical declaration.jointPatch)) :
    ¬ Commit law declaration :=
  fun commit => failed (commit.postconditions incidence)

/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Leg.request_preRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Leg.request_preRoot
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.prepared_postRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.prepared_postRoot
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_footprint_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_footprint_subset
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.toHyperedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.toHyperedge
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.joint_resources_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.joint_resources_exact
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.frame
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_outcome_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_outcome_preserved
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_postcondition
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_nonzero_resource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_nonzero_resource
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_nonzero_joint_resource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_nonzero_joint_resource
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_invalid_joint_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_invalid_joint_patch
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_lost_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_lost_outcome
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_failed_postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_failed_postcondition

end Minidregg.Kernel.TypedCellHyperedge
