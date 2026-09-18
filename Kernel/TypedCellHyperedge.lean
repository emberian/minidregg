/-
# Kernel.TypedCellHyperedge -- schema-polymorphic accepted-effect hyperedges

This is the generic flat joint-transition nucleus.  Unlike
`Kernel.DeclaredHyperedge`, it is not specialized to the legacy integer-field,
empty-resource schema.  Every incidence is an existing `AcceptedCellEffect`
over one exact canonical pre-cell and one authorization-state projection of
that cell.  The unique joint post is obtained by validating and applying the
ordered concatenation of those effects' typed patches.

Resource replacement packages do not have a schema-independent additive
meaning. Consequently conservation is parameterized by an explicit typed
`ResourceLaw` over actual logical pre/post states and validated footprints.
Both the incidence aggregate and its equality to the actual joint-state delta
are checked. Each accepted field outcome must survive in that joint state.
Every source-owned family postcondition is also required on that actual
joint state; local acceptance cannot hide a broken cross-field invariant.
Canonical order therefore allows agreeing overlaps, not unchecked overwrites
of independently accepted outcomes. Sequentially dependent mutations belong
inside one source-admitted ordered batch.
-/
import Kernel.DeclaredHyperedge
import Theory.AcceptedCellEffect

namespace Minidregg.Kernel.TypedCellHyperedge

open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z b

/-! ## One canonical pre-cell and heterogeneous accepted legs -/

/-- Authorization is projected from the same logical cell consumed by every
effect.  There is no independent ambient authorization state at the joint
transition boundary. -/
structure AuthorizationProjection (S : CellState.Schema.{u, v, w, x}) where
  project : CellState.LogicalState S -> AuthState

/-- A heterogeneous accepted semantic effect, packaged as one incidence.
The family, request, declaration, outcome, proof mode, validated patch, and
request-indexed authorization all remain recoverable from `accepted`. -/
structure Leg
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (portal : Portal) (authState : AuthState)
    (pre : CellState.Materialized M) : Type (max u v w x (y + 1) (z + 1)) where
  Nullifier : Type y
  family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier
  kind : ResourceKind
  request : Request kind
  declaration : family.Declaration
  outcome : family.Outcome declaration
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    family request pre declaration outcome

namespace Leg

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {authState : AuthState}
    {pre : CellState.Materialized M}

/-- The exact patch already validated by this incidence's accepted effect. -/
def patch (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    CellState.Patch S Digest :=
  leg.family.patch leg.declaration leg.outcome

/-- The incidence-local canonical post.  This is retained even though the
joint transition below has one separately composed post. -/
def post (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    CellState.Materialized M :=
  leg.accepted.prepared.post

@[simp] theorem request_preRoot
    (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    leg.request.preStateRoot = pre.root :=
  leg.accepted.preRootBound

@[simp] theorem request_effectsDigest
    (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    leg.request.effectsDigest =
      leg.family.effectDigest leg.declaration :=
  leg.accepted.effectsDigestBound

/-- Exact request-indexed authority is retained, not summarized by a Boolean. -/
def authorization
    (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    Authorized portal authState leg.request :=
  leg.accepted.authorization

@[simp] theorem post_exact
    (leg : Leg.{u, v, w, x, y, z} portal authState pre) :
    leg.post = leg.accepted.validated.apply :=
  rfl

end Leg

/-! ## Flat shape and deterministic patch composition -/

inductive FieldCompositionMode
  | disjoint
  /-- A fixed patch order whose accepted field outcomes must all survive.
  `Commit.fieldsPreserved` is mandatory even when structural overlap is allowed. -/
  | canonical
  deriving DecidableEq, Repr

structure CompositionPlan (Incidence : Type z) where
  fieldMode : FieldCompositionMode
  order : List Incidence

/-- A resource law measures the actual logical-state change over the exact
validated footprints. The same source-owned primitive is used for each leg
and for the joint post; there is no independently supplied aggregate meaning.
Its explicit evidence universe preserves the existing heterogeneous-leg API. -/
structure ResourceLaw
    (S : CellState.Schema.{u, v, w, x})
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Digest) (portal : Portal)
    (Coordinate : Type y) (Balance : Type b) [AddCommMonoid Balance] :
    Type (max u v w x y z b) where
  stateDelta : CellState.LogicalState S -> CellState.LogicalState S ->
    Finset S.Field -> Finset S.Resource -> Coordinate -> Balance

def ResourceLaw.delta
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {portal : Portal}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    {authState : AuthState} {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, x, y, z} portal authState pre) : Coordinate -> Balance :=
  law.stateDelta pre.logical leg.post.logical
    leg.patch.fieldFootprint leg.patch.resourceFootprint

/-- One flat family of accepted incidences.  All legs are definitionally
indexed by the same canonical pre-cell and by the authorization projection of
that exact cell. -/
structure Declaration
    (S : CellState.Schema.{u, v, w, x})
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S Digest)
    (portal : Portal) (projection : AuthorizationProjection S)
    (Incidence : Type z) where
  pre : CellState.Materialized M
  apex : Digest
  legs : Incidence -> Leg.{u, v, w, x, y, z} portal
    (projection.project pre.logical) pre
  composition : CompositionPlan Incidence

namespace Declaration

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]

def legPatch
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (incidence : Incidence) : CellState.Patch S Digest :=
  (declaration.legs incidence).patch

/-- The sole raw joint patch.  Declared footprints are recomputed from the
actual concatenated typed writes, so joint validation can contain neither an
undeclared write nor a ghost key. -/
def jointPatch
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
    CellState.Patch S Digest where
  expectedPreRoot := declaration.pre.root
  fieldWrites := declaration.composition.order.flatMap fun incidence =>
    (declaration.legPatch incidence).fieldWrites
  resourceWrites := declaration.composition.order.flatMap fun incidence =>
    (declaration.legPatch incidence).resourceWrites
  fieldFootprint :=
    ((declaration.composition.order.flatMap fun incidence =>
      (declaration.legPatch incidence).fieldWrites).map
        CellState.FieldWrite.field).toFinset
  resourceFootprint :=
    ((declaration.composition.order.flatMap fun incidence =>
      (declaration.legPatch incidence).resourceWrites).map
        CellState.ResourceWrite.resource).toFinset

def OrderComplete
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) : Prop :=
  declaration.composition.order.Nodup /\
    forall incidence, incidence ∈ declaration.composition.order

def FieldFootprintsDisjoint
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) : Prop :=
  forall left right, left ≠ right ->
    Disjoint (declaration.legPatch left).fieldFootprint
      (declaration.legPatch right).fieldFootprint

/-- Resource packages are authority/evidence-indexed replacements, so two
independently accepted legs may not both replace the same resource. -/
def ResourceFootprintsDisjoint
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) : Prop :=
  forall left right, left ≠ right ->
    Disjoint (declaration.legPatch left).resourceFootprint
      (declaration.legPatch right).resourceFootprint

structure ShapeValid
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) : Prop where
  orderComplete : declaration.OrderComplete
  resourcesDisjoint : declaration.ResourceFootprintsDisjoint
  fieldsValid :
    match declaration.composition.fieldMode with
    | .disjoint => declaration.FieldFootprintsDisjoint
    | .canonical => True

/-- Heterogeneous eager nullifiers are retained with their incidence index. -/
def JointNullifier
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) : Type _ :=
  Sigma fun incidence => (declaration.legs incidence).Nullifier

def jointNullifiers
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
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
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
    Coordinate -> Balance :=
  fun coordinate => Finset.univ.sum fun incidence =>
    law.delta (declaration.legs incidence) coordinate

/-- Every incidence's final value on each field it owns must survive the
actual joint installation. Agreeing overlaps satisfy this condition; lost
fees, balance credits, and non-monetary field effects do not. -/
def FieldOutcomesPreserved
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (post : CellState.Materialized M) : Prop :=
  forall incidence field, field ∈ (declaration.legPatch incidence).fieldFootprint ->
    post.logical.fields field = (declaration.legs incidence).post.logical.fields field

/-- Every source postcondition is evaluated on the one actual composed post,
including invariants which observe fields written by other incidences. -/
def JointPostconditions
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (post : CellState.Materialized M) : Prop :=
  forall incidence,
    (declaration.legs incidence).family.Postcondition
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome post.logical

def jointDelta
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (post : CellState.Materialized M) : Coordinate -> Balance :=
  law.stateDelta declaration.pre.logical post.logical
    declaration.jointPatch.fieldFootprint declaration.jointPatch.resourceFootprint

/-- The concatenated patch has its exact derived root and named footprints.
Semantic composition and conservation remain separate mandatory commit
conditions; structural patch validation alone does not admit a joint turn. -/
theorem jointPatch_validated
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
    Nonempty (CellState.ValidatedPatch M declaration.pre declaration.jointPatch) := by
  have witness : ∃ validated :
      CellState.ValidatedPatch M declaration.pre declaration.jointPatch,
      CellState.validate M declaration.pre declaration.jointPatch =
        CellState.ValidationOutcome.accepted validated := by
    unfold CellState.validate
    rw [dif_pos (show declaration.jointPatch.expectedPreRoot = declaration.pre.root from rfl)]
    rw [dif_pos (show declaration.jointPatch.fieldFootprint =
      declaration.jointPatch.namedFields from rfl)]
    rw [dif_pos (show declaration.jointPatch.resourceFootprint =
      declaration.jointPatch.namedResources from rfl)]
    exact ⟨_, rfl⟩
  exact ⟨witness.choose⟩

noncomputable def jointValidated
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
    CellState.ValidatedPatch M declaration.pre declaration.jointPatch :=
  Classical.choice declaration.jointPatch_validated

end Declaration

/-! ## Proof-relevant joint admission and one prepared post -/

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y}
    {Balance : Type b} [AddCommMonoid Balance]

/-- A committed generic hyperedge has one verifier-minted validation for the
exact joint patch, one exact shared apex, and the aggregate resource law. -/
structure Commit
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence) :
    Type (max u v w x y z b) where
  shape : declaration.ShapeValid
  validated : CellState.ValidatedPatch M declaration.pre declaration.jointPatch
  apexExact : validated.apply.root = declaration.apex
  fieldsPreserved : declaration.FieldOutcomesPreserved validated.apply
  postconditions : declaration.JointPostconditions validated.apply
  jointDeltaExact : declaration.jointDelta law validated.apply =
    declaration.aggregateDelta law
  aggregateBalanced : declaration.aggregateDelta law = 0

namespace Commit

variable
    {law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}

/-- The unique canonical transition.  Its post and both footprints come only
from the validated concatenated patch. -/
def prepared (commit : Commit law declaration) :
    PreparedTurn M declaration.pre (List declaration.JointNullifier) :=
  PreparedTurn.ofValidatedPatch commit.validated
    (some declaration.jointNullifiers)

@[simp] theorem prepared_post (commit : Commit law declaration) :
    commit.prepared.post = commit.validated.apply :=
  rfl

@[simp] theorem prepared_preRoot (commit : Commit law declaration) :
    commit.prepared.preRoot = declaration.pre.root :=
  rfl

@[simp] theorem prepared_postRoot (commit : Commit law declaration) :
    commit.prepared.postRoot = declaration.apex :=
  commit.apexExact

@[simp] theorem prepared_fieldFootprint (commit : Commit law declaration) :
    commit.prepared.delta.fieldFootprint = declaration.jointPatch.fieldFootprint :=
  rfl

@[simp] theorem prepared_resourceFootprint (commit : Commit law declaration) :
    commit.prepared.delta.resourceFootprint =
      declaration.jointPatch.resourceFootprint :=
  rfl

/-- Conservation concerns the actual installed joint post, even for a
nonlinear resource law or an allowed agreeing field overlap. -/
theorem joint_resources_exact (commit : Commit law declaration) :
    declaration.jointDelta law commit.prepared.post = 0 :=
  commit.jointDeltaExact.trans commit.aggregateBalanced

theorem leg_field_outcome_preserved (commit : Commit law declaration)
    (incidence : Incidence) (field : S.Field)
    (present : field ∈ (declaration.legPatch incidence).fieldFootprint) :
    commit.prepared.post.logical.fields field =
      (declaration.legs incidence).post.logical.fields field :=
  commit.fieldsPreserved incidence field present

/-- The very same source relation which admitted the local candidate holds
at the actual jointly installed post, not only at that tentative candidate. -/
theorem leg_postcondition (commit : Commit law declaration) (incidence : Incidence) :
    (declaration.legs incidence).family.Postcondition
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome commit.prepared.post.logical :=
  commit.postconditions incidence

theorem field_frame (commit : Commit law declaration)
    (field : S.Field) (outside : field ∉ declaration.jointPatch.fieldFootprint) :
    commit.prepared.post.logical.fields field =
      declaration.pre.logical.fields field :=
  commit.prepared.delta.fieldFrame field (by
    simpa only [prepared_fieldFootprint] using outside)

theorem resource_frame (commit : Commit law declaration)
    (resource : S.Resource)
    (outside : resource ∉ declaration.jointPatch.resourceFootprint) :
    commit.prepared.post.logical.resources resource =
      declaration.pre.logical.resources resource :=
  commit.prepared.delta.resourceFrame resource (by
    simpa only [prepared_resourceFootprint] using outside)

/-- Joint composition cannot omit a field declared by any accepted leg. -/
theorem leg_fieldFootprint_subset (commit : Commit law declaration)
    (incidence : Incidence) :
    (declaration.legPatch incidence).fieldFootprint ⊆
      declaration.jointPatch.fieldFootprint := by
  intro field present
  have named : field ∈ (declaration.legPatch incidence).namedFields := by
    have footprintExact :
        (declaration.legPatch incidence).fieldFootprint =
          (declaration.legPatch incidence).namedFields := by
      simpa only [Declaration.legPatch, Leg.patch] using
        (declaration.legs incidence).accepted.validated.fields_exact
    rw [← footprintExact]
    exact present
  rcases (by
      simpa [CellState.Patch.namedFields] using named :
        ∃ write ∈ (declaration.legPatch incidence).fieldWrites,
          write.field = field) with ⟨write, writePresent, writeField⟩
  have inJoint : write ∈
      declaration.composition.order.flatMap fun index =>
        (declaration.legPatch index).fieldWrites := by
    rw [List.mem_flatMap]
    exact ⟨incidence, commit.shape.orderComplete.2 incidence, writePresent⟩
  simp only [Declaration.jointPatch, List.mem_toFinset, List.mem_map]
  exact ⟨write, inJoint, writeField⟩

/-- Joint composition cannot omit a resource package declared by any accepted
leg.  Together with `ShapeValid.resourcesDisjoint`, this gives every package
write one unambiguous owning incidence. -/
theorem leg_resourceFootprint_subset (commit : Commit law declaration)
    (incidence : Incidence) :
    (declaration.legPatch incidence).resourceFootprint ⊆
      declaration.jointPatch.resourceFootprint := by
  intro resource present
  have named : resource ∈
      (declaration.legPatch incidence).namedResources := by
    have footprintExact :
        (declaration.legPatch incidence).resourceFootprint =
          (declaration.legPatch incidence).namedResources := by
      simpa only [Declaration.legPatch, Leg.patch] using
        (declaration.legs incidence).accepted.validated.resources_exact
    rw [← footprintExact]
    exact present
  rcases (by
      simpa [CellState.Patch.namedResources] using named :
        ∃ write ∈ (declaration.legPatch incidence).resourceWrites,
          write.resource = resource) with ⟨write, writePresent, writeResource⟩
  have inJoint : write ∈
      declaration.composition.order.flatMap fun index =>
        (declaration.legPatch index).resourceWrites := by
    rw [List.mem_flatMap]
    exact ⟨incidence, commit.shape.orderComplete.2 incidence, writePresent⟩
  simp only [Declaration.jointPatch, List.mem_toFinset, List.mem_map]
  exact ⟨write, inJoint, writeResource⟩

/-- Every incidence retains authority for its own exact request in the shared
authorization state projected from the common pre-cell. -/
def legAuthorization (commit : Commit law declaration) (incidence : Incidence) :
    Authorized portal (projection.project declaration.pre.logical)
      (declaration.legs incidence).request :=
  (declaration.legs incidence).authorization

/-! ## Projection to the abstract wide pullback -/

def step (_state : CellState.Materialized M) (turn : Commit law declaration) :
    CellState.Materialized M :=
  turn.prepared.post

def turnId (_incidence : Incidence) (state : CellState.Materialized M) : Digest :=
  state.root

def halfEdge (incidence : Incidence) (_state : CellState.Materialized M)
    (_turn : Commit law declaration) : Coordinate -> Balance :=
  fun coordinate => law.delta (declaration.legs incidence) coordinate

abbrev SemanticHyperedge (commit : Commit law declaration) :=
  Hyperedge Incidence (CellState.Materialized M) (Commit law declaration)
    Digest (Coordinate -> Balance) step turnId halfEdge

/-- Every leg starts from the one canonical pre-cell and reaches the one
validated joint post/apex.  Conservation is exactly the declared typed law. -/
def toHyperedge (commit : Commit law declaration) :
    SemanticHyperedge commit where
  x := fun _ => declaration.pre
  t := commit
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

/-! ## Load-bearing conservation negative -/

/-- Shape, validation, exact authorizations, and even apex agreement cannot
manufacture conservation for a nonzero typed resource coordinate. -/
theorem no_commit_of_nonzero_resource
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (coordinate : Coordinate)
    (nonzero : declaration.aggregateDelta law coordinate ≠ 0) :
    IsEmpty (Commit law declaration) :=
  ⟨fun commit => nonzero (congrFun commit.aggregateBalanced coordinate)⟩

/-- Local zero-sum equations cannot admit a different actual joint delta. -/
theorem no_commit_of_nonzero_joint_resource
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (coordinate : Coordinate)
    (nonzero : forall validated :
      CellState.ValidatedPatch M declaration.pre declaration.jointPatch,
      declaration.jointDelta law validated.apply coordinate ≠ 0) :
    IsEmpty (Commit law declaration) :=
  ⟨fun commit => nonzero commit.validated
    (congrFun commit.joint_resources_exact coordinate)⟩

/-- Even a resource-neutral overwrite is refused when it drops an accepted
field outcome, such as a prior fee in a field-stored resource book. -/
theorem no_commit_of_lost_field
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (incidence : Incidence) (field : S.Field)
    (present : field ∈ (declaration.legPatch incidence).fieldFootprint)
    (lost : forall validated :
      CellState.ValidatedPatch M declaration.pre declaration.jointPatch,
      validated.apply.logical.fields field ≠
        (declaration.legs incidence).post.logical.fields field) :
    IsEmpty (Commit law declaration) :=
  ⟨fun commit => lost commit.validated (commit.fieldsPreserved incidence field present)⟩

/-- Disjoint writes and exact local outcomes cannot admit a joint state that
breaks a retained source predicate. -/
theorem no_commit_of_failed_postcondition
    (law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance)
    (declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence)
    (incidence : Incidence)
    (failed : forall validated :
      CellState.ValidatedPatch M declaration.pre declaration.jointPatch,
      ¬ (declaration.legs incidence).family.Postcondition
        (declaration.legs incidence).declaration
        (declaration.legs incidence).outcome validated.apply.logical) :
    IsEmpty (Commit law declaration) :=
  ⟨fun commit => failed commit.validated (commit.postconditions incidence)⟩

/-! ## Resource-package outcomes survive disjoint composition -/

namespace ResourceWriteComposition

variable {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Resource]

theorem applyResourceWrites_append
    (left right : List (CellState.ResourceWrite S))
    (resources : (resource : S.Resource) -> CellState.ResourceCell S resource) :
    CellState.applyResourceWrites (left ++ right) resources =
      CellState.applyResourceWrites right
        (CellState.applyResourceWrites left resources) := by
  induction left generalizing resources with
  | nil => rfl
  | cons write rest ih =>
      exact ih _

/-- The final read at one resource depends only on its initial read and the
fixed ordered writes, even though complete resource packages are dependent. -/
theorem applyResourceWrites_read_congr
    (writes : List (CellState.ResourceWrite S))
    (left right : (resource : S.Resource) -> CellState.ResourceCell S resource)
    (resource : S.Resource) (agree : left resource = right resource) :
    CellState.applyResourceWrites writes left resource =
      CellState.applyResourceWrites writes right resource := by
  induction writes generalizing left right with
  | nil => exact agree
  | cons write rest ih =>
      apply ih
      by_cases same : resource = write.resource
      · subst resource
        simp only [Function.update_self]
      · simpa only [Function.update_of_ne same] using agree

theorem applyResourceWrites_flatMap_frame
    {Index : Type y} (writes : Index -> List (CellState.ResourceWrite S))
    (order : List Index)
    (resources : (resource : S.Resource) -> CellState.ResourceCell S resource)
    (resource : S.Resource)
    (outside : ∀ index ∈ order,
      resource ∉ ((writes index).map CellState.ResourceWrite.resource).toFinset) :
    CellState.applyResourceWrites (order.flatMap writes) resources resource =
      resources resource := by
  apply CellState.applyResourceWrites_frame
  intro present
  rcases List.mem_map.mp (List.mem_toFinset.mp present) with
    ⟨write, writePresent, writeResource⟩
  rcases List.mem_flatMap.mp writePresent with ⟨index, indexPresent, writePresent⟩
  exact outside index indexPresent
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨write, writePresent, writeResource⟩))

/-- Concatenating pairwise resource-disjoint legs preserves the full local
outcome at a resource of its unique owning incidence. -/
theorem applyResourceWrites_flatMap_owner
    {Index : Type y} [DecidableEq Index]
    (writes : Index -> List (CellState.ResourceWrite S))
    (order : List Index) (owner : Index) (resource : S.Resource) :
    order.Nodup -> owner ∈ order ->
    (∀ other ∈ order, other ≠ owner ->
      resource ∉ ((writes other).map CellState.ResourceWrite.resource).toFinset) ->
    forall resources : (resource : S.Resource) -> CellState.ResourceCell S resource,
      CellState.applyResourceWrites (order.flatMap writes) resources resource =
        CellState.applyResourceWrites (writes owner) resources resource := by
  induction order with
  | nil =>
      intro _ ownerPresent
      cases ownerPresent
  | cons first rest ih =>
      intro nodup ownerPresent outside resources
      have nodupRest := List.nodup_cons.mp nodup
      rw [List.flatMap_cons, applyResourceWrites_append]
      by_cases same : first = owner
      · subst first
        apply applyResourceWrites_flatMap_frame
        intro other otherPresent
        apply outside other (List.mem_cons_of_mem owner otherPresent)
        intro same
        subst other
        exact nodupRest.1 otherPresent
      · have ownerRest : owner ∈ rest := by
          rcases List.mem_cons.mp ownerPresent with equal | present
          · exact False.elim (same equal.symm)
          · exact present
        have outsideRest : ∀ other ∈ rest, other ≠ owner ->
            resource ∉ ((writes other).map CellState.ResourceWrite.resource).toFinset := by
          intro other present different
          exact outside other (List.mem_cons_of_mem first present) different
        rw [ih nodupRest.2 ownerRest outsideRest]
        apply applyResourceWrites_read_congr
        exact CellState.applyResourceWrites_frame (writes first) resources resource
          (outside first List.mem_cons_self same)

end ResourceWriteComposition

namespace Commit

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {portal : Portal} {projection : AuthorizationProjection S}
    {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    {law : ResourceLaw.{u, v, w, x, y, z, b} S M portal Coordinate Balance}
    {declaration : Declaration.{u, v, w, x, y, z} S M portal projection Incidence}

/-- Resource disjointness forces every accepted authority/evidence package to
survive in the actual joint post. No additional admission premise is needed. -/
theorem leg_resource_outcome_preserved (commit : Commit law declaration)
    (incidence : Incidence) (resource : S.Resource)
    (present : resource ∈ (declaration.legPatch incidence).resourceFootprint) :
    commit.prepared.post.logical.resources resource =
      (declaration.legs incidence).post.logical.resources resource := by
  change CellState.applyResourceWrites
      (declaration.composition.order.flatMap fun other =>
        (declaration.legPatch other).resourceWrites)
      declaration.pre.logical.resources resource =
    CellState.applyResourceWrites (declaration.legPatch incidence).resourceWrites
      declaration.pre.logical.resources resource
  refine ResourceWriteComposition.applyResourceWrites_flatMap_owner
    (fun other => (declaration.legPatch other).resourceWrites)
    declaration.composition.order incidence resource
    commit.shape.orderComplete.1 (commit.shape.orderComplete.2 incidence)
    ?_ declaration.pre.logical.resources
  intro other _ different
  have footprintExact :
      (declaration.legPatch other).resourceFootprint =
        ((declaration.legPatch other).resourceWrites.map
          CellState.ResourceWrite.resource).toFinset :=
    (declaration.legs other).accepted.validated.resources_exact
  rw [← footprintExact]
  exact (Finset.disjoint_left.mp
    (commit.shape.resourcesDisjoint incidence other (Ne.symm different))) present

end Commit


/-! ## Exact legacy migration boundary

The old executable module remains useful while callers migrate, but it cannot
itself manufacture `AcceptedCellEffect`: its effect declaration has no lawful
semantic-family codec, its patch is an integer-store program rather than a
`CellState.Patch`, and its committed token retains authorization under
`Nonempty`.  The certificate below states the complete adapter obligation.  It
is intentionally proof-relevant; a digest-only or root-only shim is not an
adapter.
-/

namespace LegacyAdapter

local instance effectSchemaFieldDecidableEq :
    DecidableEq Minidregg.Theory.DeclaredTurn.effectSchema.Field := by
  change DecidableEq Minidregg.Theory.EffectDeclaration.StateKey
  infer_instance

local instance effectSchemaResourceDecidableEq :
    DecidableEq Minidregg.Theory.DeclaredTurn.effectSchema.Resource := by
  change DecidableEq Empty
  infer_instance

variable
    {legacyMaterializer : CellState.Materializer
      Minidregg.Theory.DeclaredTurn.effectSchema Digest}
    {legacyPortal : Portal}
    {LegacyIncidence : Type} [Fintype LegacyIncidence]
    [DecidableEq LegacyIncidence]

/-- The old authorization projection embeds without reinterpretation. -/
def authorizationProjection
    (legacy : Minidregg.Kernel.DeclaredHyperedge.AuthorizationProjection
      legacyMaterializer) :
    AuthorizationProjection Minidregg.Theory.DeclaredTurn.effectSchema where
  project := legacy.project

/-- Exact obligations for replacing one old declaration by the generic typed
kernel.  In particular, each accepted leg must execute the old leg's patch,
the one joint post must execute the old joint patch, and the full-width legacy
resource vector must be the generic conservation vector. -/
structure Certificate
    (legacyProjection : Minidregg.Kernel.DeclaredHyperedge.AuthorizationProjection
      legacyMaterializer)
    (legacy : Minidregg.Kernel.DeclaredHyperedge.Declaration
      legacyPortal legacyMaterializer LegacyIncidence)
    (typed : Declaration
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      (authorizationProjection legacyProjection) LegacyIncidence)
    (law : ResourceLaw
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      Digest Int) : Prop where
  preExact : typed.pre = legacy.pre
  apexExact : typed.apex = legacy.apex
  kindExact : forall incidence,
    (typed.legs incidence).kind = (legacy.legs incidence).kind
  requestExact : forall incidence,
    HEq (typed.legs incidence).request (legacy.legs incidence).request
  legFieldFootprintExact : forall incidence,
    (typed.legPatch incidence).fieldFootprint =
      (legacy.legs incidence).effects.footprint.toFinset
  legResourceFootprintEmpty : forall incidence,
    (typed.legPatch incidence).resourceFootprint = ∅
  legPostLogicalExact : forall incidence,
    (typed.legs incidence).post.logical =
      legacy.logicalOfStore
        (Minidregg.Theory.EffectDeclaration.applyPatch
          (legacy.legs incidence).effects.patch legacy.preStore)
  jointPostLogicalExact : forall
      validated : CellState.ValidatedPatch legacyMaterializer typed.pre
        typed.jointPatch,
    validated.apply.logical =
      legacy.logicalOfStore
        (Minidregg.Theory.EffectDeclaration.applyPatch
          legacy.patch legacy.preStore)
  aggregateExact : typed.aggregateDelta law = legacy.aggregateDelta

theorem committed_post_matches_legacy
    {legacyProjection : Minidregg.Kernel.DeclaredHyperedge.AuthorizationProjection
      legacyMaterializer}
    {legacy : Minidregg.Kernel.DeclaredHyperedge.Declaration
      legacyPortal legacyMaterializer LegacyIncidence}
    {typed : Declaration
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      (authorizationProjection legacyProjection) LegacyIncidence}
    {law : ResourceLaw
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      Digest Int}
    (certificate : Certificate legacyProjection legacy typed law)
    (commit : Commit law typed) :
    commit.prepared.post.logical =
      legacy.logicalOfStore
        (Minidregg.Theory.EffectDeclaration.applyPatch
          legacy.patch legacy.preStore) :=
  certificate.jointPostLogicalExact commit.validated

theorem committed_balance_matches_legacy
    {legacyProjection : Minidregg.Kernel.DeclaredHyperedge.AuthorizationProjection
      legacyMaterializer}
    {legacy : Minidregg.Kernel.DeclaredHyperedge.Declaration
      legacyPortal legacyMaterializer LegacyIncidence}
    {typed : Declaration
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      (authorizationProjection legacyProjection) LegacyIncidence}
    {law : ResourceLaw
      Minidregg.Theory.DeclaredTurn.effectSchema legacyMaterializer legacyPortal
      Digest Int}
    (certificate : Certificate legacyProjection legacy typed law)
    (commit : Commit law typed) :
    legacy.aggregateDelta = 0 := by
  rw [← certificate.aggregateExact]
  exact commit.aggregateBalanced

/-
Named construction residuals:

* `[TYPED-HYPEREDGE-LEGACY-FAMILY]`: give legacy effect declarations lawful
  first-order codecs and a `SemanticEffectFamily` whose validated typed patch
  is extensionally the existing `EffectDeclaration.applyPatch`.
* `[TYPED-HYPEREDGE-LEGACY-AUTH]`: change the legacy committed carrier from
  `Nonempty (Authorized ...)` to the accepted-cell positive path, or expose
  only `Nonempty` generic commits.  Do not use classical choice to invent a
  computational authorization witness.
* `[TYPED-HYPEREDGE-HISTORY]`: migrate receipt/history admission to consume
  the generic commit and its complete incidence/request family.
-/

end LegacyAdapter

/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Leg.request_preRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Leg.request_preRoot
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.prepared_postRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.prepared_postRoot
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_resourceFootprint_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_resourceFootprint_subset
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_resource_outcome_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_resource_outcome_preserved
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.toHyperedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.toHyperedge
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.joint_resources_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.joint_resources_exact
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_field_outcome_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_field_outcome_preserved
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.Commit.leg_postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.leg_postcondition
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_nonzero_resource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_nonzero_resource
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_nonzero_joint_resource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_nonzero_joint_resource
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_lost_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_lost_field
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.no_commit_of_failed_postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_failed_postcondition
/-- info: 'Minidregg.Kernel.TypedCellHyperedge.LegacyAdapter.committed_post_matches_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LegacyAdapter.committed_post_matches_legacy

end Minidregg.Kernel.TypedCellHyperedge
