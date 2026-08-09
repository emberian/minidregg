/-
# Kernel.DeclaredHyperedge -- executable typed hyperedges

This module is the executable semantic replacement for a state-threaded call
forest.  A joint declaration is flat: a finite family of typed incidences, one
canonical pre-cell, one shared apex, and one explicit patch-composition plan.
Each incidence's complete authorization request is derived from that same
pre-root, its existing typed effect declaration, and the shared apex.  The
authorization state is likewise a projection of the same canonical pre-cell.

No authorization, effect, cell, or receipt interpreter is duplicated here.
The module delegates to `AuthorizationDeclaration.verify`, derives patches and
full-width deltas through `EffectDeclaration`, materializes through `CellState`,
uses `CanonicalTransition.PreparedTurn` for the common canonical transition,
and specializes `Kernel.Hyperedge` to the admitted joint turn.
-/
import Kernel.Turn
import Theory.CanonicalTransition

namespace Minidregg.Kernel.DeclaredHyperedge

open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.CellState

set_option autoImplicit false

local instance effectSchemaFieldDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Field := by
  change DecidableEq StateKey
  infer_instance

local instance effectSchemaResourceDecidableEq :
    DecidableEq DeclaredTurn.effectSchema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## Authorization and request derivation from one canonical pre-cell -/

/-- A system integration supplies one total authorization projection from the
same logical cell which effect execution consumes.  `execute` never accepts an
independent `AuthState`, so authorization and effect evaluation cannot be
pointed at different pre-cells. -/
structure AuthorizationProjection
    (materializer : Materializer DeclaredTurn.effectSchema Digest) where
  project : LogicalState DeclaredTurn.effectSchema -> AuthState

/-- Per-incidence request data.  The shared apex, effects digest, and pre-root
are deliberately absent: `Seed.derive` supplies them from the joint
declaration. -/
structure Seed (kind : ResourceKind) where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  target : ResourceId kind
  verb : Verb kind
  nonce : Nat
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  cost : Nat

/-- Reuse `DeclaredTurn.RequestSeed.derive`; the shared apex occupies the
request's argument commitment, while the existing effect declaration and
canonical materialization own the other two derived commitments. -/
def Seed.derive {kind : ResourceKind} (seed : Seed kind)
    (apex effectsDigest preStateRoot : Digest) : Request kind :=
  (DeclaredTurn.RequestSeed.mk seed.domain seed.semantics seed.federation
    seed.subject seed.subjectKeyEpoch seed.target seed.verb apex seed.nonce
    seed.height seed.policyId seed.policyEpoch seed.cost).derive
      effectsDigest preStateRoot

/-- One incidence.  Its presentation is indexed by the exact request derived
from this effect declaration, the common pre-root, and the common apex. -/
structure Leg (portal : Portal) (preRoot apex : Digest) where
  kind : ResourceKind
  seed : Seed kind
  effects : EffectDeclaration.Declaration seed.target
  presentation : Presentation portal (seed.derive apex effects.digest preRoot)

def Leg.request {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : Request leg.kind :=
  leg.seed.derive apex leg.effects.digest preRoot

@[simp] theorem Leg.request_target {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : leg.request.target = leg.seed.target := rfl

@[simp] theorem Leg.request_apex {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : leg.request.argsDigest = apex := rfl

@[simp] theorem Leg.request_effectsDigest
    {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) :
    leg.request.effectsDigest = leg.effects.digest := rfl

@[simp] theorem Leg.request_preRoot {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : leg.request.preStateRoot = preRoot := rfl

/-! ## Flat incidence shape and derived joint effect -/

/-- Kind plus identifier, used only for finite cross-incidence comparisons. -/
structure TargetKey where
  kindTag : Nat
  target : Nat
  deriving DecidableEq, Repr

def Leg.targetKey {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : TargetKey :=
  { kindTag := resourceKindTag leg.kind
    target := leg.seed.target.value }

/-- The account target, exactly when this is an account incidence. -/
def Leg.accountTarget? {portal : Portal} {preRoot apex : Digest}
    (leg : Leg portal preRoot apex) : Option (ResourceId .account) :=
  match kindEq : leg.kind with
  | .account => some (kindEq ▸ leg.seed.target)
  | .object => none
  | .program => none

/-- Every typed state key has exactly one primary resource target. -/
def stateKeyTarget : StateKey -> TargetKey
  | .objectField object _ => ⟨resourceKindTag .object, object.value⟩
  | .accountBalance account _ => ⟨resourceKindTag .account, account.value⟩
  | .programCode program => ⟨resourceKindTag .program, program.value⟩

/-- Overlap is either forbidden or interpreted in one declared total order.
Even the disjoint mode carries an order so executable serialization is unique. -/
inductive CompositionMode
  | disjoint
  | canonical
  deriving DecidableEq, Repr

structure CompositionPlan (Incidence : Type) where
  mode : CompositionMode
  order : List Incidence

/-- One flat joint declaration.  `legs` is a finite family indexed directly by
incidence; no parent/child execution shape is present. -/
structure Declaration
    (portal : Portal)
    (materializer : Materializer DeclaredTurn.effectSchema Digest)
    (Incidence : Type) where
  pre : Materialized materializer
  apex : Digest
  legs : Incidence -> Leg portal pre.root apex
  composition : CompositionPlan Incidence

variable {portal : Portal}
variable {materializer : Materializer DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

def Declaration.preStore
    (declaration : Declaration portal materializer Incidence) : Store :=
  DeclaredTurn.storeOfLogical declaration.pre.logical

def Declaration.authState
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) : AuthState :=
  projection.project declaration.pre.logical

@[simp] theorem Declaration.authState_same_pre
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    declaration.authState projection = projection.project declaration.pre.logical := rfl

/-- Canonical joint patch: existing per-leg patches, concatenated in the sole
declared order. -/
def Declaration.patch
    (declaration : Declaration portal materializer Incidence) : List Mutation :=
  declaration.composition.order.flatMap fun incidence =>
    (declaration.legs incidence).effects.patch

def Declaration.footprint
    (declaration : Declaration portal materializer Incidence) : List StateKey :=
  (declaration.patch.map Mutation.key).eraseDups

def Declaration.jointDeltas
    (declaration : Declaration portal materializer Incidence) : List BalanceDelta :=
  declaration.composition.order.flatMap fun incidence =>
    (declaration.legs incidence).effects.deltas

def Declaration.resources
    (declaration : Declaration portal materializer Incidence) : List Digest :=
  (declaration.jointDeltas.map BalanceDelta.resource).eraseDups

/-- Delta at one exact account/resource coordinate. -/
def accountDeltaSum (deltas : List BalanceDelta)
    (account : ResourceId .account) (resource : Digest) : Int :=
  (deltas.map fun delta =>
    if delta.account = account && delta.resource = resource
    then delta.amount else 0).sum

/-- An incidence receives the account half-deltas addressed to its exact target.
Object/program incidences have the zero balance vector.  In particular, the two
halves of an existing `accountMove` are assigned to the source and destination
incidences without adding a second effect interpretation. -/
def Declaration.halfDelta
    (declaration : Declaration portal materializer Incidence)
    (incidence : Incidence) : Digest -> Int :=
  match (declaration.legs incidence).accountTarget? with
  | some account => fun resource =>
      accountDeltaSum declaration.jointDeltas account resource
  | none => fun _ => 0

/-- Full-width aggregate over every incidence. -/
def Declaration.aggregateDelta
    (declaration : Declaration portal materializer Incidence) : Digest -> Int :=
  fun resource => Finset.univ.sum fun incidence =>
    declaration.halfDelta incidence resource

/-! ## Executable shape, authorization, balance, and guard checks -/

def Declaration.TargetsUnique
    (declaration : Declaration portal materializer Incidence) : Prop :=
  Function.Injective fun incidence => (declaration.legs incidence).targetKey

def Declaration.OrderComplete
    (declaration : Declaration portal materializer Incidence) : Prop :=
  declaration.composition.order.Nodup /\
    forall incidence, incidence ∈ declaration.composition.order

def Declaration.FootprintsDisjoint
    (declaration : Declaration portal materializer Incidence) : Prop :=
  forall left right, left ≠ right ->
    Disjoint ((declaration.legs left).effects.footprint.toFinset)
      ((declaration.legs right).effects.footprint.toFinset)

def Declaration.CompositionValid
    (declaration : Declaration portal materializer Incidence) : Prop :=
  declaration.OrderComplete /\
    match declaration.composition.mode with
    | .disjoint => declaration.FootprintsDisjoint
    | .canonical => True

/-- Every changed primary target is represented by exactly one incidence (the
uniqueness half is `TargetsUnique`). -/
def Declaration.TargetsCoverFootprint
    (declaration : Declaration portal materializer Incidence) : Prop :=
  forall key, key ∈ declaration.footprint ->
    exists incidence,
      (declaration.legs incidence).targetKey = stateKeyTarget key

structure Declaration.ShapeValid
    (declaration : Declaration portal materializer Incidence) : Prop where
  targetsUnique : declaration.TargetsUnique
  compositionValid : declaration.CompositionValid
  targetsCoverFootprint : declaration.TargetsCoverFootprint

/-- Computable universal quantification over a finite set.  The commutative
Boolean fold avoids choosing an order for `Finset`. -/
def finsetAll {alpha : Type} [DecidableEq alpha]
    (set : Finset alpha) (predicate : alpha -> Bool) : Bool :=
  set.fold Bool.and true predicate

@[simp] theorem finsetAll_eq_true_iff {alpha : Type} [DecidableEq alpha]
    (set : Finset alpha) (predicate : alpha -> Bool) :
    finsetAll set predicate = true <->
      forall element, element ∈ set -> predicate element = true := by
  induction set using Finset.induction_on with
  | empty => simp [finsetAll]
  | @insert element set outside induction =>
      rw [finsetAll, Finset.fold_insert outside]
      change (predicate element && finsetAll set predicate) = true <->
        forall candidate, candidate ∈ insert element set ->
          predicate candidate = true
      simp [outside, induction]

/-- Computable existential quantification over a finite set. -/
def finsetAny {alpha : Type} [DecidableEq alpha]
    (set : Finset alpha) (predicate : alpha -> Bool) : Bool :=
  set.fold Bool.or false predicate

@[simp] theorem finsetAny_eq_true_iff {alpha : Type} [DecidableEq alpha]
    (set : Finset alpha) (predicate : alpha -> Bool) :
    finsetAny set predicate = true <->
      exists element, element ∈ set ∧ predicate element = true := by
  induction set using Finset.induction_on with
  | empty => simp [finsetAny]
  | @insert element set outside induction =>
      rw [finsetAny, Finset.fold_insert outside]
      change (predicate element || finsetAny set predicate) = true <->
        exists candidate, candidate ∈ insert element set ∧
          predicate candidate = true
      simp [outside, induction]

def Declaration.targetsUniqueCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  finsetAll Finset.univ fun left => finsetAll Finset.univ fun right =>
    decide ((declaration.legs left).targetKey =
      (declaration.legs right).targetKey -> left = right)

@[simp] theorem Declaration.targetsUniqueCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.targetsUniqueCheck = true <-> declaration.TargetsUnique := by
  simp only [Declaration.targetsUniqueCheck, finsetAll_eq_true_iff,
    Finset.mem_univ, true_implies, decide_eq_true_eq]
  rfl

def Declaration.orderCompleteCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  decide declaration.composition.order.Nodup &&
    finsetAll Finset.univ fun incidence =>
      decide (incidence ∈ declaration.composition.order)

@[simp] theorem Declaration.orderCompleteCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.orderCompleteCheck = true <-> declaration.OrderComplete := by
  simp [Declaration.orderCompleteCheck, Declaration.OrderComplete]

def Declaration.footprintsDisjointCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  finsetAll Finset.univ fun left => finsetAll Finset.univ fun right =>
    decide (left ≠ right ->
      Disjoint ((declaration.legs left).effects.footprint.toFinset)
        ((declaration.legs right).effects.footprint.toFinset))

@[simp] theorem Declaration.footprintsDisjointCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.footprintsDisjointCheck = true <->
      declaration.FootprintsDisjoint := by
  simp only [Declaration.footprintsDisjointCheck, finsetAll_eq_true_iff,
    Finset.mem_univ, true_implies, decide_eq_true_eq]
  rfl

def Declaration.compositionCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  declaration.orderCompleteCheck &&
    match declaration.composition.mode with
    | .disjoint => declaration.footprintsDisjointCheck
    | .canonical => true

@[simp] theorem Declaration.compositionCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.compositionCheck = true <->
      declaration.CompositionValid := by
  cases modeEq : declaration.composition.mode <;>
    simp [Declaration.compositionCheck, Declaration.CompositionValid, modeEq]

def Declaration.targetsCoverCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  declaration.footprint.all fun key =>
    finsetAny Finset.univ fun incidence =>
      decide ((declaration.legs incidence).targetKey = stateKeyTarget key)

@[simp] theorem Declaration.targetsCoverCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.targetsCoverCheck = true <->
      declaration.TargetsCoverFootprint := by
  simp [Declaration.targetsCoverCheck, Declaration.TargetsCoverFootprint]

def Declaration.shapeCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  declaration.targetsUniqueCheck && declaration.compositionCheck &&
    declaration.targetsCoverCheck

@[simp] theorem Declaration.shapeCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.shapeCheck = true <-> declaration.ShapeValid := by
  constructor
  · intro accepted
    have parts : (declaration.TargetsUnique ∧
        declaration.CompositionValid) ∧
        declaration.TargetsCoverFootprint := by
      simpa [Declaration.shapeCheck] using accepted
    exact ⟨parts.1.1, parts.1.2, parts.2⟩
  · intro valid
    simpa [Declaration.shapeCheck] using
      (show (declaration.TargetsUnique ∧
          declaration.CompositionValid) ∧
          declaration.TargetsCoverFootprint from
        ⟨⟨valid.targetsUnique, valid.compositionValid⟩,
          valid.targetsCoverFootprint⟩)

def Declaration.AuthorizationAccepted
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) : Prop :=
  forall incidence,
    verify (state := declaration.authState projection)
      (declaration.legs incidence).presentation = .accepted

def Declaration.authorizationCheck
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) : Bool :=
  finsetAll Finset.univ fun incidence =>
    decide (verify (state := declaration.authState projection)
      (declaration.legs incidence).presentation = .accepted)

@[simp] theorem Declaration.authorizationCheck_eq_true_iff
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    declaration.authorizationCheck projection = true <->
      declaration.AuthorizationAccepted projection := by
  simp [Declaration.authorizationCheck,
    Declaration.AuthorizationAccepted]

def Declaration.ExactAggregateBalance
    (declaration : Declaration portal materializer Incidence) : Prop :=
  forall resource, resource ∈ declaration.resources ->
    declaration.aggregateDelta resource = 0

def Declaration.balanceCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  declaration.resources.all fun resource =>
    decide (declaration.aggregateDelta resource = 0)

@[simp] theorem Declaration.balanceCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.balanceCheck = true <-> declaration.ExactAggregateBalance := by
  simp [Declaration.balanceCheck, Declaration.ExactAggregateBalance]

def Declaration.GuardsHold
    (declaration : Declaration portal materializer Incidence) : Prop :=
  forall incidence,
    (declaration.legs incidence).effects.guardsCheck declaration.preStore = true

def Declaration.guardsCheck
    (declaration : Declaration portal materializer Incidence) : Bool :=
  finsetAll Finset.univ fun incidence =>
    (declaration.legs incidence).effects.guardsCheck declaration.preStore

@[simp] theorem Declaration.guardsCheck_eq_true_iff
    (declaration : Declaration portal materializer Incidence) :
    declaration.guardsCheck = true <-> declaration.GuardsHold := by
  simp [Declaration.guardsCheck, Declaration.GuardsHold]

theorem accountDeltaSum_zero_of_resource_not_mem
    (deltas : List BalanceDelta) (account : ResourceId .account)
    (resource : Digest)
    (outside : resource ∉ deltas.map BalanceDelta.resource) :
    accountDeltaSum deltas account resource = 0 := by
  induction deltas with
  | nil => rfl
  | cons delta rest induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at outside
      have different : delta.resource ≠ resource := fun equal =>
        outside.1 equal.symm
      rw [accountDeltaSum]
      simp only [List.map_cons, List.sum_cons]
      have conditionFalse :
          ¬ ((decide (delta.account = account) &&
            decide (delta.resource = resource)) = true) := by
        simp [different]
      rw [if_neg conditionFalse, zero_add]
      simpa [accountDeltaSum] using induction outside.2

/-- The finite resource check implies equality of the entire `Digest -> Int`
aggregate vector; coordinates absent from the derived delta list are zero by
construction. -/
theorem Declaration.aggregateDelta_zero
    (declaration : Declaration portal materializer Incidence)
    (balanced : declaration.ExactAggregateBalance) :
    declaration.aggregateDelta = 0 := by
  funext resource
  by_cases present : resource ∈ declaration.resources
  · exact balanced resource present
  · have absent : resource ∉
        declaration.jointDeltas.map BalanceDelta.resource := by
      simpa [Declaration.resources] using present
    simp only [Declaration.aggregateDelta]
    apply Finset.sum_eq_zero
    intro incidence _
    cases targetEq : (declaration.legs incidence).accountTarget? with
    | none => simp [Declaration.halfDelta, targetEq]
    | some account =>
        simpa [Declaration.halfDelta, targetEq] using
          accountDeltaSum_zero_of_resource_not_mem
            declaration.jointDeltas account resource absent

/-! ## Total data execution -/

inductive RejectReason
  | shape
  | authorization
  | aggregateBalance
  | guard
  | apex
  deriving DecidableEq, Repr

inductive Outcome
    (declaration : Declaration portal materializer Incidence)
  | committed (postStore : Store)
  | rejected (reason : RejectReason)

/-- One data-only joint execution.  Every shape, authorization, balance, and
guard check precedes patch evaluation.  The candidate is admitted only when its
canonical root equals the shared apex. -/
def execute
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence) :
    Outcome declaration :=
  if declaration.shapeCheck then
    if declaration.authorizationCheck projection then
      if declaration.balanceCheck then
        if declaration.guardsCheck then
          let postStore := applyPatch declaration.patch declaration.preStore
          let post := materialize materializer (DeclaredTurn.logicalOfStore postStore)
          if post.root = declaration.apex then .committed postStore
          else .rejected .apex
        else .rejected .guard
      else .rejected .aggregateBalance
    else .rejected .authorization
  else .rejected .shape

def Outcome.materialized
    {declaration : Declaration portal materializer Incidence} :
    Outcome declaration -> Materialized materializer
  | .committed postStore =>
      materialize materializer (DeclaredTurn.logicalOfStore postStore)
  | .rejected _ => declaration.pre

@[simp] theorem Outcome.rejected_materialized
    {declaration : Declaration portal materializer Incidence}
    (reason : RejectReason) :
    (Outcome.rejected (declaration := declaration) reason).materialized =
      declaration.pre := rfl

theorem execute_rejected_unchanged
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (reason : RejectReason)
    (rejected : execute projection declaration = .rejected reason) :
    (execute projection declaration).materialized = declaration.pre := by
  rw [rejected]
  rfl

/-! ## Proof-relevant committed hyperedge -/

/-- The existing effect interpreter, viewed as the shared transition of the
abstract hyperedge. -/
def jointStep (state : Store)
    (declaration : Declaration portal materializer Incidence) : Store :=
  applyPatch declaration.patch state

/-- The shared apex reader is the sole canonical materialization root. -/
def jointTurnId
    (materializer : Materializer DeclaredTurn.effectSchema Digest)
    (_incidence : Incidence) (state : Store) : Digest :=
  (materialize materializer (DeclaredTurn.logicalOfStore state)).root

/-- The hyperedge half-edge is the declaration-derived full-width vector. -/
def jointHalfEdge (incidence : Incidence) (_state : Store)
    (declaration : Declaration portal materializer Incidence) : Digest -> Int :=
  declaration.halfDelta incidence

abbrev SemanticHyperedge
    (declaration : Declaration portal materializer Incidence) :=
  Hyperedge Incidence Store (Declaration portal materializer Incidence)
    Digest (Digest -> Int) jointStep (jointTurnId materializer) jointHalfEdge

/-- Semantic certification of one exact committed post.  Every proof field is a
reflection of a check made by `execute`; authorizations are the existing
request-indexed tokens, and the post is the existing patch interpreter's exact
result. -/
structure CommittedHyperedge
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (postStore : Store) : Type where
  shape : declaration.ShapeValid
  authorizations : forall incidence,
    Nonempty (Authorized portal (declaration.authState projection)
      (declaration.legs incidence).request)
  aggregateBalanced : declaration.ExactAggregateBalance
  guards : declaration.GuardsHold
  evaluated : applyPatch declaration.patch declaration.preStore = postStore
  apexExact :
    (materialize materializer (DeclaredTurn.logicalOfStore postStore)).root =
      declaration.apex

def CommittedHyperedge.post
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (_commit : CommittedHyperedge projection declaration postStore) :
    Materialized materializer :=
  materialize materializer (DeclaredTurn.logicalOfStore postStore)

def CommittedHyperedge.receipt
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    ReactiveReceipt.ReceiptDelta declaration.preStore postStore where
  touched := declaration.footprint.toFinset
  frame := by
    intro key outside
    rw [← commit.evaluated]
    apply applyPatch_frame
    simpa [Declaration.footprint] using outside

/-- Projection into the shared canonical transition nucleus. -/
def CommittedHyperedge.prepared
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    CanonicalTransition.PreparedTurn materializer declaration.pre Empty where
  post := commit.post
  delta :=
    { fieldFootprint := commit.receipt.touched
      resourceFootprint := ∅
      fieldFrame := commit.receipt.frame
      resourceFrame := by intro resource; exact nomatch resource }
  nullifier := none

@[simp] theorem CommittedHyperedge.prepared_preRoot
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    commit.prepared.preRoot = declaration.pre.root := rfl

@[simp] theorem CommittedHyperedge.prepared_postRoot
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    commit.prepared.postRoot = commit.post.root := rfl

/-- The actual wide-pullback carrier.  Every incidence starts from the one
canonical pre-store, fires the one joint patch, reaches the one apex/root, and
contributes its exact full-width half-delta. -/
def CommittedHyperedge.toHyperedge
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    SemanticHyperedge declaration where
  x := fun _ => declaration.preStore
  t := declaration
  tid := declaration.apex
  agree := by
    intro incidence
    change
      (materialize materializer
        (DeclaredTurn.logicalOfStore
          (applyPatch declaration.patch declaration.preStore))).root =
        declaration.apex
    rw [commit.evaluated]
    exact commit.apexExact
  balanced := by
    funext resource
    have balanced := congrFun
      (declaration.aggregateDelta_zero commit.aggregateBalanced) resource
    simpa [Declaration.aggregateDelta, jointHalfEdge] using balanced

@[simp] theorem CommittedHyperedge.edge_turn_exact
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    commit.toHyperedge.t = declaration := rfl

@[simp] theorem CommittedHyperedge.edge_apex_exact
    {projection : AuthorizationProjection materializer}
    {declaration : Declaration portal materializer Incidence}
    {postStore : Store}
    (commit : CommittedHyperedge projection declaration postStore) :
    commit.toHyperedge.tid = declaration.apex := rfl

/-- The central data-to-semantics seam.  It uses the one existing authorization
admission theorem independently at each exact request index; there is no second
authorization proof interpreter. -/
theorem execute_committed_hyperedge_sound
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (postStore : Store)
    (committed : execute projection declaration = .committed postStore) :
    Nonempty (CommittedHyperedge projection declaration postStore) := by
  unfold execute at committed
  split at committed
  next shapeAccepted =>
    split at committed
    next authorizationAccepted =>
      split at committed
      next balanceAccepted =>
        split at committed
        next guardsAccepted =>
          dsimp only at committed
          split at committed
          next apexAccepted =>
            have evaluated :
                applyPatch declaration.patch declaration.preStore = postStore := by
              simpa using committed
            have allAuthorized :=
              (declaration.authorizationCheck_eq_true_iff projection).mp
                authorizationAccepted
            refine ⟨
              { shape := (declaration.shapeCheck_eq_true_iff).mp shapeAccepted
                authorizations := ?_
                aggregateBalanced :=
                  (declaration.balanceCheck_eq_true_iff).mp balanceAccepted
                guards := (declaration.guardsCheck_eq_true_iff).mp guardsAccepted
                evaluated := evaluated
                apexExact := ?_ }⟩
            · intro incidence
              exact verify_accepted_authorized
                (declaration.legs incidence).presentation (allAuthorized incidence)
            · simpa [evaluated] using apexAccepted
          next _ => simp at committed
        next _ => simp at committed
      next _ => simp at committed
    next _ => simp at committed
  next _ => simp at committed

/-! ## Load-bearing negative -/

/-- Even if shape and every exact request authorize, a nonzero full-width
aggregate is rejected before patch evaluation.  The extra `agreement` premise
exhibits the sharp case: the would-be post already has the declared apex, but
apex agreement cannot manufacture conservation. -/
theorem execute_rejects_agreeing_nonzero_balance
    (projection : AuthorizationProjection materializer)
    (declaration : Declaration portal materializer Incidence)
    (shapeAccepted : declaration.shapeCheck = true)
    (authorizationAccepted : declaration.authorizationCheck projection = true)
    (resource : Digest) (present : resource ∈ declaration.resources)
    (nonzero : declaration.aggregateDelta resource ≠ 0)
    (_agreement :
      (materialize materializer
        (DeclaredTurn.logicalOfStore
          (applyPatch declaration.patch declaration.preStore))).root =
        declaration.apex) :
    execute projection declaration = .rejected .aggregateBalance := by
  have balanceRejected : declaration.balanceCheck = false := by
    cases checked : declaration.balanceCheck with
    | false => rfl
    | true =>
        exfalso
        exact nonzero
          ((declaration.balanceCheck_eq_true_iff.mp checked) resource present)
  simp [execute, shapeAccepted, authorizationAccepted, balanceRejected]

end Minidregg.Kernel.DeclaredHyperedge
