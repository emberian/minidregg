/-
# Theory.CanonicalReactiveView -- receipt-driven views of canonical typed cells

The original reactive receipt lens is intentionally candidate-neutral, but its
state carrier is a uniform `Key -> Value` function.  The canonical cell kernel
has a stronger dependent state: fields have field-indexed types and resource
cells retain value-indexed authority and evidence.  This module puts reactive
UI semantics directly on that carrier.  It never materializes a parallel
uniform post-store.

An `ObserverLens` is indexed by the observer and declares separate typed field
and resource dependencies.  A canonical `CellDelta` invalidates the view iff
one of those dependency sets intersects the exact verified footprint.  Clean
views are provably unchanged and caches reuse their old rendering; dirty views
are reprojected from the sole canonical post-cell.

`PreparedReaction` is the guarded-hole bridge.  Its private constructor is
exposed only through `ofAccepted`: the eager hole, typed replay nullifier,
canonical pre-root, and unified footprint are all retained from an accepted
`ReactiveCellTransition`.  It is a logical preparation, not evidence that a
physical CAS, nullifier insertion, history append, or I/O has happened.
-/
import Theory.CanonicalTransition

namespace Minidregg.Theory.CanonicalReactiveView

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CanonicalTransition

universe u v w x y z o q

/-! ## Observer-indexed lenses on the dependent canonical state -/

/-- A pure observer-indexed projection of the canonical typed state.

The field and resource dependency sets are part of the lens semantics.  The
resource locality premise compares the complete dependent `ResourceCell`, so
an authority/evidence change cannot be hidden behind equality of an untyped
payload. -/
structure ObserverLens
    (S : CellState.Schema.{u, v, w, x})
    (Observer : Type o) (View : Observer -> Type q)
    [DecidableEq S.Field] [DecidableEq S.Resource] where
  fieldDependencies : Observer -> Finset S.Field
  resourceDependencies : Observer -> Finset S.Resource
  project : (observer : Observer) -> CellState.LogicalState S -> View observer
  locality : forall observer left right,
    (forall field, field ∈ fieldDependencies observer ->
      left.fields field = right.fields field) ->
    (forall resource, resource ∈ resourceDependencies observer ->
      left.resources resource = right.resources resource) ->
    project observer left = project observer right

/-- A canonical delta dirties a view exactly when it touches an observed typed
field or a complete observed resource package. -/
def ObserverLens.Dirty
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) : Prop :=
  (lens.fieldDependencies observer ∩ delta.fieldFootprint).Nonempty ∨
    (lens.resourceDependencies observer ∩ delta.resourceFootprint).Nonempty

/-- Proof-relevant explanation of why an observer's view was invalidated. -/
inductive InvalidationCause
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) : Type _
  | field (key : S.Field)
      (observed : key ∈ lens.fieldDependencies observer)
      (touched : key ∈ delta.fieldFootprint)
  | resource (key : S.Resource)
      (observed : key ∈ lens.resourceDependencies observer)
      (touched : key ∈ delta.resourceFootprint)

/-- Boolean-style dirtiness and proof-relevant invalidation causes have exactly
the same meaning; event interpreters may therefore retain the precise cause. -/
theorem ObserverLens.dirty_iff_cause
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) :
    lens.Dirty observer delta ↔
      Nonempty (InvalidationCause lens observer delta) := by
  constructor
  · intro dirty
    rcases dirty with fieldDirty | resourceDirty
    · rcases fieldDirty with ⟨key, hkey⟩
      exact ⟨.field key (Finset.mem_inter.mp hkey).1
        (Finset.mem_inter.mp hkey).2⟩
    · rcases resourceDirty with ⟨key, hkey⟩
      exact ⟨.resource key (Finset.mem_inter.mp hkey).1
        (Finset.mem_inter.mp hkey).2⟩
  · rintro ⟨cause⟩
    cases cause with
    | field key observed touched =>
        exact Or.inl ⟨key, Finset.mem_inter.mpr ⟨observed, touched⟩⟩
    | resource key observed touched =>
        exact Or.inr ⟨key, Finset.mem_inter.mpr ⟨observed, touched⟩⟩

/-- The load-bearing typed invalidation theorem: a clean canonical receipt
cannot change this observer's projection. -/
theorem ObserverLens.project_eq_of_clean
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (clean : ¬ lens.Dirty observer delta) :
    lens.project observer post.logical = lens.project observer pre.logical := by
  apply lens.locality observer
  · intro field observed
    exact delta.fieldFrame field (by
      intro touched
      exact clean (Or.inl
        ⟨field, Finset.mem_inter.mpr ⟨observed, touched⟩⟩))
  · intro resource observed
    exact delta.resourceFrame resource (by
      intro touched
      exact clean (Or.inr
        ⟨resource, Finset.mem_inter.mpr ⟨observed, touched⟩⟩))

/-- If an observer's rendered value changes, the exact canonical delta must
contain an invalidation cause for that observer. -/
theorem ObserverLens.dirty_of_project_ne
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (changed : lens.project observer post.logical ≠
      lens.project observer pre.logical) :
    lens.Dirty observer delta := by
  by_contra clean
  exact changed (lens.project_eq_of_clean observer delta clean)

/-! ## Correct-by-construction observer caches -/

/-- A rendered value proven to be the selected observer's projection of one
exact canonical cell. -/
structure Cache
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (lens : ObserverLens S Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer S Root}
    (state : CellState.Materialized M) where
  rendered : View observer
  correct : rendered = lens.project observer state.logical

/-- Advance one observer cache across a verified canonical delta.  No uniform
`Key -> Value` post-state is constructed: the dirty branch reads `post.logical`
and the clean branch reuses the already-correct value. -/
def Cache.advance
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post) :
    Cache lens observer post := by
  letI : Decidable (lens.Dirty observer delta) := by
    unfold ObserverLens.Dirty
    infer_instance
  exact if dirty : lens.Dirty observer delta then
    ⟨lens.project observer post.logical, rfl⟩
  else
    ⟨cache.rendered,
      cache.correct.trans
        (lens.project_eq_of_clean observer delta dirty).symm⟩

@[simp] theorem Cache.advance_clean_reuses
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post)
    (clean : ¬ lens.Dirty observer delta) :
    (cache.advance delta).rendered = cache.rendered := by
  simp [Cache.advance, clean]

@[simp] theorem Cache.advance_dirty_reprojects
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post)
    (dirty : lens.Dirty observer delta) :
    (cache.advance delta).rendered = lens.project observer post.logical := by
  simp [Cache.advance, dirty]

/-- A prepared logical turn advances a cache through its sole canonical post. -/
def PreparedTurn.advanceCache
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre : CellState.Materialized M} {Nullifier : Type z}
    (turn : PreparedTurn M pre Nullifier) (cache : Cache lens observer pre) :
    Cache lens observer turn.post :=
  cache.advance turn.delta

/-- Blocked and rejected decisions reuse the old projection definitionally;
only a prepared logical transition can invoke invalidation. -/
def Decision.advanceCache
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre : CellState.Materialized M}
    {Blocked Reject Nullifier : Type z}
    (decision : Decision M Blocked Reject Nullifier pre)
    (cache : Cache lens observer pre) :
    Cache lens observer decision.logicalPost :=
  match decision with
  | .blocked _ => cache
  | .rejected _ => cache
  | .prepared turn => PreparedTurn.advanceCache turn cache

@[simp] theorem Decision.advanceCache_blocked_reuses
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre : CellState.Materialized M}
    {Blocked Reject Nullifier : Type z}
    (reason : Blocked) (cache : Cache lens observer pre) :
    (Decision.advanceCache
      (Decision.blocked (M := M) (Reject := Reject) (Nullifier := Nullifier)
        (pre := pre) reason) cache).rendered = cache.rendered :=
  rfl

@[simp] theorem Decision.advanceCache_rejected_reuses
    {S : CellState.Schema.{u, v, w, x}}
    {Observer : Type o} {View : Observer -> Type q}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {lens : ObserverLens S Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer S Root}
    {pre : CellState.Materialized M}
    {Blocked Reject Nullifier : Type z}
    (reason : Reject) (cache : Cache lens observer pre) :
    (Decision.advanceCache
      (Decision.rejected (M := M) (Blocked := Blocked) (Nullifier := Nullifier)
        (pre := pre) reason) cache).rendered = cache.rendered :=
  rfl

/-! ## Accepted guarded holes as canonical prepared reactions -/

/-- The exact guarded preparation retained for reactive consumers.

The constructor is private.  The public constructor below consumes the joined
`ReactiveCellTransition.Accepted` proof, then drops the controller's legacy
uniform store and retains only the canonical typed transition plus its eager
hole bindings.  This object deliberately makes no physical-CAS claim. -/
structure PreparedReaction
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (M : CellState.Materializer S T.Root)
    (layout : CellState.ControllerLayout S T)
    (pre : CellState.Materialized M) : Type _ where
  private mk ::
  declaration : ReactiveController.Declaration U T
  prepared : PreparedTurn M pre (GuardedAdvice.NullifierKey T.vocabulary)
  eagerPreRoot : declaration.hole.preRoot = prepared.preRoot
  eagerNullifier : prepared.nullifier = some declaration.hole.nullifierKey
  eagerFootprint :
    prepared.delta.fieldFootprint.image layout.fieldKey ∪
        prepared.delta.resourceFootprint.image layout.resourceKey =
      declaration.hole.footprint

/-- The sole public construction path from guarded execution to a canonical
prepared reaction. -/
def PreparedReaction.ofAccepted
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : CellState.Patch S T.Root}
    (accepted : ReactiveCellTransition.Accepted M layout declaration observation
      advice proof controllerPre pre patch) :
    PreparedReaction (U := U) M layout pre where
  declaration := declaration
  prepared := PreparedTurn.ofReactiveAccepted accepted
  eagerPreRoot :=
    accepted.exact_bindings.eagerPreRoot.symm.trans
      (PreparedTurn.ofReactiveAccepted_preRoot accepted).symm
  eagerNullifier := PreparedTurn.ofReactiveAccepted_nullifier accepted
  eagerFootprint := PreparedTurn.ofReactiveAccepted_footprint accepted

/-- Observer caches consume only the canonical prepared transition retained by
the reaction; the old uniform controller post is absent from this API. -/
def PreparedReaction.advanceCache
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {pre : CellState.Materialized M}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens S Observer View} {observer : Observer}
    (reaction : PreparedReaction (U := U) M layout pre)
    (cache : Cache lens observer pre) :
    Cache lens observer reaction.prepared.post :=
  PreparedTurn.advanceCache reaction.prepared cache

/-- Every changed observer projection has a proof-relevant cause in the exact
accepted guarded footprint. -/
theorem PreparedReaction.changed_has_cause
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S T.Root}
    {layout : CellState.ControllerLayout S T}
    {pre : CellState.Materialized M}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens S Observer View) (observer : Observer)
    (reaction : PreparedReaction (U := U) M layout pre)
    (changed : lens.project observer reaction.prepared.post.logical ≠
      lens.project observer pre.logical) :
    Nonempty (InvalidationCause lens observer reaction.prepared.delta) := by
  apply (lens.dirty_iff_cause observer reaction.prepared.delta).mp
  exact lens.dirty_of_project_ne observer reaction.prepared.delta changed

#print axioms ObserverLens.project_eq_of_clean
#print axioms PreparedReaction.changed_has_cause

end Minidregg.Theory.CanonicalReactiveView
