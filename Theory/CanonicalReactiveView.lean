/-
# Theory.CanonicalReactiveView -- receipt-driven views of canonical typed cells

The original reactive receipt lens is intentionally candidate-neutral, but its
state carrier is a uniform `Key -> Value` function.  The canonical cell kernel
has a stronger dependent state: one `Store L`, whose addresses carry
namespace-indexed value types.  This module puts reactive UI semantics directly
on that carrier.  It never materializes a parallel uniform post-store.

An `ObserverLens` is indexed by the observer and declares its typed address
dependencies.  A canonical `CellDelta` invalidates the view iff that dependency
set intersects the exact verified footprint.  Clean views are provably
unchanged and caches reuse their old rendering; dirty views are reprojected
from the sole canonical post-cell.  The `Example` section at the end exhibits
both poles on a built prepared turn: an observed address that the turn writes
dirties and changes the view, and a lens that under-declares its dependencies
cannot exist.

`PreparedReaction` is the guarded-hole bridge.  Its private constructor is
exposed only through `ofAccepted`: the eager hole, typed replay nullifier,
canonical pre-root, and unified footprint are all retained from an accepted
`ReactiveCellTransition`.  It is a logical preparation, not evidence that a
physical CAS, nullifier insertion, history append, or I/O has happened.
-/
import Theory.ReactiveCellTransition
import Theory.CanonicalTransitionWitness

namespace Minidregg.Theory.CanonicalReactiveView

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.Store

set_option autoImplicit false

universe u v w y z o q

/-! ## Observer-indexed lenses on the dependent canonical state -/

/-- A pure observer-indexed projection of the canonical typed state.

The address dependency set is part of the lens semantics.  The locality
premise compares the complete typed `Option` value at each observed address, so
presence and absence are observed exactly. -/
structure ObserverLens
    (L : Layout.{u, v, w})
    (Observer : Type o) (View : Observer -> Type q) where
  dependencies : Observer -> Finset (Address L)
  project : (observer : Observer) -> Store L -> View observer
  locality : forall observer left right,
    (forall address, address ∈ dependencies observer ->
      left address = right address) ->
    project observer left = project observer right

/-- A canonical delta dirties a view exactly when it touches an observed typed
address. -/
def ObserverLens.Dirty
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) : Prop :=
  (lens.dependencies observer ∩ delta.footprint).Nonempty

/-- Proof-relevant explanation of why an observer's view was invalidated. -/
inductive InvalidationCause
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) : Type _
  | address (address : Address L)
      (observed : address ∈ lens.dependencies observer)
      (touched : address ∈ delta.footprint)

/-- Boolean-style dirtiness and proof-relevant invalidation causes have exactly
the same meaning; event interpreters may therefore retain the precise cause. -/
theorem ObserverLens.dirty_iff_cause
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post) :
    lens.Dirty observer delta ↔
      Nonempty (InvalidationCause lens observer delta) := by
  constructor
  · rintro ⟨address, hmem⟩
    exact ⟨.address address (Finset.mem_inter.mp hmem).1
      (Finset.mem_inter.mp hmem).2⟩
  · rintro ⟨cause⟩
    cases cause with
    | address address observed touched =>
        exact ⟨address, Finset.mem_inter.mpr ⟨observed, touched⟩⟩

/-- The load-bearing typed invalidation theorem: a clean canonical receipt
cannot change this observer's projection. -/
theorem ObserverLens.project_eq_of_clean
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M} (delta : CellDelta pre post)
    (clean : ¬ lens.Dirty observer delta) :
    lens.project observer post.logical = lens.project observer pre.logical := by
  apply lens.locality observer
  intro address observed
  exact delta.frame address (by
    intro touched
    exact clean ⟨address, Finset.mem_inter.mpr ⟨observed, touched⟩⟩)

/-- If an observer's rendered value changes, the exact canonical delta must
contain an invalidation cause for that observer. -/
theorem ObserverLens.dirty_of_project_ne
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
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
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    {Root : Type y} {M : CellState.Materializer L Root}
    (state : CellState.Materialized M) where
  rendered : View observer
  correct : rendered = lens.project observer state.logical

/-- Advance one observer cache across a verified canonical delta.  No uniform
`Key -> Value` post-state is constructed: the dirty branch reads `post.logical`
and the clean branch reuses the already-correct value. -/
def Cache.advance
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post) :
    Cache lens observer post := by
  letI : Decidable (lens.Dirty observer delta) :=
    inferInstanceAs (Decidable (lens.dependencies observer ∩ delta.footprint).Nonempty)
  exact if dirty : lens.Dirty observer delta then
    ⟨lens.project observer post.logical, rfl⟩
  else
    ⟨cache.rendered,
      cache.correct.trans
        (lens.project_eq_of_clean observer delta dirty).symm⟩

@[simp] theorem Cache.advance_clean_reuses
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post)
    (clean : ¬ lens.Dirty observer delta) :
    (cache.advance delta).rendered = cache.rendered := by
  simp [Cache.advance, clean]

@[simp] theorem Cache.advance_dirty_reprojects
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre post : CellState.Materialized M}
    (cache : Cache lens observer pre) (delta : CellDelta pre post)
    (dirty : lens.Dirty observer delta) :
    (cache.advance delta).rendered = lens.project observer post.logical := by
  simp [Cache.advance, dirty]

/-- A prepared logical turn advances a cache through its sole canonical post. -/
def PreparedTurn.advanceCache
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre : CellState.Materialized M} {Nullifier : Type z}
    (turn : PreparedTurn M pre Nullifier) (cache : Cache lens observer pre) :
    Cache lens observer turn.post :=
  cache.advance turn.delta

/-- Blocked and rejected decisions reuse the old projection definitionally;
only a prepared logical transition can invoke invalidation. -/
def Decision.advanceCache
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
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
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
    {pre : CellState.Materialized M}
    {Blocked Reject Nullifier : Type z}
    (reason : Blocked) (cache : Cache lens observer pre) :
    (Decision.advanceCache
      (Decision.blocked (M := M) (Reject := Reject) (Nullifier := Nullifier)
        (pre := pre) reason) cache).rendered = cache.rendered :=
  rfl

@[simp] theorem Decision.advanceCache_rejected_reuses
    {L : Layout.{u, v, w}}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
    {Root : Type y} {M : CellState.Materializer L Root}
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
    {L : Layout.{u, v, w}}
    (M : CellState.Materializer L T.Root)
    (layout : CellState.ControllerLayout L T)
    (pre : CellState.Materialized M) : Type _ where
  private mk ::
  declaration : ReactiveController.Declaration U T
  prepared : PreparedTurn M pre (GuardedAdvice.NullifierKey T.vocabulary)
  eagerPreRoot : declaration.hole.preRoot = prepared.preRoot
  eagerNullifier : prepared.nullifier = some declaration.hole.nullifierKey
  eagerFootprint :
    prepared.delta.footprint.image layout.addressKey = declaration.hole.footprint

/-- The sole public construction path from guarded execution to a canonical
prepared reaction. -/
def PreparedReaction.ofAccepted
    {U : FirstOrderUniverse} {T : ReactiveController.Types.{z}}
    [LinearOrder T.Height]
    [DecidableEq (ReactiveController.HoleSpec U T)] [DecidableEq T.TurnId]
    [DecidableEq T.AuthorityDemand] [DecidableEq T.Commitment]
    [DecidableEq T.Root] [DecidableEq T.Key] [DecidableEq T.Value]
    [DecidableEq (GuardedAdvice.NullifierKey T.vocabulary)]
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {declaration : ReactiveController.Declaration U T}
    {observation : ReactiveController.HostObservation T}
    {advice : ReactiveController.Advice declaration.hole}
    {proof : ReactiveController.ProofData T}
    {controllerPre : ReactiveReceipt.Store T.Key T.Value}
    {pre : CellState.Materialized M} {patch : Patch L}
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
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {pre : CellState.Materialized M}
    {Observer : Type o} {View : Observer -> Type q}
    {lens : ObserverLens L Observer View} {observer : Observer}
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
    {L : Layout.{u, v, w}}
    {M : CellState.Materializer L T.Root}
    {layout : CellState.ControllerLayout L T}
    {pre : CellState.Materialized M}
    {Observer : Type o} {View : Observer -> Type q}
    (lens : ObserverLens L Observer View) (observer : Observer)
    (reaction : PreparedReaction (U := U) M layout pre)
    (changed : lens.project observer reaction.prepared.post.logical ≠
      lens.project observer pre.logical) :
    Nonempty (InvalidationCause lens observer reaction.prepared.delta) := by
  apply (lens.dirty_iff_cause observer reaction.prepared.delta).mp
  exact lens.dirty_of_project_ne observer reaction.prepared.delta changed

/-! ## Example: both poles on a built prepared turn

`CanonicalTransitionWitness.preparedTurn` is a real `PreparedTurn` over
`CellStateWitness.layout` whose one written address (`sole`) changes from
`false` to `true`. -/

namespace Example

open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.CanonicalTransitionWitness

/-- The observer that renders the sole address, declaring exactly it. -/
def soleLens : ObserverLens CellStateWitness.layout Unit (fun _ => Option Bool) where
  dependencies := fun _ => {sole}
  project := fun _ store => store sole
  locality := fun _ _ _ same => same sole (Finset.mem_singleton_self _)

/-- An observer with no dependencies and a constant rendering. -/
def blindLens : ObserverLens CellStateWitness.layout Unit (fun _ => Unit) where
  dependencies := fun _ => ∅
  project := fun _ _ => ()
  locality := fun _ _ _ _ => rfl

/-- Satisfiable pole: the observed written address dirties the view. -/
theorem soleLens_dirty : soleLens.Dirty () preparedTurn.delta :=
  ⟨sole, Finset.mem_inter.mpr
    ⟨Finset.mem_singleton_self _, preparedTurn_footprint_changes.1⟩⟩

/-- The dirty view really changes, so invalidation is not over-approximating
a no-op here. -/
theorem soleLens_changes :
    soleLens.project () preparedTurn.post.logical ≠
      soleLens.project () cell.logical :=
  preparedTurn_footprint_changes.2

/-- The cache reprojects from the canonical post on the dirty turn. -/
theorem soleLens_cache_reprojects :
    (Cache.advance (lens := soleLens) (observer := ())
        ⟨cell.logical sole, rfl⟩ preparedTurn.delta).rendered =
      preparedTurn.post.logical sole :=
  Cache.advance_dirty_reprojects _ _ soleLens_dirty

/-- Dirtiness is not constant: an observer of nothing is clean. -/
theorem blindLens_clean : ¬ blindLens.Dirty () preparedTurn.delta := by
  rintro ⟨address, hmem⟩
  simp [blindLens] at hmem

/-- Refuting pole: the locality premise is load-bearing.  No lens can declare
no dependencies and still render the address the turn writes. -/
theorem underDeclared_lens_impossible
    (lens : ObserverLens CellStateWitness.layout Unit (fun _ => Option Bool))
    (undeclared : lens.dependencies () = ∅) :
    lens.project () ≠ fun store => store sole := by
  intro reads
  have clean : ¬ lens.Dirty () preparedTurn.delta := by
    rintro ⟨address, hmem⟩
    rw [undeclared] at hmem
    simp at hmem
  have same := lens.project_eq_of_clean () preparedTurn.delta clean
  rw [reads] at same
  exact preparedTurn_footprint_changes.2 same

end Example

/-- info: 'Minidregg.Theory.CanonicalReactiveView.ObserverLens.project_eq_of_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ObserverLens.project_eq_of_clean
/-- info: 'Minidregg.Theory.CanonicalReactiveView.PreparedReaction.changed_has_cause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedReaction.changed_has_cause
/-- info: 'Minidregg.Theory.CanonicalReactiveView.Example.underDeclared_lens_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.underDeclared_lens_impossible
/-- info: 'Minidregg.Theory.CanonicalReactiveView.Example.soleLens_cache_reprojects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.soleLens_cache_reprojects

end Minidregg.Theory.CanonicalReactiveView
