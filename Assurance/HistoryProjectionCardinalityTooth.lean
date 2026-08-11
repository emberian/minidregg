/-
# Assurance.HistoryProjectionCardinalityTooth -- the unbounded target is finite

The legacy `HistoryProjection` asks a fixed `Fin n -> F` word to determine the
root of every materialized cell.  Over a finite accumulator field, that forces
the whole root image to be finite.  In particular it cannot represent any
root-separated infinite stream, including a length-root materializer on a
stream whose canonical encoded lengths are injective/unbounded.

This is a cardinality theorem only.  It neither asserts nor assumes
cryptographic binding.  The finite declared-footprint replacement lives in
`Assurance.ScopedAcceptedCellEffectHistory`.
-/
import Assurance.AcceptedCellEffectHistory
import Assurance.ScopedAcceptedCellEffectHistory

namespace Minidregg.Assurance.HistoryProjectionCardinalityTooth

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z

variable
    {S : CellState.Schema.{u, v, w, x}} [DecidableEq S.Field]
    [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F] [Finite F]

/-- A fixed finite-word `HistoryProjection` cannot cover a stream of canonical
cells with pairwise-distinct roots.  This is the exact hidden cardinality
obligation in the old interface. -/
theorem no_historyProjection_of_rootSeparatedStream
    (cells : Nat -> CellState.Materialized M)
    (rootsInjective : Function.Injective (fun index => (cells index).root)) :
    ¬ Nonempty (HistoryProjection family n F) := by
  rintro ⟨projection⟩
  apply not_injective_infinite_finite
    (fun index => projection.project (cells index))
  intro left right wordsEqual
  apply rootsInjective
  change (cells left).root = (cells right).root
  rw [← projection.root_exact (cells left),
    ← projection.root_exact (cells right)]
  simpa using congrArg projection.stateCommitment.root wordsEqual

/-! ## Axiom pin -/

/-- info: 'Minidregg.Assurance.HistoryProjectionCardinalityTooth.no_historyProjection_of_rootSeparatedStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_historyProjection_of_rootSeparatedStream

end Minidregg.Assurance.HistoryProjectionCardinalityTooth
