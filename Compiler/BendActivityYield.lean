/- A persistent source yield is a real affine heap pair: the typed Plan data
and the captured source continuation. Extraction retains exact heap/source
proofs and uses the existing complete native Plan decoder. It does not grant
value/typing, reachability, dispatch or native installation authority. -/
import Compiler.BendPlanLowering
import Theory.BendClosureDecode
import Theory.BendClosureMachine

namespace Minidregg.Compiler.BendActivityYield
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

structure Extracted (program : Program) (state : State) where
  resultPointer : Nat
  planPointer : Nat
  continuationPointer : Nat
  completed : state.control = .complete resultPointer
  pairRow : state.heap.get? resultPointer = some (.pair .Q1 planPointer continuationPointer)
  planSource : Term
  continuationSource : Term
  planExact : Denotes program state.heap planPointer planSource
  continuationExact : Denotes program state.heap continuationPointer continuationSource
  plan : BendWorldPlan.Plan
  decoded : BendPlanLowering.lower planSource = some plan

/-- This is the explicit public/reference extraction path. Private execution
requires a qualified oblivious decoder and disclosure policy; using this
proof-producing reference function does not establish trace privacy. -/
def extract (program : Program) (ticks : Nat) (state : State) :
    Option (Extracted program state) := do
  match completed : state.control with
  | .complete result =>
    match pairRow : state.heap.get? result with
    | some (.pair .Q1 planPointer continuationPointer) =>
      let planSource ← BendClosureArena.decode program state.heap ticks planPointer
      let continuationSource ← BendClosureArena.decode program state.heap ticks continuationPointer
      match decoded : BendPlanLowering.lower planSource.term with
      | none => none
      | some plan => some ⟨result, planPointer, continuationPointer, completed, pairRow,
          planSource.term, continuationSource.term, planSource.exact, continuationSource.exact,
          plan, decoded⟩
    | _ => none
  | _ => none

theorem extracted_pair_exact {program : Program} {state : State}
    (yielded : Extracted program state) :
    Denotes program state.heap yielded.resultPointer
      (.Tup .Q1 yielded.planSource yielded.continuationSource) :=
  .pair yielded.pairRow yielded.planExact yielded.continuationExact

/-- The actual generated native command must agree with every ordered effect
of the decoded Plan. Current authorization, read guards and charge admission
are still checked by the receiving adapter on the same complete command. -/
structure BoundCommand (program : Program) (state : State) (command : Command) where
  yielded : Extracted program state
  exactEffects : BendWorldPlan.matchesCommand yielded.plan command = true

theorem native_payloads_exact {program : Program} {state : State} {command : Command}
    (bound : BoundCommand program state command) :
    bound.yielded.plan.effects = BendWorldPlan.effectsOf command :=
  BendWorldPlan.ordered_payloads_exact bound.exactEffects

#assert_axioms extract
#assert_axioms extracted_pair_exact
#assert_axioms native_payloads_exact
end Minidregg.Compiler.BendActivityYield
