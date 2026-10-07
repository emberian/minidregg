/- New Core4 execution/output evidence below current native authority admission.
This token checks actual closed typing, executes SAME source term with one root+
field budget, materializes complete data, and binds exact source Plan against
ACTUAL loaded directory and command. It creates no accepted receipt or authority. -/
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandCapacity
import Compiler.ObjectiveBendPlanAdapter
import Theory.AssertAxioms
namespace Minidregg.Kernel.ObjectiveBendPreparedOutput
open Minidregg.Theory
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Compiler
open Minidregg.Compiler.ObjectiveNativeScalarBinding
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

inductive Failure where
  | typing
  | execution (reason : ObjectiveBendDemandData.Failure) (retained : State)
  | nativeBinding
  deriving Repr

structure Prepared (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) (source : AnnotatedTerm) (limits : Limits) (budget : Budget)
    (capacity : ObjectiveBendDemandCapacity.Profile) where
  private mk ::
  checked : Checked source []
  execution : ExecutionWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term
  runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term = .ok execution
  proposal : NativePlan
  bound : BoundPlan deployment loaded command proposal
  lowerExact : ObjectiveBendPlanAdapter.lower deployment loaded command execution.extraction =
    some ⟨proposal,bound⟩

/-- Current source/input/codec/profile/funding/family gates consume this evidence
separately. Native binding refusal never becomes a source success fallback. -/
def prepare (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) (source : AnnotatedTerm) (typeFuel : Nat)
    (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) :
    Except Failure (Prepared deployment loaded command source limits budget capacity) := do
  let some checked := check source [] typeFuel | throw .typing
  match runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term with
  | .error failure => throw (.execution failure.1 failure.2)
  | .ok execution =>
    match lowerExact : ObjectiveBendPlanAdapter.lower deployment loaded command execution.extraction with
    | none => throw .nativeBinding
    | some native => pure ⟨checked,execution,runExact,native.1,native.2,lowerExact⟩

structure Usage where
  sourceAndForcingTicks : Nat
  outputNodes : Nat
  canonicalOutputBytes : Nat
  allocatedHeap : Nat
  deriving Repr

def usage {deployment : CanonicalCellRegistry.Deployment}
    {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {command : Command} {source : AnnotatedTerm} {limits : Limits} {budget : Budget}
    {capacity : ObjectiveBendDemandCapacity.Profile}
    (prepared : Prepared deployment loaded command source limits budget capacity) : Usage :=
  ⟨budget.ticks-prepared.execution.extraction.result.remaining.ticks,
   budget.nodes-prepared.execution.extraction.result.remaining.nodes,
   budget.bytes-prepared.execution.extraction.result.remaining.bytes,
   prepared.execution.extraction.result.state.heap.size⟩

/-- Complete proposed effects/physical read guards come from the existing
proof-producing native binder. A surface/result cannot substitute their lists. -/
def plan {deployment : CanonicalCellRegistry.Deployment}
    {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {command : Command} {source : AnnotatedTerm} {limits : Limits} {budget : Budget}
    {capacity : ObjectiveBendDemandCapacity.Profile}
    (prepared : Prepared deployment loaded command source limits budget capacity) : BendWorldPlan.Plan :=
  prepared.bound.plan
theorem native_matches {deployment : CanonicalCellRegistry.Deployment}
    {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {command : Command} {source : AnnotatedTerm} {limits : Limits} {budget : Budget}
    {capacity : ObjectiveBendDemandCapacity.Profile}
    (prepared : Prepared deployment loaded command source limits budget capacity) :
    BendWorldPlan.matchesCommand (plan prepared) command = true :=
  prepared.bound.nativeExact

theorem no_returns {deployment : CanonicalCellRegistry.Deployment}
    {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {command : Command} {source : AnnotatedTerm} {limits : Limits} {budget : Budget}
    {capacity : ObjectiveBendDemandCapacity.Profile}
    (prepared : Prepared deployment loaded command source limits budget capacity) :
    (plan prepared).returns = [] := prepared.bound.returnsExact

#assert_axioms native_matches
#assert_axioms no_returns
end Minidregg.Kernel.ObjectiveBendPreparedOutput
