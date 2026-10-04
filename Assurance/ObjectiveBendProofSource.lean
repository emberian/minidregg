import Theory.ObjectiveBendDemandAdequacy
import Compiler.ObliviousUnrollSemantics
import Theory.AssertAxioms

/- Source receiving for the sole Objective Bend language. A physical circuit
step may be administrative; completed macrosteps are actual lazy stepRaw.
No old CBV evaluator, termination theorem, or source coverage oracle is used.
The concrete ROM/controller owner must instantiate packed-state refinement. -/
namespace Minidregg.Assurance.ObjectiveBendProofSource
open Minidregg.Compiler Minidregg.Theory
open ObjectiveBendOpenRecursion ObjectiveBendDemandMachine ObjectiveBendDemandAdequacy
open ObjectiveBendDemandInvariant
open ObliviousNetwork ObliviousUnroll
set_option autoImplicit false

/-- Zero or one ACTUAL lazy-machine macrosteps per bounded physical tick.
Intermediate allocation/renaming work must preserve the represented state. -/
inductive Macrostep : State → State → Prop where
  | administrative (state : State) : Macrostep state state
  | transition (state : State) : Macrostep state (stepRaw state)

/-- Real raw transition trace; no unrelated Eval proposition is supplied. -/
inductive Trace : Nat → State → State → Prop where
  | refl (state : State) : Trace 0 state state
  | next {ticks : Nat} {state final : State} :
      Trace ticks (stepRaw state) final → Trace (ticks + 1) state final

theorem Trace.raw {ticks : Nat} {state final : State} (trace : Trace ticks state final) :
    rawRun ticks state = final := by
  induction trace with
  | refl => rfl
  | next rest ih => exact ih

/-- Conformance is a concrete relation between the packed implementation and
this lazy machine. It covers accepted physical edges only: capacity/word
refusal is not falsely asserted to be semantic divergence or completion. -/
structure PackedRefinement (network : Network) where
  represents : Array Bool → State → Prop
  acceptedStep : ∀ {input output : Array Bool} {state : State},
    network.evaluate input = some output → output[0]? = some true →
    represents input state → ∃ next, Macrostep state next ∧
      represents (output.extract 1 output.size) next

/-- Arbitrary accepted circuit runs yield actual lazy raw traces with at most
one source-machine step per physical tick, including administrative stutters. -/
theorem accepted_trace {network : Network} (refinement : PackedRefinement network)
    {ticks : Nat} {input output : Array Bool} {state : State}
    (run : AcceptedRun network ticks input output) (initial : refinement.represents input state) :
    ∃ count final, count ≤ ticks ∧ Trace count state final ∧ refinement.represents output final := by
  induction run generalizing state with
  | done input => exact ⟨0,state,Nat.le_refl 0,.refl state,initial⟩
  | step evaluated handled tail ih =>
      obtain ⟨next,edge,represented⟩ := refinement.acceptedStep evaluated handled initial
      obtain ⟨count,final,bound,trace,representedFinal⟩ := ih represented
      cases edge with
      | administrative => exact ⟨count,final,Nat.le_trans bound (Nat.le_succ _),trace,representedFinal⟩
      | transition => exact ⟨count+1,final,Nat.succ_le_succ bound,.next trace,representedFinal⟩

/-- Completed decoded outputs receive independent Objective source meaning.
The final observation law is supplied by the actual packed codec, not by a
proof-carried source/result label. This theorem handles every closed source. -/
theorem completed_observation {network : Network} (refinement : PackedRefinement network)
    {ticks : Nat} {input output : Array Bool} {source : Term} (closed : Scoped 0 source)
    (run : AcceptedRun network ticks input output)
    (initial : refinement.represents input (ObjectiveBendDemandMachine.initial source))
    (observation : Observation)
    (finished : ∀ state, refinement.represents output state →
      state.control = .complete (observationRuntime observation)) :
    Evaluates source (observationTerm observation) := by
  obtain ⟨count,final,_,trace,represented⟩ := accepted_trace refinement run initial
  have completed : (rawRun count (ObjectiveBendDemandMachine.initial source)).control =
      .complete (observationRuntime observation) := by rw [trace.raw]; exact finished final represented
  cases observation with
  | natural number => exact rawRun_natural_sound closed completed
  | boolean value => exact rawRun_boolean_sound closed completed
  | label name => exact rawRun_label_sound closed completed

/-- Higher-order and lazy structured results retain their actual heap meaning.
No eager evaluation of record fields, closure capture erasure, or contextual
identity theorem is substituted for this concrete graph interpretation. -/
theorem completed_value {network : Network} (refinement : PackedRefinement network)
    {ticks : Nat} {input output : Array Bool} {source : Term} (closed : Scoped 0 source)
    (run : AcceptedRun network ticks input output)
    (initial : refinement.represents input (ObjectiveBendDemandMachine.initial source))
    (value : RuntimeValue)
    (finished : ∀ state, refinement.represents output state → state.control = .complete value) :
    ∃ final meaning, refinement.represents output final ∧
      MeaningsScoped final.heap.size meaning ∧ HeapRealizes meaning final.heap ∧
      Evaluates source (valueMeaning meaning value) := by
  obtain ⟨count,final,_,trace,represented⟩ := accepted_trace refinement run initial
  have complete := finished final represented
  have successful : ResultControl (rawRun count (ObjectiveBendDemandMachine.initial source)).control := by
    rw [trace.raw,complete]
    trivial
  have graph := rawRun_graph (graph_initializes closed) successful
  rw [trace.raw] at graph
  obtain ⟨meaning,names,heap,evaluates⟩ := graph_complete_value_sound graph complete
  exact ⟨final,meaning,represented,names,heap,evaluates⟩

#assert_axioms completed_value
#assert_axioms Trace.raw
#assert_axioms accepted_trace
#assert_axioms completed_observation
end Minidregg.Assurance.ObjectiveBendProofSource
