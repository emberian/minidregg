/- Fixed circuit blocks and the universal source runner share this exact Trace.
Source transition count is not the physical cost of an optimized circuit and
may be private. These adapters neither register an evaluator nor price a run. -/
import Compiler.BendLogicSpecialization
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendLogicTrace

open BendLogicCase BendLogicSpecialization
open Minidregg.Theory.BendLiveMachine

set_option autoImplicit false

def sourceCount (input : Bool) : Nat := if input then 2 else 1

theorem source_trace (book : BBook) (plan : Plan) (input : Bool) :
    Trace book (sourceCount input) (inputTerm plan input) (label (plan.output input)) := by
  cases input with
  | false => exact .step (Minidregg.Theory.BendTT.Eval.hit rfl) (.refl _)
  | true =>
      exact .step (Minidregg.Theory.BendTT.Eval.miss rfl (by decide))
        (.step (Minidregg.Theory.BendTT.Eval.hit rfl) (.refl _))

/-- A block's source trace and the universal machine's completion evidence have
exactly the same type. This does not assert executeChecked ran on the block. -/
def execution (book : BBook) (plan : Plan) (input : Bool) :
    Execution book (inputTerm plan input) :=
  .complete (label (plan.output input)) (sourceCount input)
    (source_trace book plan input) .lab

theorem compiled_descriptor_trace_sound {F : Type} [Field F] (book : BBook)
    {nPublic : Nat} {source : BTerm} {plan : Plan} {d : ConstraintDescriptor F}
    (accepted : compile nPublic source plan = some d)
    (input output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 2, wv i.val = assignment input output i)
    (holds : descriptorHolds d wv) :
    Trace book (sourceCount input) (.App .Q1 source (label input)) (label output) := by
  obtain ⟨_, hs, hd⟩ := compile_exact accepted
  rw [hs]
  have correct : output = plan.output input :=
    (descriptor_correct nPublic plan input output).mp ⟨wv, pinned, hd ▸ holds⟩
  rw [correct]
  exact source_trace book plan input

/-- Equal authorized outputs do not make the exact source meter safe to reveal.
This is the paired privacy counterexample; negation would already reveal input. -/
def constantFalse : Plan := ⟨false, false⟩

theorem same_output_different_source_count :
    constantFalse.output false = constantFalse.output true ∧
      sourceCount false ≠ sourceCount true := by decide

theorem constant_false_traces (book : BBook) :
    Trace book 1 (inputTerm constantFalse false) (label false) ∧
      Trace book 2 (inputTerm constantFalse true) (label false) :=
  ⟨source_trace book constantFalse false, source_trace book constantFalse true⟩

#assert_axioms same_output_different_source_count
#assert_axioms constant_false_traces
#assert_axioms source_trace
#assert_axioms execution
#assert_axioms compiled_descriptor_trace_sound

end Minidregg.Compiler.BendLogicTrace
